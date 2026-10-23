"""
Private-key recovery attack on M-CEPKC
======================================

Accompanying code for our cryptanalysis of M-CEPKC, the public-key encryption
scheme of Min et al. (Designs, Codes and Cryptography, 2025).

The script
  1. implements key generation of M-CEPKC, including the generation of the
     initial matrix from the FL-NMLD hyperchaotic map (Min et al.,
     Appendix A.1 and A.2);
  2. implements the private-key recovery attack of the paper (Algorithm 1),
     which uses the repeated roots of the minimal polynomial of the public
     matrix X_init; and
  3. runs the attack on fresh random keys and reports the number of
     successful recoveries and the running time of the attack.

Requirements : SageMath
Usage        : sage key_recovery_attack.sage

A recovered value s' counts as a success if T_{s'}(X_init) = A.
"""

import math
import random
import time


# ============================================================
# M-CEPKC: key generation
# ============================================================
def fl_nmld_generator(x0, x1, alpha, beta, n_iterations):
    """
    Generates a pseudo-random sequence using the FL-NMLD hyperchaotic system.
    """
    seq = []
    xn_minus_1 = x0
    xn = x1
    
    for _ in range(n_iterations):
        # FL-NMLD mathematical expression
        term = xn + beta * math.sin(math.pi * xn_minus_1)
        xn_plus_1 = (alpha * term * (1 - term)) % 1.0
        
        seq.append(xn_plus_1)
        
        xn_minus_1 = xn
        xn = xn_plus_1
        
    return seq

def generate_initial_matrix(p, k):
    """
    Generate the initial matrix X following the initial matrix generation
    procedure in Appendix A.2 (Algorithm 2) of Min et al.
    Fixed parameters (randomly selected):
        alpha = 3.7
        beta  = 0.5
        N0    = 1000
    """
    alpha = 3.7
    beta = 0.5 
    N0 = 1000
    while True:
        x0 = random.uniform(0, 1)                      # random initial value x_0 of the FL-NMLD chaotic system.
        x1 = random.uniform(0, 1)                      # random initial value x_1 of the FL-NMLD chaotic system.
        total_iters = N0 + (k + 2) * k
        raw_seq = fl_nmld_generator(x0, x1, alpha, beta, total_iters)
        seq = raw_seq[N0:]
        
        Q_elements = []
        for i in range(k * k):
            val = round(seq[i] * (10**16)) % p
            Q_elements.append(val)
            
        Q = matrix(F, k, k, Q_elements)
        
        if Q.rank() < k:
            continue
            
        remaining_seq = seq[k*k : k*k + 2*k]
        a_arr = []
        b_arr = []
        for i in range(k):
            a_arr.append(round(remaining_seq[i] * (10**16)))
            b_arr.append(F(round(remaining_seq[i + k] * (10**16))))
            
        for i in range(k):
            a_arr[i] = (a_arr[i] % k) + 1 
            
        num = 0
        jordan_blocks = []
        
        for j in range(k):
            if num == k:
                break
                
            num += a_arr[j]
            if num <= k:
                ord_size = a_arr[j]
            else:
                ord_size = a_arr[j] - (num - k)
                num = k
                
            block = matrix(F, ord_size, ord_size)
            for r in range(ord_size):
                block[r, r] = b_arr[j]
                if r < ord_size - 1:
                    block[r, r + 1] = 1
            jordan_blocks.append(block)
            
        J = block_diagonal_matrix(jordan_blocks)
        
        if J.nrows() < k:
            pad_size = k - J.nrows()
            J = block_diagonal_matrix([J, zero_matrix(F, pad_size, pad_size)])
        
        X = Q.inverse() * J * Q
        
        if X^p == X:
            continue
            
        return X



def MDGCP(X, n, a):
    """
    Computes the Multi-Dimensional General Chebyshev Polynomial T_n(X) 
    using the fast matrix calculation method from Appendix A.1 of Min et al.
    
    Parameters:
    X : Matrix - The k x k matrix over a finite field F_p.
    n : Integer - The degree of the MDGCP.
    a : Integer/Field Element - The parameter 'a' from F_p* (a != 0).
    """
    
    I = identity_matrix(F, k)
    Z = zero_matrix(F, k, k)
    
    T0 = 2 * F(a)^(-1) * I
    T1 = X
    
    # Handle base cases directly for efficiency
    if n == 0:
        return T0
    if n == 1:
        return T1
    
    # Construct the 2k x 2k block matrix D
    # D = [[0, E_k], [-E_k, aX]]
    D = block_matrix(F, [[Z, I], [-I, a * X]])
    
    # Fast matrix exponentiation (Sage uses binary exponentiation automatically)
    Dn = D^n
    
    # Extract submatrices D11 and D12 from Dn
    D11 = Dn[0:k, 0:k]
    D12 = Dn[0:k, k:2*k]
    
    # Compute T_n(X) = D11 * T0 + D12 * T1
    Tn = D11 * T0 + D12 * T1
    
    return Tn


def KeyGen(p, k, a):
    """
    Key generation for M-CEPKC.

    Parameters:
    p : Integer       - prime defining the finite field F_p.
    k : Integer       - matrix dimension (keys are k x k matrices over F_p).
    a : Field element - public MDGCP parameter a in F_p^* (a != 0).

    Returns:
    (pk, sk) where
        pk = (X, a, A) is the public key, and
        sk = s         is the secret key.
    """
    s = ZZ.random_element(1, 4*p)
    # Public initial matrix X, generated via the FL-NMLD procedure (Appendix A.2).
    X = generate_initial_matrix(p, k)
    A = MDGCP(X, s, a)
    pk = (X, a, A)
    sk = s
    return (pk, sk)


# ============================================================
# Private-key recovery attack (Algorithm 1 of the paper)
# ============================================================

def recover_private_key(X_init, a, A, p):
    """
    Private-key recovery when the minimal polynomial mu_init of X_init has a
    repeated root.

    Returns an integer s' with 1 <= s' < 4p and T_{s'}(X_init) = A, or None
    if the attack fails (no repeated root, or case (iii) of Theorem 1 at
    every repeated root).

    Roots of g = gcd(mu_init, mu_init') are computed in F_p. This suffices
    for keys generated as in Min et al., whose eigenvalues lie in F_p.
    """
    F = GF(p)
    R = PolynomialRing(F, 'x')

    # Step 1. Minimal polynomial mu_init and the basis I, X_init, ..., X_init^(d-1).
    mu_init = X_init.minimal_polynomial()
    d = mu_init.degree()
    basis = [X_init^i for i in range(d)]

    # Step 2. Solve A = sum_i h_i X_init^i for the polynomial h of degree < d.
    # Each column of M is the vectorization of one basis matrix.
    M = matrix(F, [b.list() for b in basis]).transpose()
    A_vec = vector(F, A.list())

    try:
        h_vec = M.solve_right(A_vec)
    except ValueError:
        return None    # A is not a polynomial in X_init (cannot happen for valid keys)

    h = R(list(h_vec))
    h_prime = h.derivative()

    # Step 3. The roots of g are exactly the repeated roots of mu_init.
    g = mu_init.gcd(mu_init.derivative())

    if g == 1:
        return None    # no repeated root

    # Step 4. Use each repeated root lambda to obtain s^2 mod p (Theorem 1).
    roots = g.roots(multiplicities=False)

    for lmbda in roots:
        alpha = (F(a) / F(2)) * lmbda
        beta = (F(a) / F(2)) * h(lmbda)
        delta = h_prime(lmbda)

        S=[]
        # Candidate values S for s^2 mod p
        if alpha^2 == F(1):
            S = [delta, -delta]                                     # case (ii)
        elif beta^2 != F(1):
            S = [(alpha^2 - F(1)) * delta^2 / (beta^2 - F(1))]      # case (i)
        else:
            continue                                                # case (iii)

        for w in S:
            if not w.is_square():
                continue

            sigma = Integer(w.sqrt())

            # Candidates s' in {±sigma + j p : 0 <= j <= 4} with 1 <= s' < 4p
            candidates = set()
            for j in range(5):
                val1 = sigma + j * p
                val2 = (-sigma) % p + j * p    # integer representative of -sigma mod p

                if 1 <= val1 < 4 * p:
                    candidates.add(val1)
                if 1 <= val2 < 4 * p:
                    candidates.add(val2)

            # Accept the candidate that reproduces the public key.
            for s_prime in sorted(candidates):
                if MDGCP(X_init, s_prime, a) == A:
                    return s_prime

    return None


# ============================================================
# Experiment
# ============================================================

def run_experiment(p, a, k, instances):
    """
    Run the key-recovery attack on `instances` fresh keys of dimension k and
    print the results. The reported time covers only the attack, not key
    generation.
    """
    total_time = 0
    max_time = 0
    count_fail = 0
    count_exact = 0

    for _ in range(instances):
        # Fresh key pair for this trial; the attack uses only the public key.
        pk, sk = KeyGen(p, k, a)
        X, a_pub, A = pk

        t0 = time.perf_counter()
        s_prime = recover_private_key(X, a_pub, A, p)
        trial_time = time.perf_counter() - t0

        total_time += trial_time
        max_time = max(max_time, trial_time)

        # Success: s' reproduces the public key, so it decrypts every ciphertext.
        if s_prime is None or MDGCP(X, s_prime, a_pub) != A:
            count_fail += 1
        elif s_prime == sk:
            count_exact += 1

    print(f"k = {k}")
    print(f"  Number of instances:     {instances}")
    print(f"  Successful recoveries:   {instances - count_fail}")
    print(f"    of which s' = s:       {count_exact}")
    print(f"  Failures:                {count_fail}")
    print(f"  Average recovery time:   {total_time / instances:.4f} seconds")
    print(f"  Maximum recovery time:   {max_time:.4f} seconds")
    print()


# ============================================================
# Main
# ============================================================

if __name__ == "__main__":
    # Parameters considered by the designers (Min et al., Section 4.2).
    p = 2^1279 - 1          # Mersenne prime
    F = GF(p)
    a = F(2)
    dimensions = [2, 3, 4, 5]
    instances = 100

    for k in dimensions:
        run_experiment(p, a, k, instances)
