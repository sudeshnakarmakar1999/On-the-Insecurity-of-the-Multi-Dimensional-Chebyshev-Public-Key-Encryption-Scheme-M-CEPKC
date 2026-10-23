"""
IND-CPA attack on M-CEPKC
=========================

Accompanying code for our cryptanalysis of M-CEPKC, the public-key encryption
scheme of Min et al. (Designs, Codes and Cryptography, 2025).

The script
  1. implements key generation and encryption of M-CEPKC, including the
     generation of the initial matrix from the FL-NMLD hyperchaotic map
     (Min et al., Appendix A.1 and A.2);
  2. implements the IND-CPA adversary of the paper (Algorithm 2); and
  3. runs the IND-CPA experiment on fresh random keys and reports the number
     of correct guesses and the running time of the adversary.

Requirements : SageMath
Usage        : sage ind_cpa_attack.sage

Inner product convention: for k x k matrices W and Y,
    <W, Y> = sum_{i,j} W[i,j] * Y[i,j] = tr(W^T Y),
which is the dot product of the row-by-row vectorizations of W and Y.
"""

import math
import random
import time


# ============================================================
# M-CEPKC: key generation and encryption
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
    
    # Define identity and zero matrices of size k
    I = identity_matrix(F, k)
    Z = zero_matrix(F, k, k)
    
    # Base cases for MDGCP
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
    p : Integer      - prime defining the finite field F_p.
    k : Integer      - matrix dimension (keys are k x k matrices over F_p).
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


def Enc(pk, M):
    """
    Encryption for M-CEPKC.

    Parameters:
    pk : tuple       - public key (X, a, A).
    M  : Matrix      - plaintext, a k x k matrix over F_p.
    Returns:
    (C1, C2), the ciphertext.
    """
    X, a, A = pk
    r = ZZ.random_element(1, 4*p)
    C1 = MDGCP(X, r, a)
    B = MDGCP(A, r, a)
    C2 = B + M
    return (C1, C2)


# ============================================================
# IND-CPA attack on M-CEPKC (Algorithm 2 of the paper)
# ============================================================

def matrix_inner_product(W, Y):
    """<W, Y> = sum_{i,j} W[i,j] * Y[i,j] = tr(W^T Y)."""
    return (W.transpose() * Y).trace()


def W_init_basis(X):
    """
    Basis of W_init, the orthogonal complement of
    V_init = span{I, X, ..., X^(d_init - 1)} with respect to the matrix
    inner product. Returned as a list of k x k matrices.
    """
    F = X.base_ring()
    k = X.nrows()
    d_init = X.minimal_polynomial().degree()   # d_init = dim V_init

    # Rows of R are the vectorizations of I, X, ..., X^(d_init - 1).
    rows, P = [], identity_matrix(F, k)        # P = X^0
    for _ in range(d_init):
        rows.append(P.list())                  # row-by-row vectorization
        P = P * X
    R = matrix(F, rows)                         # d_init x k^2

    # W_init is the right kernel of R, reshaped back into matrices.
    return [matrix(F, k, k, list(v)) for v in R.right_kernel().basis()]


def find_distinguisher(X):
    """A nonzero W in W_init and an index (i0, j0) with W[i0, j0] != 0."""
    basis = W_init_basis(X)
    assert basis, "W_init is trivial; this cannot happen for k >= 2."
    W = basis[0]                                # any nonzero element works
    for i in range(X.nrows()):
        for j in range(X.ncols()):
            if W[i, j] != 0:
                return W, (i, j)


def attack_choose_messages(X):
    """
    Adversary, phase 1: choose two plaintexts M0, M1 with
    <W, M0> = 0 and <W, M1> = 1.
    """
    F = X.base_ring()
    k = X.nrows()
    W, (i0, j0) = find_distinguisher(X)
    M0 = zero_matrix(F, k, k)                   # <W, M0> = 0
    M1 = zero_matrix(F, k, k)
    M1[i0, j0] = W[i0, j0]^(-1)                 # <W, M1> = 1
    return (M0, M1), W


def attack_guess(W, C2):
    """
    Adversary, phase 2: output b' = <W, C2>.
    Since <W, C2> = <W, M_b> = b, this value is exactly 0 or 1.
    """
    return ZZ(matrix_inner_product(W, C2))


# ============================================================
# IND-CPA experiment
# ============================================================

def run_experiment(p, a, k, instances):
    """
    Run the IND-CPA experiment on `instances` fresh keys of dimension k and
    print the results. The reported time covers only the adversary
    (phases 1 and 2), not key generation or the challenger's encryption.
    """
    total_time = 0
    max_time = 0
    count_fail = 0

    for _ in range(instances):
        # Fresh key pair for this trial; the adversary uses only the public key.
        pk, sk = KeyGen(p, k, a)
        X, _, _ = pk

        # Adversary, phase 1: compute W in W_init and choose M0, M1.
        t0 = time.perf_counter()
        M, W = attack_choose_messages(X)
        t_choose = time.perf_counter() - t0

        # Challenger: sample b uniformly from {0, 1} and encrypt M_b.
        b = ZZ.random_element(0, 2)
        C1, C2 = Enc(pk, M[b])

        # Adversary, phase 2: read the challenge bit off C2.
        t0 = time.perf_counter()
        b_prime = attack_guess(W, C2)
        t_guess = time.perf_counter() - t0

        if b != b_prime:
            count_fail += 1
        trial_time = t_choose + t_guess
        total_time += trial_time
        max_time = max(max_time, trial_time)

    correct = instances - count_fail
    advantage = abs(2 * correct / instances - 1)

    print(f"k = {k}")
    print(f"  Number of instances:  {instances}")
    print(f"  Correct guesses:      {correct}")
    print(f"  Failures:             {count_fail}")
    print(f"  Advantage:            {float(advantage):.4f}")
    print(f"  Average attack time:  {total_time / instances:.4f} seconds")
    print(f"  Maximum attack time:  {max_time:.4f} seconds")
    print()


# ============================================================
# Main
# ============================================================

if __name__ == "__main__":
    # Parameters considered by the designers (Min et al., Section 4.2).
    p = 2^1279 - 1          # Prime
    F = GF(p)
    a = F(2)
    dimensions = [2, 3, 4, 5]
    instances = 100

    for k in dimensions:
        run_experiment(p, a, k, instances)
