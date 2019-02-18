'''
Chabauty - Coleman method for hyperelliptic curves of genus 3, with Jacobian of rank 0.

The main function is Chabauty_Coleman(H, p0, pts).

INPUT:
- H: a hyperelliptic curve of genus 3 whose Jacobian has rank 0, given by an equation
      of the form y^2 = f(x), where f(x)  \in Q[x] is a monic polynomial of degree 7.
- p0: a prime greater than 5.
- pts: a list of known rational points of H.

OUTPUT:
- The first prime p >= p0 such that H has good reduction mod p
- A list of all points in H(Q).
- A list of all Weierstrass points in H(Q_p) \setminus H(Q).
- A list of all points R in H(Q_p) such that [R-infty]\in J(Q_p)_{tors}\setminus J(Q_p)[2], 
  where J is the Jacobian of H.
- A list of all remaining points R in C(Q_p) such that [R-infty] is in the p-adic closure of J(Q) in J(Q_p).
  Note that since H is rank 0 this list should be empty, but it might contain points in H(Q) which
  could not be recognized as rational points with the precision returned by the algorithm.

AUTHORS:
- Maria Ines de Frutos Fernandez and Sachi Hashimoto.
'''

### AUXILIARY FUNCTIONS ###

'''
Finds a prime p >= p0 such that the hyperelliptic 
curve H has good reduction mod p.
'''
def find_good_p(H, p0):
    p_found = False
    p=p0
    while not p_found:
        try:
            Hred = H.change_ring(GF(p))
            p_found = True
        except (ValueError, ZeroDivisionError):
            p = p.next_prime()
    return p

'''
Computes the Coleman integrals \{\int_b^P x^i dx/2y \}_{i=0}^{2g-1}.
'''
def basis_coleman_integrals(H, p, b, P):
    if mod(P[1], p) == 0:
        return H.coleman_integrals_on_basis(H([P[0], -P[1], P[2]]), P)/2
    else:
        return H.coleman_integrals_on_basis(b,P)

'''
Returns local coordinates at the point P.
'''
def local_coordinates_at_P(H, P):
    if P[1] == 0:
        return H.local_coordinates_at_weierstrass(P)
    return H.local_coordinates_at_nonweierstrass(P)

'''
Computes the intersection of all the lists contained in the list L.
'''
def list_intersection(L):
    S = L[0]
    for i in range(1, len(L)):
        S = S.intersection(L[i])
    return list(S)

'''
Returns the common roots of the three power series determined by the
basis of differentials in a residue disk.
'''
def roots_at_disk(H, xt, yt, inf, p, Kp, pows, L, M, N):
    #Check for double roots
    simple_roots = -1
    for i in range(len(pows)):
       if pows[i].truncate(M).discriminant() != 0:
           simple_roots = i
           break
    if simple_roots == -1:
        raise NotImplementedError('All series have double roots')

    Zerosf = gp.polrootspadic(pows[simple_roots].truncate(M), p, N)
    pows.remove(pows[simple_roots])
    int_roots = [x for x in Zerosf if pows[0].truncate()(x) == 0]
    common_roots = [p*x for x in int_roots if pows[1].truncate()(x) == 0]

    if inf:
        common_roots.remove(0)
    
    for r in common_roots:
        if pari(r).valuation(p) > 0:
            P = H.point([xt(Kp(pari(r))), yt(Kp(pari(r)))])
            L.append(P)
            if P[1] != 0:
                L.append(H.point([P[0], -P[1], P[2]]))
    return L

'''
Returns the common roots of the three power series determined by the
basis of differentials in the residue disk of the point at infinity.
'''
def roots_at_infinity_disk(H, xt, yt, g, p, Kp, L, M, N):
    basis_integrals = [(((xt)^i*xt.derivative()/ (2*yt)).integral()).power_series() for i in range(g)]     
    t = basis_integrals[0].parent().gens()[0] 
    
    R2 = Kp[['s']]
    pows = [R2(w(p*t)) for w in basis_integrals]
    
    return roots_at_disk(H, xt, yt, True, p, Kp, pows, L, M, N)

'''
Returns the common roots of the three power series determined by the
basis of differentials in the residue disk of a rational point.
'''
def roots_at_rational_disk(H, xt, yt, g, p, Kp, L, M, N):
    basis_integrals = [((xt)^i*xt.derivative()/ (2*yt)).integral() for i in range(g)]     
    t = basis_integrals[0].parent().gens()[0] 
    
    R2 = Kp[['s']]
    pows = [R2(w(p*t)) for w in basis_integrals]
    
    return roots_at_disk(H, xt, yt, False, p, Kp, pows, L, M, N)

'''
Returns the common roots of the three power series determined by the
basis of differentials in the residue disk of a nonrational point.
'''
def roots_at_nonrational_disk(H, xt, yt, g, p, Kp, const_int, L, M, N):
    basis_integrals = [((xt)^i*xt.derivative()/ (2*yt)).integral() for i in range(g)]     
    t = basis_integrals[0].parent().gens()[0] 
    
    pow_series = [a + b for (a, b) in zip(basis_integrals, const_int)]
   
    pows = [w(p*t) for w in pow_series]
    
    return roots_at_disk(H, xt, yt, False, p, Kp, pows, L, M, N)

'''
Classifies the found points into rational points, 2-torsion,
n-torsion and other points.
'''
def process_points(H, Hpadic, pts):
    rational = []
    two_tors = []
    other_tors = []
    other_pts = []

    b = Hpadic([0,1,0])
    for P in pts:
        try:
            Q = H(P)
            rational.append(Q)
        except (ValueError, TypeError) as e:
            if P[1] == 0:
                two_tors.append(P)
            else:
                C = Hpadic.coleman_integrals_on_basis(b,P)
                if [C[i] for i in range(3)] == [0, 0, 0]:
                    other_tors.append(P)
                else:
                    other_pts.append(P)
    return rational, two_tors, other_pts, other_tors


### MAIN FUNCTION ###
def Chabauty_Coleman(H, p0, pts):
    g = 3
    r = 0

    # Find a prime p >= p0 such that H has good reduction mod p.
    p = find_good_p(H, p0)
    N = 2*p + 4 # p-adic precision
    M = 2*p + 1 # t-adic precision
    
    # Base change H to Q_p and compute the residue points and Weierstrass points
    Kp = Qp(p, N)
    Hpadic = H.change_ring(Kp)
    Hred = H.change_ring(GF(p))
    redpts = Hred.rational_points()
    Weipts = Hpadic.weierstrass_points()
    
    # Fix the point at infinity as the basepoint
    b = H.point([0, 1, 0])
    # Take infinity out of the list of points (It will be added again later)
    pts.remove(b)
    Weipts.remove(Hpadic(b))

    # The list L will contain X(Q_p)_1
    L = [b]
    
    # Point at infinity
    redpts.remove(b.change_ring(GF(p)))
    xt, yt = H.local_coordinates_at_infinity()
    L = roots_at_infinity_disk(Hpadic, xt, yt, g, p, Kp, L, M, N)
    
    # Rational points
    for P in pts:
        try:
            Pred = P.change_ring(GF(p))
            redpts.remove(Pred)
            if Pred[1] != 0:
                redpts.remove(Hred.point([Pred[0], - Pred[1], Pred[2]]))
            elif P == 0:
                Weipts.remove(Hpadic(P))
            xt, yt = local_coordinates_at_P(H, P)
            L = roots_at_rational_disk(Hpadic, xt, yt, g, p, Kp, L, M, N)

        except ValueError as e:
            pass
    pts.insert(0, b)
    
    # Residual points
    indexpts = copy(redpts)
    for P in indexpts:
        try:
            redpts.remove(P)
            lifts = Hpadic.lift_x(int(P[0]), all)
            if len(lifts) > 0:
                for Q in lifts:
                    try:
                        redpts.remove(Q.change_ring(GF(p)))
                    except ValueError:
                        pass
                xt, yt = local_coordinates_at_P(H, lifts[0])
                C = basis_coleman_integrals(Hpadic, p, Hpadic(b), Hpadic(lifts[0]))
                L = roots_at_nonrational_disk(Hpadic, xt, yt, g, p, Kp, [C[i] for i in range(g)],  L, M, N)
            elif len(lifts) == 0 and P[1] == 0:
                i = 0
                Q = Weipts[i]
                while Q.change_ring(GF(p)) != P:
                    i += 1
                    Q = Weipts[i]
                Weipts.remove(Q)
                xt, yt = local_coordinates_at_P(H, Q)
                L = roots_at_nonrational_disk(Hpadic, xt, yt, g, p, Kp, [0 for i in range(g)],  L, M, N)
            else:
                raise ValueError('Error when lifting a residue point')
        except ValueError as e:
            pass

    return p, process_points(H, Hpadic, L)




