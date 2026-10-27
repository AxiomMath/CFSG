module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BLinX

public section

namespace CFSG.OddStandard.SmallF3.FritzII.FzL59BLin

theorem chiQ_mul : ∀ p q : Q, chiQ (p * q) = (chiQ p ^^ chiQ q) := by decide

theorem chiQ_psi_zp : ∀ (b : Bool) (q : Q), chiQ (psiQ q * zp b) = chiQ q := by decide

@[expose] def e1 (n : N) : Bool := xor (chiQ n.1) (chiQ n.2.1)

@[expose] def e2 (n : N) : Bool := chiQ n.2.2

theorem e1_mul (n m : N) : e1 (n * m) = (e1 n ^^ e1 m) := by
  obtain ⟨n0, n1, n2⟩ := n
  obtain ⟨m0, m1, m2⟩ := m
  have h0 := chiQ_mul n0 m0
  have h1 := chiQ_mul n1 m1
  simp only [e1, Prod.mk_mul_mk, h0, h1]
  cases chiQ n0 <;> cases chiQ n1 <;> cases chiQ m0 <;> cases chiQ m1 <;> rfl

theorem e2_mul (n m : N) : e2 (n * m) = (e2 n ^^ e2 m) := by
  obtain ⟨n0, n1, n2⟩ := n
  obtain ⟨m0, m1, m2⟩ := m
  simp only [e2, Prod.mk_mul_mk, chiQ_mul]

theorem e1_xi (n : N) : e1 (xiN n) = e1 n := by
  obtain ⟨n0, n1, n2⟩ := n
  show xor (chiQ n1) (chiQ n0) = xor (chiQ n0) (chiQ n1)
  cases chiQ n0 <;> cases chiQ n1 <;> rfl

theorem e1_psi (ε : Bool) (n : N) : e1 (psiN ε n) = e1 n := by
  obtain ⟨n0, n1, n2⟩ := n
  show xor (chiQ (psiQ n0 * zp (ε && chiQ n1))) (chiQ (psiQ n1 * zp (ε && chiQ n2)))
    = xor (chiQ n0) (chiQ n1)
  rw [chiQ_psi_zp, chiQ_psi_zp]

theorem e2_psi (ε : Bool) (n : N) : e2 (psiN ε n) = e2 n := by
  obtain ⟨n0, n1, n2⟩ := n
  show chiQ (psiQ n2 * zp (ε && chiQ n0)) = chiQ n2
  rw [chiQ_psi_zp]

theorem e1_twE (e : Bool) (n : N) : e1 (twE e n) = e1 n := by
  cases e
  · rfl
  · exact e1_xi n

theorem e2_twE (e : Bool) (n : N) : e2 (twE e n) = e2 n := by
  cases e <;> rfl

theorem e1_twF (ε f : Bool) (n : N) : e1 (twF ε f n) = e1 n := by
  cases f
  · rfl
  · exact e1_psi ε n

theorem e2_twF (ε f : Bool) (n : N) : e2 (twF ε f n) = e2 n := by
  cases f
  · rfl
  · exact e2_psi ε n

theorem e1_cinv (ε : Bool) : e1 (cN ε)⁻¹ = false := by
  cases ε <;> decide

theorem e2_cinv (ε : Bool) : e2 (cN ε)⁻¹ = false := by
  cases ε <;> decide

theorem e1_one : e1 1 = false := rfl

theorem e2_one : e2 1 = false := rfl

theorem star_fst (ε : Bool) (x y : X) :
    (star ε x y).1 = x.1 * twE x.2.1 (twF ε x.2.2 y.1) *
      (if x.2.2 && y.2.1 then twE x.2.1 (cN ε)⁻¹ else 1) := rfl

theorem e1_star (ε : Bool) (x y : X) : e1 (star ε x y).1 = (e1 x.1 ^^ e1 y.1) := by
  rw [star_fst, e1_mul, e1_mul, e1_twE, e1_twF]
  have h : e1 (if x.2.2 && y.2.1 then twE x.2.1 (cN ε)⁻¹ else 1) = false := by
    split_ifs
    · rw [e1_twE, e1_cinv]
    · exact e1_one
  rw [h]
  cases e1 x.1 <;> cases e1 y.1 <;> rfl

theorem e2_star (ε : Bool) (x y : X) : e2 (star ε x y).1 = (e2 x.1 ^^ e2 y.1) := by
  rw [star_fst, e2_mul, e2_mul, e2_twE, e2_twF]
  have h : e2 (if x.2.2 && y.2.1 then twE x.2.1 (cN ε)⁻¹ else 1) = false := by
    split_ifs
    · rw [e2_twE, e2_cinv]
    · exact e2_one
  rw [h]
  cases e2 x.1 <;> cases e2 y.1 <;> rfl

theorem epsv_eq (x : X) : epsv x = (e1 x.1, e2 x.1, x.2.1, x.2.2) := rfl

theorem lin_star (ε : Bool) (f : Fin 4 → Bool) (x y : X) :
    lin f (star ε x y) = (lin f x ^^ lin f y) := by
  have h1 := e1_star ε x y
  have h2 := e2_star ε x y
  have h3 : (star ε x y).2.1 = (x.2.1 ^^ y.2.1) := rfl
  have h4 : (star ε x y).2.2 = (x.2.2 ^^ y.2.2) := rfl
  simp only [lin, epsv_eq, linE, h1, h2, h3, h4]
  generalize f 0 = a0
  generalize f 1 = a1
  generalize f 2 = a2
  generalize f 3 = a3
  generalize e1 x.1 = p1
  generalize e1 y.1 = q1
  generalize e2 x.1 = p2
  generalize e2 y.1 = q2
  generalize x.2.1 = r1
  generalize y.2.1 = s1
  generalize x.2.2 = r2
  generalize y.2.2 = s2
  decide +revert

theorem lin_ktr (f : Fin 4 → Bool) (x : X) : lin f (ktr x) = lin f x := by
  obtain ⟨⟨n0, n1, n2⟩, e, g⟩ := x
  have h0 : ∀ q : Q, chiQ (q * QuaternionGroup.a 2) = chiQ q := by decide
  show linE f (xor (chiQ (n0 * QuaternionGroup.a 2)) (chiQ (n1 * QuaternionGroup.a 2)),
      chiQ (n2 * QuaternionGroup.a 2), e, g) = linE f (xor (chiQ n0) (chiQ n1), chiQ n2, e, g)
  rw [h0, h0, h0]

theorem lin_one (f : Fin 4 → Bool) : lin f oneX = false := by
  simp [lin, linE, epsv, oneX, chiQ]
  decide +revert

theorem ktr_ktr (x : X) : ktr (ktr x) = x := by
  obtain ⟨n, e, g⟩ := x
  have h : zetaN * zetaN = 1 := by decide
  show (n * zetaN * zetaN, e, g) = (n, e, g)
  rw [mul_assoc, h, mul_one]

@[expose] def inHQ (q : Q) : Bool := encQ q == 0 || encQ q == 1 || encQ q == 4 || encQ q == 5

@[expose] def inH (x : X) : Bool := inHQ x.1.2.2

theorem inH_ktr (x : X) : inH (ktr x) = !inH x := by
  obtain ⟨⟨n0, n1, n2⟩, e, g⟩ := x
  have h : ∀ q : Q, inHQ (q * QuaternionGroup.a 2) = !inHQ q := by decide
  exact h n2

end CFSG.OddStandard.SmallF3.FritzII.FzL59BLin
