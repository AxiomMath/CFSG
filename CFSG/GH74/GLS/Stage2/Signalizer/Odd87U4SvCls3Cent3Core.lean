module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LinearGroups.UnitaryThreeOverNine CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

section Ord

variable {K : Type} [Field K]

theorem unitary_two_pow_eq_one (hK : Nat.card K = 9) (h : UnitaryFieldData 3 1 K) {r n : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) {Q : Matrix (Fin 2) (Fin 2) K}
    (hQ : (Q.map h.bar)ᵀ * Q = 1) (hpow : Q ^ (r ^ n) = 1) : Q = 1 := by
  have hunit : IsUnit Q := IsUnit.of_pow_eq_one hpow (pow_ne_zero n hr.ne_zero)
  let Qu : GL (Fin 2) K := hunit.unit
  have hmem : Matrix.GeneralLinearGroup.toLin Qu ∈
      sesqUnitaryGroup (gramForm h (1 : Matrix (Fin 2) (Fin 2) K)) := by
    rw [mem_sesqUnitaryGroup, Matrix.GeneralLinearGroup.coe_toLin]
    simp only [Matrix.mulVecLin_apply]
    rw [gramForm_isometry_iff, Matrix.mul_one]
    simpa [Qu] using hQ
  let g : ↥(sesqUnitaryGroup (gramForm h (1 : Matrix (Fin 2) (Fin 2) K))) := ⟨_, hmem⟩
  have hcard : Nat.card ↥(sesqUnitaryGroup (gramForm h (1 : Matrix (Fin 2) (Fin 2) K))) = 96 := by
    rw [← card_unitarySet_eq h 2]
    exact card_unitary_two hK
  have hQpow : Qu ^ (r ^ n) = 1 := Units.ext (by simpa [Qu] using hpow)
  have hgpow : g ^ (r ^ n) = 1 := by
    apply Subtype.ext
    change (Matrix.GeneralLinearGroup.toLin Qu) ^ (r ^ n) = 1
    rw [← map_pow, hQpow, map_one]
  have hord1 : orderOf g ∣ r ^ n := orderOf_dvd_of_pow_eq_one hgpow
  have hord2 : orderOf g ∣ 96 := hcard ▸ orderOf_dvd_natCard g
  have hcop : Nat.Coprime (r ^ n) 96 := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hr]
    intro hd
    have h96 : r ∣ 2 ^ 5 * 3 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hr).1 h96 with h1 | h1
    · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h1)
      omega
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
  have h1 : orderOf g = 1 := by
    have := Nat.dvd_gcd hord1 hord2
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.1 this
  have h2 : g = 1 := orderOf_eq_one_iff.1 h1
  have h3 : Matrix.GeneralLinearGroup.toLin Qu = 1 := congrArg Subtype.val h2
  have h4 : Qu = 1 := Matrix.GeneralLinearGroup.toLin.injective (by rw [h3, map_one])
  simpa [Qu] using congrArg Units.val h4

theorem two_by_two_isometry_eq_one (hK : Nat.card K = 9) (h : UnitaryFieldData 3 1 K) {r n : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) {a0 a1 : K} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    {Q : Matrix (Fin 2) (Fin 2) K}
    (hQ : (Q.map h.bar)ᵀ * Matrix.diagonal ![h.norm a0, h.norm a1] * Q =
      Matrix.diagonal ![h.norm a0, h.norm a1])
    (hpow : Q ^ (r ^ n) = 1) : Q = 1 := by
  have hb0 : h.bar a0 ≠ 0 := (map_ne_zero h.bar).2 ha0
  have hb1 : h.bar a1 ≠ 0 := (map_ne_zero h.bar).2 ha1
  set Dm : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![a0, a1] with hDm
  set Di : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![a0⁻¹, a1⁻¹] with hDi
  have hDD : Dm * Di = 1 := by
    rw [hDm, hDi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [ha0, ha1]
  have hDD' : Di * Dm = 1 := by
    rw [hDm, hDi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [ha0, ha1]
  have hN : (Dm.map h.bar)ᵀ * 1 * Dm = Matrix.diagonal ![h.norm a0, h.norm a1] := by
    rw [hDm, diagonal_map (map_zero h.bar), diagonal_transpose, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [UnitaryFieldData.norm, mul_comm]
  have hI : (Di.map h.bar)ᵀ * Matrix.diagonal ![h.norm a0, h.norm a1] * Di = 1 := by
    rw [hDi, diagonal_map (map_zero h.bar), diagonal_transpose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i
    · simp [UnitaryFieldData.norm, map_inv₀]
      field_simp
    · simp [UnitaryFieldData.norm, map_inv₀]
      field_simp
  set Q' : Matrix (Fin 2) (Fin 2) K := Dm * Q * Di with hQ'
  have hQ'u : (Q'.map h.bar)ᵀ * Q' = 1 := by
    have e1 := conjTranspose_mul_mul h (1 : Matrix (Fin 2) (Fin 2) K) (Dm * Q) Di
    have e2 := conjTranspose_mul_mul h (1 : Matrix (Fin 2) (Fin 2) K) Dm Q
    rw [hN, hQ] at e2
    have e3 : (Q'.map h.bar)ᵀ * 1 * Q' = 1 := by rw [hQ', e1, e2, hI]
    simpa using e3
  have hpow' : Q' ^ (r ^ n) = 1 := by
    have : ∀ k : ℕ, Q' ^ k = Dm * Q ^ k * Di := by
      intro k
      induction k with
      | zero => simp [hDD]
      | succ k ih =>
        rw [pow_succ, ih, hQ', pow_succ]
        calc Dm * Q ^ k * Di * (Dm * Q * Di) = Dm * Q ^ k * (Di * Dm) * Q * Di := by
              simp only [Matrix.mul_assoc]
          _ = Dm * (Q ^ k * Q) * Di := by rw [hDD', Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, hpow, Matrix.mul_one, hDD]
  have hQ'1 : Q' = 1 := unitary_two_pow_eq_one hK h hr hr5 hQ'u hpow'
  calc Q = (Di * Dm) * Q * (Di * Dm) := by rw [hDD', Matrix.one_mul, Matrix.mul_one]
    _ = Di * (Dm * Q * Di) * Dm := by simp only [Matrix.mul_assoc]
    _ = Di * 1 * Dm := by rw [← hQ', hQ'1]
    _ = 1 := by rw [Matrix.mul_one, hDD']

end Ord

section Blocks

variable {K : Type} [Field K]

def u4Blk (P Q : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![P 0 0, P 0 1, 0, 0; P 1 0, P 1 1, 0, 0; 0, 0, Q 0 0, Q 0 1; 0, 0, Q 1 0, Q 1 1]

theorem u4Blk_mul (P Q P' Q' : Matrix (Fin 2) (Fin 2) K) :
    u4Blk P Q * u4Blk P' Q' = u4Blk (P * P') (Q * Q') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u4Blk, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem u4Blk_one : u4Blk (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4Blk]

theorem u4Blk_pow (P Q : Matrix (Fin 2) (Fin 2) K) (k : ℕ) :
    (u4Blk P Q) ^ k = u4Blk (P ^ k) (Q ^ k) := by
  induction k with
  | zero => simp [u4Blk_one]
  | succ k ih => rw [pow_succ, ih, u4Blk_mul, ← pow_succ, ← pow_succ]

theorem u4Blk_inj {P Q P' Q' : Matrix (Fin 2) (Fin 2) K} (h : u4Blk P Q = u4Blk P' Q') :
    P = P' ∧ Q = Q' := by
  have e : ∀ i j, u4Blk P Q i j = u4Blk P' Q' i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  have e22 := e 2 2
  have e23 := e 2 3
  have e32 := e 3 2
  have e33 := e 3 3
  simp [u4Blk] at e00 e01 e10 e11 e22 e23 e32 e33
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simpa using ‹_›
  · ext i j
    fin_cases i <;> fin_cases j <;> simpa using ‹_›

theorem u4Blk_map (φ : K →+* K) (P Q : Matrix (Fin 2) (Fin 2) K) :
    (u4Blk P Q).map φ = u4Blk (P.map φ) (Q.map φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4Blk]

theorem u4Blk_transpose (P Q : Matrix (Fin 2) (Fin 2) K) : (u4Blk P Q)ᵀ = u4Blk Pᵀ Qᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4Blk]

theorem diagonal_four (d : Fin 4 → K) :
    Matrix.diagonal d = u4Blk (Matrix.diagonal ![d 0, d 1]) (Matrix.diagonal ![d 2, d 3]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4Blk]

end Blocks


section Core

variable {K : Type} [Field K]

theorem core4 (hK : Nat.card K = 9) (h : UnitaryFieldData 3 1 K) {r n : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (dK : Fin 4 → K) (hd : ∀ i, ∃ a : K, a ≠ 0 ∧ h.norm a = dK i)
    {X : Matrix (Fin 4) (Fin 4) K}
    (hXY : X * Matrix.diagonal ![-1, -1, 1, 1] = Matrix.diagonal ![-1, -1, 1, 1] * X)
    (hXiso : (X.map h.bar)ᵀ * Matrix.diagonal dK * X = Matrix.diagonal dK)
    (hXpow : X ^ (r ^ n) = 1) : X = 1 := by
  have hchar : CharP K 3 := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    have := (CharP.cast_eq_zero_iff K 3 2).1 this
    omega
  have hne : (-1 : K) ≠ 1 := fun h' => h2 (by linear_combination -h')
  have hz : ∀ u v : Fin 4, (![-1, -1, 1, 1] : Fin 4 → K) u ≠ (![-1, -1, 1, 1] : Fin 4 → K) v →
      X u v = 0 := by
    intro u v huv
    have h1 := congrFun (congrFun hXY u) v
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h3 : X u v * ((![-1, -1, 1, 1] : Fin 4 → K) v - (![-1, -1, 1, 1] : Fin 4 → K) u) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · exact absurd (by linear_combination -h4) huv
  have e02 := hz 0 2 (by simpa using hne)
  have e03 := hz 0 3 (by simpa using hne)
  have e12 := hz 1 2 (by simpa using hne)
  have e13 := hz 1 3 (by simpa using hne)
  have e20 := hz 2 0 (by simpa using hne.symm)
  have e21 := hz 2 1 (by simpa using hne.symm)
  have e30 := hz 3 0 (by simpa using hne.symm)
  have e31 := hz 3 1 (by simpa using hne.symm)
  set P : Matrix (Fin 2) (Fin 2) K := !![X 0 0, X 0 1; X 1 0, X 1 1] with hP
  set Q : Matrix (Fin 2) (Fin 2) K := !![X 2 2, X 2 3; X 3 2, X 3 3] with hQ
  have hblk : X = u4Blk P Q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u4Blk, P, Q, e02, e03, e12, e13, e20, e21, e30, e31]
  rw [hblk] at hXiso hXpow
  rw [u4Blk_pow, ← u4Blk_one] at hXpow
  obtain ⟨hP', hQ'⟩ := u4Blk_inj hXpow
  rw [diagonal_four, u4Blk_map, u4Blk_transpose, u4Blk_mul, u4Blk_mul] at hXiso
  obtain ⟨hPi, hQi⟩ := u4Blk_inj hXiso
  obtain ⟨a0, ha0, hn0⟩ := hd 0
  obtain ⟨a1, ha1, hn1⟩ := hd 1
  obtain ⟨a2, ha2, hn2⟩ := hd 2
  obtain ⟨a3, ha3, hn3⟩ := hd 3
  rw [← hn0, ← hn1] at hPi
  rw [← hn2, ← hn3] at hQi
  have hP1 := two_by_two_isometry_eq_one hK h hr hr5 ha0 ha1 hPi hP'
  have hQ1 := two_by_two_isometry_eq_one hK h hr hr5 ha2 ha3 hQi hQ'
  rw [hblk, hP1, hQ1, u4Blk_one]

end Core

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
