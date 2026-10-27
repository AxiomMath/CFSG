module

public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem s26_sl2_pow_eq_neg_one [Finite F] (hodd : Odd (Nat.card F)) {A : SL(2, F)} {n : ℕ}
    (h1 : A ^ 2 ^ (n + 1) = 1) (h0 : A ^ 2 ^ n ≠ 1) : A ^ 2 ^ n = -1 := by
  have h2 : orderOf (A ^ 2 ^ n) = 2 := by
    apply orderOf_eq_prime
    · rw [← pow_mul, ← pow_succ]
      exact h1
    · exact h0
  exact (CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hodd _).mp h2

theorem s26_no_root [Finite F] (h2 : (2 : F) ≠ 0) (hq3 : Nat.card F % 4 = 3) {n : ℕ}
    (hn : 1 ≤ n) {A : SL(2, F)} (hneg : ((A ^ 2 ^ n : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1)
    (l : F) :
    l ^ 2 - ((A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1) * l + 1 ≠
      0 := by
  intro hl
  have hdetA : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hdet : ((A : Matrix (Fin 2) (Fin 2) F) - l • (1 : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
    rw [Matrix.det_fin_two]
    simp
    linear_combination hl + hdetA
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hAv : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v = l • v := by
    have h := hv
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h
  have hpow : ∀ k : ℕ, ((A ^ k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = l ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hAv,
        Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have hy := hpow (2 ^ n)
  rw [hneg] at hy
  simp only [neg_mulVec, one_mulVec] at hy
  have hl2 : (l ^ 2 ^ n + 1) • v = 0 := by
    rw [add_smul, one_smul, ← hy]
    simp
  have hl2' : l ^ 2 ^ n = -1 := by
    rcases smul_eq_zero.mp hl2 with h | h
    · linear_combination h
    · exact absurd h hv0
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  have h2' : (1 : F) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  let u : Fˣ := Units.mk0 l hl0
  have hu1 : u ^ 2 ^ n ≠ 1 := by
    intro h
    have h' : l ^ 2 ^ n = 1 := by
      have := congrArg (fun x : Fˣ => (x : F)) h
      simpa [u] using this
    rw [hl2'] at h'
    exact h2' h'.symm
  have hu2 : u ^ 2 ^ (n + 1) = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    show l ^ 2 ^ (n + 1) = 1
    rw [pow_succ, pow_mul, hl2']
    norm_num
  have hord : orderOf u = 2 ^ (n + 1) := orderOf_eq_prime_pow hu1 hu2
  have hcard : Nat.card Fˣ = Nat.card F - 1 := by
    classical
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hdvd : 2 ^ (n + 1) ∣ Nat.card F - 1 := by
    rw [← hcard, ← hord]
    exact orderOf_dvd_natCard u
  have h4 : 4 ∣ 2 ^ (n + 1) := by
    have := pow_dvd_pow 2 (show 2 ≤ n + 1 by omega)
    simpa using this
  have h4' := h4.trans hdvd
  omega

theorem s26_commutant (h2 : (2 : F) ≠ 0) {a b c d e g h k m : F} (hdet : a * d - b * c = 1)
    (hirr : ∀ l : F, l ^ 2 - (a + d) * l + 1 ≠ 0) (hm : m ≠ 0)
    (C1 : b * h = c * g) (C2 : (a - d) * g + b * (k - e) = 0)
    (C3 : c * (e - k) + (d - a) * h = 0)
    (B1 : e ^ 2 + g * h = m ^ 2) (B3 : h * (e + k) = 0) :
    g = 0 ∧ h = 0 ∧ e = k ∧ (e = m ∨ e = -m) := by
  have hsq : ∀ r : F, r ^ 2 ≠ (a - d) ^ 2 + 4 * (b * c) := by
    intro r hr
    have h4 : (4 : F) ≠ 0 := by
      have := mul_ne_zero h2 h2
      norm_num at this
      exact this
    have hnum : r ^ 2 - (a + d) ^ 2 + 4 = 0 := by linear_combination hr - 4 * hdet
    have hl2 : 2 * ((a + d + r) / 2) = a + d + r := by field_simp
    apply hirr ((a + d + r) / 2)
    have h0 : 4 * (((a + d + r) / 2) ^ 2 - (a + d) * ((a + d + r) / 2) + 1) = 0 := by
      linear_combination (2 * ((a + d + r) / 2) + (a + d + r) - 2 * (a + d)) * hl2 + hnum
    exact (mul_eq_zero.mp h0).resolve_left h4
  have hc0 : c ≠ 0 := by
    intro hc
    apply hirr a
    subst hc
    linear_combination (-1 : F) * hdet
  by_cases hek : e + k = 0
  ·
    exfalso
    have hk : k = -e := by linear_combination hek
    subst hk
    have hC2 : (a - d) * g = 2 * b * e := by linear_combination C2
    have hC3 : (a - d) * h = 2 * c * e := by linear_combination -C3
    by_cases he : e = 0
    · subst he
      have hgh : g * h = m ^ 2 := by linear_combination B1
      have hg0 : g ≠ 0 := by
        intro hg
        rw [hg] at hgh
        exact hm (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination -hgh))
      have hs : a - d = 0 := by
        have : (a - d) * g = 0 := by linear_combination hC2
        exact (mul_eq_zero.mp this).resolve_right hg0
      have e1 : (b * h) ^ 2 = b * c * m ^ 2 := by
        linear_combination (b * h) * C1 + b * c * hgh
      apply hsq (2 * b * h / m)
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hm)]
      linear_combination 4 * e1 + (-(a - d) * m ^ 2) * hs
    · have e1 : (a - d) ^ 2 * m ^ 2 = e ^ 2 * ((a - d) ^ 2 + 4 * (b * c)) := by
        have : (a - d) ^ 2 * (e ^ 2 + g * h) = e ^ 2 * ((a - d) ^ 2 + 4 * (b * c)) := by
          linear_combination ((a - d) * h) * hC2 + (2 * b * e) * hC3
        rw [B1] at this
        exact this
      apply hsq ((a - d) * m / e)
      rw [div_pow, div_eq_iff (pow_ne_zero 2 he)]
      linear_combination e1
  · have hh : h = 0 := (mul_eq_zero.mp B3).resolve_right hek
    have hg : g = 0 := by
      have : c * g = 0 := by linear_combination -C1 + b * hh
      exact (mul_eq_zero.mp this).resolve_left hc0
    subst hg
    subst hh
    have hek' : e = k := by
      have : c * (e - k) = 0 := by linear_combination C3
      have := (mul_eq_zero.mp this).resolve_left hc0
      linear_combination this
    refine ⟨rfl, rfl, hek', ?_⟩
    have : e ^ 2 = m ^ 2 := by linear_combination B1
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this

@[expose] def s26xM : Matrix (Fin 3) (Fin 3) F := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

@[expose] def s26R0 (a b c d : F) : Matrix (Fin 3) (Fin 3) F := !![a, b, 0; c, d, 0; 0, 0, 1]

theorem s26_block_diag (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 3) (Fin 3) F}
    (hx : s26xM * M = M * s26xM) :
    M 0 2 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 := by
  have e02 := congrFun (congrFun hx 0) 2
  have e12 := congrFun (congrFun hx 1) 2
  have e20 := congrFun (congrFun hx 2) 0
  have e21 := congrFun (congrFun hx 2) 1
  simp [s26xM, Matrix.mul_apply, Fin.sum_univ_three] at e02 e12 e20 e21
  have two_mul_eq : ∀ x : F, x + x = 0 → x = 0 := fun x hx => by
    have : (2 : F) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left h2
  exact ⟨two_mul_eq _ (by linear_combination -e02), two_mul_eq _ (by linear_combination -e12),
    two_mul_eq _ (by linear_combination e20), two_mul_eq _ (by linear_combination e21)⟩

theorem s26_matrix_main (h2 : (2 : F) ≠ 0) {a b c d : F} (hdet : a * d - b * c = 1)
    (hirr : ∀ l : F, l ^ 2 - (a + d) * l + 1 ≠ 0) {M : Matrix (Fin 3) (Fin 3) F}
    (hx : s26xM * M = M * s26xM) (hr : s26R0 a b c d * M = M * s26R0 a b c d)
    (hm : M 2 2 ≠ 0) (hQ00 : (M * M) 0 0 = (M * M) 2 2) (hQ10 : (M * M) 1 0 = 0) :
    M = M 2 2 • (1 : Matrix (Fin 3) (Fin 3) F) ∨ M = M 2 2 • s26xM := by
  obtain ⟨m02, m12, m20, m21⟩ := s26_block_diag h2 hx
  have r00 := congrFun (congrFun hr 0) 0
  have r01 := congrFun (congrFun hr 0) 1
  have r10 := congrFun (congrFun hr 1) 0
  simp [s26R0, Matrix.mul_apply, Fin.sum_univ_three, m02, m12, m20, m21] at r00 r01 r10
  simp [Matrix.mul_apply, Fin.sum_univ_three, m02, m12, m20, m21] at hQ00 hQ10
  have hres := s26_commutant h2 (a := a) (b := b) (c := c) (d := d) (e := M 0 0) (g := M 0 1)
    (h := M 1 0) (k := M 1 1) (m := M 2 2) hdet hirr hm
    (by linear_combination r00) (by linear_combination r01) (by linear_combination r10)
    (by linear_combination hQ00) (by linear_combination hQ10)
  obtain ⟨hg, hh, hek, hem⟩ := hres
  rcases hem with he | he
  · left
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, m02, m12, m20, m21, hg, hh, ← hek, he]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s26xM, Matrix.smul_apply, m02, m12, m20, m21, hg, hh, ← hek, he]

end CFSG.ClassicalInvolution.Asc77
