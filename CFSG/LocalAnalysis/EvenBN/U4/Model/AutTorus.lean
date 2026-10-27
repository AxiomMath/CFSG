module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Aut

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section MatrixLemmas

omit [Field K] in
theorem det_fin_four_expand {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det = M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
        M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)) -
      M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
        M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)) +
      M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) -
        M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) -
      M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) -
        M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0) + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_one]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc, Fin.succ]
  simp
  ring

theorem miyamotoJ4_unitary_entry {M : Matrix (Fin 4) (Fin 4) K}
    (hM : (M.map h.bar)ᵀ * miyamotoJ4 K * M = miyamotoJ4 K) (i j : Fin 4) :
    h.bar (M 0 i) * M 3 j + h.bar (M 1 i) * M 2 j + h.bar (M 2 i) * M 1 j +
      h.bar (M 3 i) * M 0 j = miyamotoJ4 K i j := by
  rw [← hM]
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.map_apply,
    miyamotoJ4]
  simp
  ring

theorem eq_zero_of_mul_diagonal_eq {M : Matrix (Fin 4) (Fin 4) K} {v : Fin 4 → K}
    (hM : M * diagonal v = diagonal v * M) {i j : Fin 4} (hij : v i ≠ v j) : M i j = 0 := by
  have e := congrFun (congrFun hM i) j
  rw [mul_diagonal, diagonal_mul] at e
  have : M i j * (v j - v i) = 0 := by linear_combination e
  exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hij))

theorem det_sub_scalar_eq_of_conj {s X Y : GL (Fin 4) K} (e : s * X * s⁻¹ = Y) (c : K) :
    ((X : Matrix (Fin 4) (Fin 4) K) - Matrix.scalar (Fin 4) c).det =
      ((Y : Matrix (Fin 4) (Fin 4) K) - Matrix.scalar (Fin 4) c).det := by
  have hs : (s : Matrix (Fin 4) (Fin 4) K) * ((s⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hY : (Y : Matrix (Fin 4) (Fin 4) K) - Matrix.scalar (Fin 4) c =
      (s : Matrix (Fin 4) (Fin 4) K) * ((X : Matrix (Fin 4) (Fin 4) K) -
        Matrix.scalar (Fin 4) c) * ((s⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [← e, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hs]
  rw [hY, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, det_one, one_mul]

theorem det_diagonal_sub_scalar (v : Fin 4 → K) (c : K) :
    (diagonal v - Matrix.scalar (Fin 4) c).det = (v 0 - c) * (v 1 - c) * (v 2 - c) * (v 3 - c) := by
  rw [Matrix.scalar_apply, diagonal_sub, det_diagonal, Fin.prod_univ_four]

end MatrixLemmas

section Field

include h in
theorem exists_sq_eq (x : K) : ∃ y : K, y ^ 2 = x := by
  have : CharP K 2 := h.charP
  have := h.finite
  obtain ⟨y, hy⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) x
  exact ⟨y, by rw [hy, sq]⟩

theorem eq_of_sq_eq_sq [CharP K 2] {x y : K} (e : x ^ 2 = y ^ 2) : x = y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (x - y) ^ 2 = 0 := by linear_combination e + (y ^ 2 - x * y) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)

include h in
theorem exists_generator_units :
    ∃ a : Kˣ, (∀ x : Kˣ, x ∈ zpowers a) ∧ orderOf a = (2 ^ f) ^ 2 - 1 := by
  have := h.finite
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨a, ha, ?_⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_units, h.card, ← pow_mul, mul_comm]

theorem eq_refl_of_apply_generator {a : Kˣ} (ha : ∀ x : Kˣ, x ∈ zpowers a) {φ : K ≃+* K}
    (hφ : φ a = a) : φ = RingEquiv.refl K := by
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · rw [hx, map_zero]
    rfl
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (ha (Units.mk0 x hx))
    have e : x = ((a ^ k : Kˣ) : K) := by rw [hk, Units.val_mk0]
    rw [e, Units.val_zpow_eq_zpow_val, map_zpow₀, hφ]
    rfl

theorem pow_ne_one_of_lt {G : Type*} [Monoid G] {x : G} {m : ℕ} (hm : 0 < m)
    (hlt : m < orderOf x) : x ^ m ≠ 1 :=
  pow_ne_one_of_lt_orderOf hm.ne' hlt

end Field

section TorusTwo

theorem pow_q_sub_one_eq {a : K} (ha : a ≠ 0) : a ^ (2 ^ f - 1) = h.bar a * a⁻¹ := by
  rw [h.bar_apply, eq_mul_inv_iff_mul_eq₀ ha, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]

theorem coe_miyamotoI2Hom (a : Kˣ) :
    ((miyamotoI2Hom h a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![(a : K) ^ 2, h.bar a * (a : K)⁻¹, h.bar a * (a : K)⁻¹, (h.bar a ^ 2)⁻¹] := by
  rw [← pow_q_sub_one_eq h a.ne_zero]
  simp [miyamotoI2Hom, miyamotoDiag]

theorem miyamotoI2Hom_mem_gramSU (a : Kˣ) : miyamotoI2Hom h a ∈ gramSU h (miyamotoJ4 K) := by
  have ha : (a : K) ≠ 0 := a.ne_zero
  have hb : h.bar (a : K) ≠ 0 := (map_ne_zero _).mpr ha
  have hbb := h.bar_bar (a : K)
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · rw [coe_miyamotoI2Hom]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four, diagonal, map_inv₀, hbb] <;>
      field_simp
  · rw [coe_miyamotoI2Hom, det_diagonal, Fin.prod_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    field_simp

theorem miyamotoI2_le_gramSU : miyamotoI2 h ≤ gramSU h (miyamotoJ4 K) := by
  rintro _ ⟨a, rfl⟩
  exact miyamotoI2Hom_mem_gramSU h a

theorem coe_glAut_miyamotoI2Hom (φ : K ≃+* K) (a : Kˣ) :
    ((glAut φ (miyamotoI2Hom h a) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![φ a ^ 2, h.bar (φ a) * (φ a)⁻¹, h.bar (φ a) * (φ a)⁻¹, (h.bar (φ a) ^ 2)⁻¹] := by
  rw [coe_glAut, coe_miyamotoI2Hom, diagonal_map (map_zero φ)]
  congr 1
  ext i
  fin_cases i <;> simp [map_bar_comm]

variable {h}

theorem miyamotoI2Hom_eigen_ne (hf : 2 ≤ f) {a : Kˣ} (hao : orderOf a = (2 ^ f) ^ 2 - 1) :
    (a : K) ^ 2 ≠ h.bar a * (a : K)⁻¹ ∧ (a : K) ^ 2 ≠ (h.bar a ^ 2)⁻¹ ∧
      h.bar a * (a : K)⁻¹ ≠ (h.bar a ^ 2)⁻¹ := by
  have hq : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have ha : (a : K) ≠ 0 := a.ne_zero
  have hbar : h.bar (a : K) = (a : K) ^ 2 ^ f := h.bar_apply _
  have hpow : ∀ m : ℕ, 0 < m → m < (2 ^ f) ^ 2 - 1 → (a : K) ^ m ≠ 1 := fun m hm hlt e =>
    pow_ne_one_of_lt hm (hao ▸ hlt) (Units.ext (by rw [Units.val_pow_eq_pow_val, e, Units.val_one]))
  have hQ : 4 * 2 ^ f ≤ (2 ^ f) ^ 2 := by nlinarith
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  ·
    have e1 : (a : K) ^ 3 * (a : K) ^ (2 ^ f - 3) = (a : K) ^ 3 := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega), ← hbar]
      field_simp at e
      linear_combination -e
    exact hpow (2 ^ f - 3) (by omega) (by omega)
      (mul_left_cancel₀ (pow_ne_zero 3 ha) (by rw [e1, mul_one]))
  ·
    have e1 : (a : K) ^ (2 * (2 ^ f + 1)) = 1 := by
      rw [show 2 * (2 ^ f + 1) = 2 * 2 ^ f + 2 by ring, pow_add, pow_mul', ← hbar]
      field_simp at e
      linear_combination e
    exact hpow _ (by omega) (by omega) e1
  ·
    have e1 : (a : K) * (a : K) ^ (3 * 2 ^ f - 1) = (a : K) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega), pow_mul', ← hbar]
      field_simp at e
      linear_combination e
    exact hpow (3 * 2 ^ f - 1) (by omega) (by omega)
      (mul_left_cancel₀ ha (by rw [e1, mul_one]))

theorem eq_refl_of_conj_glAut_miyamotoI2Hom (hf : 2 ≤ f) {a : Kˣ}
    (ha : ∀ x : Kˣ, x ∈ zpowers a) (hao : orderOf a = (2 ^ f) ^ 2 - 1) {s : GL (Fin 4) K}
    {φ : K ≃+* K} (e : s * glAut φ (miyamotoI2Hom h a) * s⁻¹ = miyamotoI2Hom h a) :
    φ = RingEquiv.refl K := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hq : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have hQ : 4 * 2 ^ f ≤ (2 ^ f) ^ 2 := by nlinarith
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have hy0 : h.bar (a : K) ≠ 0 := (map_ne_zero _).mpr ha0
  have hb0 : φ (a : K) ≠ 0 := (map_ne_zero φ).mpr ha0
  have hbb := h.bar_bar
  have hdet := det_sub_scalar_eq_of_conj e (φ (a : K) ^ 2)
  rw [coe_glAut_miyamotoI2Hom, coe_miyamotoI2Hom, det_diagonal_sub_scalar,
    det_diagonal_sub_scalar] at hdet
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, sub_self, zero_mul] at hdet
  have hφo : orderOf (Units.map (φ : K →* K) a) = (2 ^ f) ^ 2 - 1 := by
    rw [orderOf_injective (Units.map (φ : K →* K)) (fun x y hxy => Units.ext
      (φ.injective (congrArg Units.val hxy))) a, hao]
  have hB : φ (a : K) ^ 2 = h.bar (a : K) * (a : K)⁻¹ → False := by
    intro e5
    have e7 : h.bar (φ (a : K)) ^ 2 = (a : K) * (h.bar (a : K))⁻¹ := by
      rw [← map_pow, e5, map_mul, map_inv₀, hbb]
    have e6 : (φ (a : K) * h.bar (φ (a : K))) ^ 2 = 1 ^ 2 := by
      rw [mul_pow, e5, e7, one_pow]
      field_simp
    have e8 : φ (a : K) * φ (a : K) ^ 2 ^ f = 1 := by
      rw [← h.bar_apply]
      exact eq_of_sq_eq_sq e6
    have e9 : (Units.map (φ : K →* K) a) ^ (2 ^ f + 1) = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one, pow_succ', ← e8]
      rfl)
    exact pow_ne_one_of_lt (by omega) (by rw [hφo]; omega) e9
  rcases mul_eq_zero.mp hdet.symm with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      ·
        exact eq_refl_of_apply_generator ha (eq_of_sq_eq_sq (sub_eq_zero.mp h5).symm)
      · exact (hB (sub_eq_zero.mp h5).symm).elim
    · exact (hB (sub_eq_zero.mp h4).symm).elim
  ·
    exfalso
    have hb : φ (a : K) = (h.bar (a : K))⁻¹ := by
      refine eq_of_sq_eq_sq ?_
      rw [inv_pow]
      exact (sub_eq_zero.mp h3).symm
    have ha1 : (a : K) + 1 ≠ 0 := by
      intro e1
      have e2 : (a : K) = 1 := by linear_combination e1 - h2
      have : a = 1 := Units.ext e2
      rw [this, orderOf_one] at hao
      omega
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (ha (Units.mk0 _ ha1))
    have hk' : (a : K) ^ k = (a : K) + 1 := by
      rw [← Units.val_zpow_eq_zpow_val, hk, Units.val_mk0]
    have e1 : φ ((a : K) + 1) = (h.bar (a : K) + 1)⁻¹ := by
      rw [← hk', map_zpow₀, hb, _root_.inv_zpow, ← map_zpow₀, hk', map_add, map_one]
    rw [map_add, map_one, hb] at e1
    have hy1 : h.bar (a : K) + 1 ≠ 0 := by
      rw [← map_one h.bar, ← map_add]
      exact (map_ne_zero _).mpr ha1
    have e2 : h.bar (a : K) ^ 2 + h.bar (a : K) + 1 = 0 := by
      field_simp at e1
      linear_combination e1
    have e3 : h.bar ((a : K) ^ 3) = h.bar 1 := by
      rw [map_pow, map_one]
      linear_combination (h.bar (a : K) - 1) * e2
    have e4 : a ^ 3 = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact h.bar.injective e3)
    exact pow_ne_one_of_lt (by norm_num) (by rw [hao]; omega) e4

end TorusTwo

section CentralizerTwo

theorem exists_mem_miyamotoN2 {x y z w : K} (hx : h.bar x = x) (hy : h.bar y = y)
    (hz : h.bar z = z) (hw : h.bar w = w) (hdet : x * w - y * z = 1) :
    ∃ n ∈ miyamotoN2 h, (n : Matrix (Fin 4) (Fin 4) K) =
      !![1, 0, 0, 0; 0, x, y, 0; 0, z, w, 0; 0, 0, 0, 1] := by
  let g : SpecialLinearGroup (Fin 2) h.fixedField :=
    ⟨!![⟨x, hx⟩, ⟨y, hy⟩; ⟨z, hz⟩, ⟨w, hw⟩], by
      rw [Matrix.det_fin_two_of]
      exact Subtype.ext (by simpa using hdet)⟩
  refine ⟨_, ⟨g, rfl⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem exists_miyamotoI2_N2_of_block {s : GL (Fin 4) K} (hs : s ∈ gramSU h (miyamotoJ4 K))
    (h01 : (s : Matrix (Fin 4) (Fin 4) K) 0 1 = 0) (h02 : (s : Matrix (Fin 4) (Fin 4) K) 0 2 = 0)
    (h03 : (s : Matrix (Fin 4) (Fin 4) K) 0 3 = 0) (h10 : (s : Matrix (Fin 4) (Fin 4) K) 1 0 = 0)
    (h13 : (s : Matrix (Fin 4) (Fin 4) K) 1 3 = 0) (h20 : (s : Matrix (Fin 4) (Fin 4) K) 2 0 = 0)
    (h23 : (s : Matrix (Fin 4) (Fin 4) K) 2 3 = 0) (h30 : (s : Matrix (Fin 4) (Fin 4) K) 3 0 = 0)
    (h31 : (s : Matrix (Fin 4) (Fin 4) K) 3 1 = 0) (h32 : (s : Matrix (Fin 4) (Fin 4) K) 3 2 = 0) :
    ∃ i ∈ miyamotoI2 h, ∃ n ∈ miyamotoN2 h, s = i * n := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  obtain ⟨hU, hdet⟩ := mem_gramSU.mp hs
  have E03 := miyamotoJ4_unitary_entry h hU 0 3
  have E11 := miyamotoJ4_unitary_entry h hU 1 1
  have E12 := miyamotoJ4_unitary_entry h hU 1 2
  have E21 := miyamotoJ4_unitary_entry h hU 2 1
  have E22 := miyamotoJ4_unitary_entry h hU 2 2
  simp only [h01, h02, h03, h10, h13, h20, h23, h30, h31, h32, map_zero, mul_zero,
    add_zero, zero_add, miyamotoJ4, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one] at E03 E11 E12 E21 E22
  rw [det_fin_four_expand, h01, h02, h03, h10, h13, h20, h23, h30, h31, h32] at hdet
  set l := (s : Matrix (Fin 4) (Fin 4) K) 0 0 with hl
  set m := (s : Matrix (Fin 4) (Fin 4) K) 3 3 with hm
  set α := (s : Matrix (Fin 4) (Fin 4) K) 1 1 with hα
  set β := (s : Matrix (Fin 4) (Fin 4) K) 1 2 with hβ
  set γ := (s : Matrix (Fin 4) (Fin 4) K) 2 1 with hγ
  set ε := (s : Matrix (Fin 4) (Fin 4) K) 2 2 with hε
  have hl0 : l ≠ 0 := by
    rintro e
    rw [e, map_zero, zero_mul] at E03
    exact zero_ne_one E03
  obtain ⟨a₀, ha₀⟩ := exists_sq_eq h l
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    exact hl0 (by rw [← ha₀]; ring)
  have hb₀0 : h.bar a₀ ≠ 0 := (map_ne_zero _).mpr ha₀0
  set ν := h.bar a₀ * a₀⁻¹ with hν
  have hν0 : ν ≠ 0 := mul_ne_zero hb₀0 (inv_ne_zero ha₀0)
  have hνbar : h.bar ν = ν⁻¹ := by
    rw [hν, map_mul, map_inv₀, hbb, mul_inv, inv_inv, mul_comm]
  have hm' : m = (h.bar a₀ ^ 2)⁻¹ := by
    rw [← map_pow, ha₀]
    exact eq_inv_of_mul_eq_one_right E03
  have hδ : α * ε - β * γ = ν ^ 2 := by
    have e' : (α * ε - β * γ) * (l * m) = 1 := by rw [← hdet]; ring
    rw [eq_inv_of_mul_eq_one_left e', hm', ← ha₀, hν]
    field_simp
  have hxα : h.bar α * ν ^ 2 = α := by
    rw [← hδ]; linear_combination α * E12 - β * E11
  have hxγ : h.bar γ * ν ^ 2 = γ := by
    rw [← hδ]; linear_combination ε * E11 - γ * E12 - γ * h2
  have hxβ : h.bar β * ν ^ 2 = β := by
    rw [← hδ]; linear_combination α * E22 - β * E21 - β * h2
  have hxε : h.bar ε * ν ^ 2 = ε := by
    rw [← hδ]; linear_combination ε * E21 - γ * E22
  have hF : ∀ x : K, h.bar x * ν ^ 2 = x → h.bar (ν⁻¹ * x) = ν⁻¹ * x := by
    intro x hx
    rw [map_mul, map_inv₀, hνbar, inv_inv]
    calc ν * h.bar x = ν⁻¹ * (h.bar x * ν ^ 2) := by field_simp
      _ = ν⁻¹ * x := by rw [hx]
  obtain ⟨n, hn, hnM⟩ := exists_mem_miyamotoN2 h (hF α hxα) (hF β hxβ) (hF γ hxγ) (hF ε hxε)
    (by
      calc ν⁻¹ * α * (ν⁻¹ * ε) - ν⁻¹ * β * (ν⁻¹ * γ) = (ν⁻¹) ^ 2 * (α * ε - β * γ) := by ring
        _ = 1 := by rw [hδ, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hν0)])
  refine ⟨miyamotoI2Hom h (Units.mk0 a₀ ha₀0), ⟨_, rfl⟩, n, hn, Units.ext ?_⟩
  rw [Units.val_mul, coe_miyamotoI2Hom, hnM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, diagonal, h01, h02, h03, h10, h13, h20, h23, h30,
      h31, h32, ← hl, ← hm, ← hα, ← hβ, ← hγ, ← hε, ← ha₀, hm', hν] <;>
    field_simp

variable {h} in
theorem exists_miyamotoI2_N2_of_commute (hf : 2 ≤ f) {a : Kˣ}
    (hao : orderOf a = (2 ^ f) ^ 2 - 1) {s : GL (Fin 4) K} (hs : s ∈ gramSU h (miyamotoJ4 K))
    (hc : s * miyamotoI2Hom h a = miyamotoI2Hom h a * s) :
    ∃ i ∈ miyamotoI2 h, ∃ n ∈ miyamotoN2 h, s = i * n := by
  obtain ⟨e1, e2, e3⟩ := miyamotoI2Hom_eigen_ne (h := h) hf hao
  have hM := congrArg Units.val hc
  rw [Units.val_mul, Units.val_mul, coe_miyamotoI2Hom] at hM
  have z := fun (i j : Fin 4) (hij : ![(a : K) ^ 2, h.bar a * (a : K)⁻¹, h.bar a * (a : K)⁻¹,
    (h.bar a ^ 2)⁻¹] i ≠ ![(a : K) ^ 2, h.bar a * (a : K)⁻¹, h.bar a * (a : K)⁻¹,
    (h.bar a ^ 2)⁻¹] j) => eq_zero_of_mul_diagonal_eq hM hij
  exact exists_miyamotoI2_N2_of_block h hs (z 0 1 e1) (z 0 2 e1) (z 0 3 e2) (z 1 0 e1.symm)
    (z 1 3 e3) (z 2 0 e1.symm) (z 2 3 e3) (z 3 0 e2.symm) (z 3 1 e3.symm) (z 3 2 e3.symm)

theorem miyamotoI2_commute {g g' : GL (Fin 4) K} (hg : g ∈ miyamotoI2 h)
    (hg' : g' ∈ miyamotoI2 h) : g * g' = g' * g := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, rfl⟩ := hg'
  rw [← map_mul, ← map_mul, mul_comm]

theorem miyamotoN2_commute_I2 {n g : GL (Fin 4) K} (hn : n ∈ miyamotoN2 h)
    (hg : g ∈ miyamotoI2 h) : n * g = g * n := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨a, rfl⟩ := hg
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_miyamotoI2Hom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, miyamotoN2Mat, diagonal] <;> ring

theorem commute_miyamotoI2_of_mul {i n g : GL (Fin 4) K} (hi : i ∈ miyamotoI2 h)
    (hn : n ∈ miyamotoN2 h) (hg : g ∈ miyamotoI2 h) : i * n * g = g * (i * n) := by
  rw [mul_assoc, miyamotoN2_commute_I2 h hn hg, ← mul_assoc, miyamotoI2_commute h hi hg,
    mul_assoc]

theorem miyamotoFieldAut_refl : miyamotoFieldAut h (RingEquiv.refl K) = 1 :=
  (miyamotoFieldHom h).map_one

theorem fixes_miyamotoI2_iff (hf : 2 ≤ f) (α : MulAut (gramSU h (miyamotoJ4 K))) :
    (∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoI2 h → α g = g) ↔
      ∃ s : gramSU h (miyamotoJ4 K), (∃ i ∈ miyamotoI2 h, ∃ n ∈ miyamotoN2 h,
        (s : GL (Fin 4) K) = i * n) ∧ α = MulAut.conj s := by
  constructor
  · intro hα
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h α
    set φ := miyamotoFieldFactor h α with hφdef
    obtain ⟨a, ha, hao⟩ := exists_generator_units h
    set d : gramSU h (miyamotoJ4 K) := ⟨miyamotoI2Hom h a, miyamotoI2Hom_mem_gramSU h a⟩
    have hd := hα d ⟨a, rfl⟩
    have hφ : φ = RingEquiv.refl K := by
      refine eq_refl_of_conj_glAut_miyamotoI2Hom (h := h) hf ha hao (s := s) ?_
      have e := congrArg (fun x : gramSU h (miyamotoJ4 K) => (x : GL (Fin 4) K)) hd
      rw [hs] at e
      simpa [MulAut.conj_apply] using e
    rw [hφ, miyamotoFieldAut_refl, mul_one] at hs
    refine ⟨s, ?_, hs⟩
    refine exists_miyamotoI2_N2_of_commute hf hao s.2 ?_
    have e := congrArg (fun x : gramSU h (miyamotoJ4 K) => (x : GL (Fin 4) K)) hd
    rw [hs] at e
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at e
    calc (s : GL (Fin 4) K) * miyamotoI2Hom h a =
        (s * miyamotoI2Hom h a * (s : GL (Fin 4) K)⁻¹) * s := by group
      _ = _ := by rw [e]
  · rintro ⟨s, ⟨i, hi, n, hn, hs⟩, rfl⟩ g hg
    apply Subtype.ext
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hs,
      commute_miyamotoI2_of_mul h hi hn hg]
    group

section Ambient

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem exists_eq_miyamotoI2_N2_mul_of_mem_centralizer (hf : 2 ≤ f)
    (x : normalizer (L : Set G)) (hx : (x : G) ∈ centralizer (miyamotoI2G h L η : Set G)) :
    ∃ s : gramSU h (miyamotoJ4 K), (∃ i ∈ miyamotoI2 h, ∃ n ∈ miyamotoN2 h,
      (s : GL (Fin 4) K) = i * n) ∧
        ∃ c ∈ centralizer (L : Set G), (x : G) = (η.symm s : G) * c := by
  obtain ⟨s, hs, hα⟩ := (fixes_miyamotoI2_iff h hf (miyamotoAct h L η x)).mp
    fun g hg => miyamotoAct_apply_of_mem_centralizer h L η x hx hg
  exact ⟨s, hs, exists_eq_mul_of_miyamotoAct_eq_conj h L η x s hα⟩

end Ambient

end CentralizerTwo

end CFSG.LocalAnalysis.EvenBN.U4
