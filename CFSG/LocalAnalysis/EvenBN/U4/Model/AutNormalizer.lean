module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutTorusOne

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section NormalizerSU

omit [Field K] in
theorem eq_zero_of_vecMul_two {R : Type*} [Field R] {x y m₀₀ m₀₁ m₁₀ m₁₁ : R}
    (hdet : m₀₀ * m₁₁ - m₀₁ * m₁₀ ≠ 0) (h0 : x * m₀₀ + y * m₁₀ = 0)
    (h1 : x * m₀₁ + y * m₁₁ = 0) : x = 0 ∧ y = 0 := by
  have hx : x * (m₀₀ * m₁₁ - m₀₁ * m₁₀) = 0 := by linear_combination m₁₁ * h0 - m₁₀ * h1
  have hy : y * (m₀₀ * m₁₁ - m₀₁ * m₁₀) = 0 := by linear_combination m₀₀ * h1 - m₀₁ * h0
  exact ⟨(mul_eq_zero.mp hx).resolve_right hdet, (mul_eq_zero.mp hy).resolve_right hdet⟩

theorem miyamotoA1_mul_comm {g g' : GL (Fin 4) K} (hg : g ∈ miyamotoA1 h)
    (hg' : g' ∈ miyamotoA1 h) : g * g' = g' * g := by
  have : CharP K 2 := h.charP
  obtain ⟨b, c, d, hb, -, rfl⟩ := (mem_A1 h).mp hg
  obtain ⟨b', c', d', hb', -, rfl⟩ := (mem_A1 h).mp hg'
  rw [miyamotoXGL_mul_A1 h hb, miyamotoXGL_mul_A1 h hb', add_comm b, add_comm c, add_comm d]

theorem exists_A1_I1_N1_of_conj_mem_A1 {s : GL (Fin 4) K} (hs : s ∈ gramSU h (miyamotoJ4 K))
    (hconj : s⁻¹ * miyamotoXGL h 0 0 1 0 * s ∈ miyamotoA1 h) :
    ∃ a ∈ miyamotoA1 h, ∃ i ∈ miyamotoI1 h, ∃ n ∈ miyamotoN1 h, s = a * (i * n) := by
  obtain ⟨h02, h03, h12, h13⟩ := upper_right_eq_zero_of_conj_mem_A1 h hconj
  obtain ⟨i, hi, n, hn, hD⟩ := exists_miyamotoI1_N1_diag_blocks h hs h02 h03 h12 h13
  refine ⟨s * (i * n)⁻¹, ?_, i, hi, n, hn, by group⟩
  have hin : i * n ∈ gramSU h (miyamotoJ4 K) :=
    mul_mem (miyamotoI1_le_gramSU h hi) (miyamotoN1_le_gramSU_of_det h hn)
  have hS : s * (i * n)⁻¹ ∈ gramSU h (miyamotoJ4 K) := mul_mem hs (inv_mem hin)
  set A := ((s * (i * n)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hA
  have hAD : A * ((i * n : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (s : Matrix (Fin 4) (Fin 4) K) := by
    rw [hA, ← Units.val_mul, inv_mul_cancel_right]
  rw [hD] at hAD
  have E : ∀ k l : Fin 4, _ := fun k l => congrFun (congrFun hAD k) l
  have E00 := E 0 0
  have E01 := E 0 1
  have E10 := E 1 0
  have E11 := E 1 1
  have E02 := E 0 2
  have E03 := E 0 3
  have E12 := E 1 2
  have E13 := E 1 3
  have E22 := E 2 2
  have E23 := E 2 3
  have E32 := E 3 2
  have E33 := E 3 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at E00 E01 E10 E11 E02 E03 E12 E13 E22 E23 E32 E33
  have hdet := (mem_gramSU.mp hs).2
  rw [det_fin_four_expand, h02, h03, h12, h13] at hdet
  have hdet' : ((s : Matrix (Fin 4) (Fin 4) K) 0 0 * (s : Matrix (Fin 4) (Fin 4) K) 1 1 -
      (s : Matrix (Fin 4) (Fin 4) K) 0 1 * (s : Matrix (Fin 4) (Fin 4) K) 1 0) *
      ((s : Matrix (Fin 4) (Fin 4) K) 2 2 * (s : Matrix (Fin 4) (Fin 4) K) 3 3 -
      (s : Matrix (Fin 4) (Fin 4) K) 2 3 * (s : Matrix (Fin 4) (Fin 4) K) 3 2) = 1 := by
    rw [← hdet]; ring
  have hd1 := left_ne_zero_of_mul_eq_one hdet'
  have hd2 := right_ne_zero_of_mul_eq_one hdet'
  obtain ⟨a00, a01⟩ := eq_zero_of_vecMul_two (x := A 0 0 - 1) (y := A 0 1) hd1
    (by linear_combination E00) (by linear_combination E01)
  obtain ⟨a10, a11⟩ := eq_zero_of_vecMul_two (x := A 1 0) (y := A 1 1 - 1) hd1
    (by linear_combination E10) (by linear_combination E11)
  obtain ⟨a02, a03⟩ := eq_zero_of_vecMul_two (x := A 0 2) (y := A 0 3) hd2
    (by linear_combination E02 + h02) (by linear_combination E03 + h03)
  obtain ⟨a12, a13⟩ := eq_zero_of_vecMul_two (x := A 1 2) (y := A 1 3) hd2
    (by linear_combination E12 + h12) (by linear_combination E13 + h13)
  obtain ⟨a22, a23⟩ := eq_zero_of_vecMul_two (x := A 2 2 - 1) (y := A 2 3) hd2
    (by linear_combination E22) (by linear_combination E23)
  obtain ⟨a32, a33⟩ := eq_zero_of_vecMul_two (x := A 3 2) (y := A 3 3 - 1) hd2
    (by linear_combination E32) (by linear_combination E33)
  refine mem_A1_of_block h hS (b := A 2 1) (c := A 2 0) (d := A 3 0) (e := A 3 1) ?_
  rw [← hA]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [sub_eq_zero.mp a00, a01, a10, sub_eq_zero.mp a11, a02, a03, a12, a13,
      sub_eq_zero.mp a22, a23, a32, sub_eq_zero.mp a33]

theorem normalizes_A1_iff {s : GL (Fin 4) K} (hs : s ∈ gramSU h (miyamotoJ4 K)) :
    (∀ g : GL (Fin 4) K, s * g * s⁻¹ ∈ miyamotoA1 h ↔ g ∈ miyamotoA1 h) ↔
      ∃ a ∈ miyamotoA1 h, ∃ i ∈ miyamotoI1 h, ∃ n ∈ miyamotoN1 h, s = a * (i * n) := by
  have : CharP K 2 := h.charP
  constructor
  · intro hN
    refine exists_A1_I1_N1_of_conj_mem_A1 h hs ((hN _).mp ?_)
    rw [show s * (s⁻¹ * miyamotoXGL h 0 0 1 0 * s) * s⁻¹ = miyamotoXGL h 0 0 1 0 by group]
    exact (miyamotoXGL_mem_A1 h).mpr ⟨rfl, map_zero _, map_zero _⟩
  · rintro ⟨a, ha, i, hi, n, hn, rfl⟩ g
    rw [show a * (i * n) * g * (a * (i * n))⁻¹ = a * (i * n * g * (i * n)⁻¹) * a⁻¹ by group]
    constructor
    · intro hg
      have e : i * n * g * (i * n)⁻¹ = a⁻¹ * (a * (i * n * g * (i * n)⁻¹) * a⁻¹) * a := by group
      rw [← conj_mem_A1_iff_of_I1_N1 h hi hn, e]
      exact mul_mem (mul_mem (inv_mem ha) hg) ha
    · intro hg
      exact mul_mem (mul_mem ha ((conj_mem_A1_iff_of_I1_N1 h hi hn).mpr hg)) (inv_mem ha)

end NormalizerSU

section NormalizerAut

theorem stabilizes_A1_iff (α : MulAut (gramSU h (miyamotoJ4 K))) :
    (∀ g : gramSU h (miyamotoJ4 K),
        ((α g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈ miyamotoA1 h ↔
          (g : GL (Fin 4) K) ∈ miyamotoA1 h) ↔
      ∃ s : gramSU h (miyamotoJ4 K), (∃ a ∈ miyamotoA1 h, ∃ i ∈ miyamotoI1 h,
        ∃ n ∈ miyamotoN1 h, (s : GL (Fin 4) K) = a * (i * n)) ∧
          ∃ φ : K ≃+* K, α = MulAut.conj s * miyamotoFieldAut h φ := by
  have : CharP K 2 := h.charP
  constructor
  · intro hA
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h α
    set φ := miyamotoFieldFactor h α with hφdef
    set x₀ : gramSU h (miyamotoJ4 K) := ⟨miyamotoXGL h 0 0 1 0,
      miyamotoUnipotent_le_SU h true false ((miyamotoXGL_mem_A1 h).mpr ⟨rfl, map_zero _,
        map_zero _⟩)⟩ with hx₀
    have hx₀A : (x₀ : GL (Fin 4) K) ∈ miyamotoA1 h :=
      (miyamotoXGL_mem_A1 h).mpr ⟨rfl, map_zero _, map_zero _⟩
    set y := α⁻¹ x₀ with hydef
    have hy : (y : GL (Fin 4) K) ∈ miyamotoA1 h :=
      (hA y).mp (by rw [hydef, MulAut.apply_inv_self]; exact hx₀A)
    have hconj : (s : GL (Fin 4) K)⁻¹ * miyamotoXGL h 0 0 1 0 * s ∈ miyamotoA1 h := by
      have e : ((α y : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) = miyamotoXGL h 0 0 1 0 := by
        rw [hydef, MulAut.apply_inv_self]
      rw [hs] at e
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_miyamotoFieldAut_apply] at e
      have e2 : glAut φ (y : GL (Fin 4) K) =
          (s : GL (Fin 4) K)⁻¹ * miyamotoXGL h 0 0 1 0 * s := by
        rw [← e]
        group
      rw [← e2]
      exact glAut_mem_A1 h φ hy
    exact ⟨s, exists_A1_I1_N1_of_conj_mem_A1 h s.2 hconj, φ, hs⟩
  · rintro ⟨s, hs, φ, rfl⟩ g
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_miyamotoFieldAut_apply, (normalizes_A1_iff h s.2).mpr hs,
      glAut_mem_A1_iff]

end NormalizerAut

section Orders

@[expose] def miyamotoNormA1 : Subgroup (GL (Fin 4) K) :=
  gramSU h (miyamotoJ4 K) ⊓ normalizer (miyamotoA1 h : Set (GL (Fin 4) K))

@[expose] def miyamotoNormA1Param
    (x : miyamotoA1 h × (h.fixedField)ˣ × SpecialLinearGroup (Fin 2) K) : GL (Fin 4) K :=
  (x.1 : GL (Fin 4) K) * (((miyamotoI1Hom (K := K)).comp
    (Units.map h.fixedField.subtype.toMonoidHom)) x.2.1 *
      ((Units.map (miyamotoN1Mat h)).comp SpecialLinearGroup.toGL) x.2.2)

include h in
theorem card_specialLinearGroup_miyamoto :
    Nat.card (SpecialLinearGroup (Fin 2) K) = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) := by
  have := h.finite
  let := Fintype.ofFinite K
  have hK : Fintype.card K = (2 ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h.card, ← pow_mul, mul_comm]
  have hq : 1 < (2 ^ f) ^ 2 := Nat.one_lt_pow (by norm_num)
    (Nat.one_lt_two_pow (by have := h.one_le; omega))
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, hK]
  have e : ((2 ^ f) ^ 2) ^ 2 - (2 ^ f) ^ 2 = (2 ^ f) ^ 2 * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.mul_sub_one, sq ((2 ^ f) ^ 2)]
  rw [e, ← mul_assoc, Nat.mul_div_cancel _ (by omega), mul_comm, ← pow_mul, ← pow_mul,
    ← pow_mul, show f * 2 * 2 = f * 4 by ring]

theorem miyamotoA1_mul_apply {a : GL (Fin 4) K} (ha : a ∈ miyamotoA1 h)
    (X : Matrix (Fin 4) (Fin 4) K) (k l : Fin 4) (hk : k = 0 ∨ k = 1) :
    ((a : Matrix (Fin 4) (Fin 4) K) * X) k l = X k l := by
  have : CharP K 2 := h.charP
  obtain ⟨b, c, d, -, -, rfl⟩ := (mem_A1 h).mp ha
  rcases hk with rfl | rfl <;> simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoX]

theorem miyamotoI1_N1_param_apply (t : (h.fixedField)ˣ) (m : SpecialLinearGroup (Fin 2) K)
    (k l : Fin 2) :
    ((((miyamotoI1Hom (K := K)).comp (Units.map h.fixedField.subtype.toMonoidHom)) t *
      ((Units.map (miyamotoN1Mat h)).comp SpecialLinearGroup.toGL) m : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) (Fin.castLE (by norm_num) k) (Fin.castLE (by norm_num) l) =
      ((t : h.fixedField) : K) * (m : Matrix (Fin 2) (Fin 2) K) k l := by
  rw [Units.val_mul, MonoidHom.comp_apply, coe_miyamotoI1Hom, coe_miyamotoN1_elem]
  fin_cases k <;> fin_cases l <;> simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoN1Mat]

theorem miyamotoNormA1Param_mem
    (x : miyamotoA1 h × (h.fixedField)ˣ × SpecialLinearGroup (Fin 2) K) :
    miyamotoNormA1Param h x ∈ miyamotoNormA1 h := by
  have hi : ((miyamotoI1Hom (K := K)).comp (Units.map h.fixedField.subtype.toMonoidHom)) x.2.1 ∈
      miyamotoI1 h := ⟨x.2.1, rfl⟩
  have hn : ((Units.map (miyamotoN1Mat h)).comp SpecialLinearGroup.toGL) x.2.2 ∈ miyamotoN1 h :=
    ⟨x.2.2, rfl⟩
  have hS : miyamotoNormA1Param h x ∈ gramSU h (miyamotoJ4 K) :=
    mul_mem (miyamotoUnipotent_le_SU h true false x.1.2)
      (mul_mem (miyamotoI1_le_gramSU h hi) (miyamotoN1_le_gramSU_of_det h hn))
  refine ⟨hS, mem_normalizer_iff.mpr fun g => ?_⟩
  exact ((normalizes_A1_iff h hS).mpr ⟨x.1, x.1.2, _, hi, _, hn, rfl⟩ g).symm

theorem miyamotoNormA1Param_injective : Function.Injective (miyamotoNormA1Param h) := by
  have : CharP K 2 := h.charP
  rintro ⟨a, t, m⟩ ⟨a', t', m'⟩ e
  have hM := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) e
  simp only [miyamotoNormA1Param, Units.val_mul] at hM
  have key : ∀ k l : Fin 2, ((t : h.fixedField) : K) * (m : Matrix (Fin 2) (Fin 2) K) k l =
      ((t' : h.fixedField) : K) * (m' : Matrix (Fin 2) (Fin 2) K) k l := by
    intro k l
    have hk : Fin.castLE (by norm_num : 2 ≤ 4) k = 0 ∨ Fin.castLE (by norm_num : 2 ≤ 4) k = 1 := by
      fin_cases k
      exacts [Or.inl rfl, Or.inr rfl]
    have e1 := congrFun (congrFun hM (Fin.castLE (by norm_num) k)) (Fin.castLE (by norm_num) l)
    rw [miyamotoA1_mul_apply h a.2 _ _ _ hk, miyamotoA1_mul_apply h a'.2 _ _ _ hk,
      ← Units.val_mul, ← Units.val_mul, miyamotoI1_N1_param_apply,
      miyamotoI1_N1_param_apply] at e1
    exact e1
  have hdet : ∀ m : SpecialLinearGroup (Fin 2) K, (m : Matrix (Fin 2) (Fin 2) K) 0 0 *
      (m : Matrix (Fin 2) (Fin 2) K) 1 1 - (m : Matrix (Fin 2) (Fin 2) K) 0 1 *
        (m : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := fun m => by
    rw [← Matrix.det_fin_two]; exact m.2
  have ht : ((t : h.fixedField) : K) = ((t' : h.fixedField) : K) := by
    refine eq_of_sq_eq_sq ?_
    calc ((t : h.fixedField) : K) ^ 2 =
        ((t : h.fixedField) : K) * (m : Matrix (Fin 2) (Fin 2) K) 0 0 *
          (((t : h.fixedField) : K) * (m : Matrix (Fin 2) (Fin 2) K) 1 1) -
        ((t : h.fixedField) : K) * (m : Matrix (Fin 2) (Fin 2) K) 0 1 *
          (((t : h.fixedField) : K) * (m : Matrix (Fin 2) (Fin 2) K) 1 0) := by
          linear_combination (-((t : h.fixedField) : K) ^ 2) * hdet m
      _ = _ := by
          rw [key 0 0, key 1 1, key 0 1, key 1 0]
          linear_combination ((t' : h.fixedField) : K) ^ 2 * hdet m'
  have ht0 : ((t : h.fixedField) : K) ≠ 0 := fun e0 => t.ne_zero (Subtype.ext e0)
  have htt : t = t' := Units.ext (Subtype.ext ht)
  have hmm : m = m' := Subtype.ext (Matrix.ext fun k l =>
    mul_left_cancel₀ ht0 (by rw [key k l, ht]))
  subst htt hmm
  have haa : (a : GL (Fin 4) K) = a' := mul_right_cancel e
  rw [Subtype.ext haa]

theorem miyamotoNormA1Param_surjective {s : GL (Fin 4) K} (hs : s ∈ miyamotoNormA1 h) :
    ∃ x, miyamotoNormA1Param h x = s := by
  obtain ⟨a, ha, i, ⟨t, rfl⟩, n, ⟨m, rfl⟩, rfl⟩ :=
    (normalizes_A1_iff h hs.1).mp fun g => (mem_normalizer_iff.mp hs.2 g).symm
  exact ⟨(⟨a, ha⟩, t, m), rfl⟩

theorem card_miyamotoNormA1 : Nat.card (miyamotoNormA1 h) =
    (2 ^ f) ^ 4 * (2 ^ f - 1) * ((2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1)) := by
  have : CharP K 2 := h.charP
  have := h.finite
  have : Finite h.fixedField := Subtype.finite
  let e : miyamotoA1 h × (h.fixedField)ˣ × SpecialLinearGroup (Fin 2) K ≃ miyamotoNormA1 h :=
    Equiv.ofBijective (fun x => ⟨miyamotoNormA1Param h x, miyamotoNormA1Param_mem h x⟩)
      ⟨fun x y hxy => miyamotoNormA1Param_injective h (congrArg Subtype.val hxy),
        fun s => by
          obtain ⟨x, hx⟩ := miyamotoNormA1Param_surjective h s.2
          exact ⟨x, Subtype.ext hx⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_prod, card_miyamotoA1, Nat.card_units,
    h.card_fixedField, card_specialLinearGroup_miyamoto h, mul_assoc]

@[expose] def miyamotoAutStabA1 : Subgroup (MulAut (gramSU h (miyamotoJ4 K))) where
  carrier := {α | ∀ g : gramSU h (miyamotoJ4 K),
    ((α g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈ miyamotoA1 h ↔
      (g : GL (Fin 4) K) ∈ miyamotoA1 h}
  mul_mem' {α β} hα hβ g := by
    rw [MulAut.mul_apply]
    exact (hα (β g)).trans (hβ g)
  one_mem' g := by rw [MulAut.one_apply]
  inv_mem' {α} hα g := by
    have := hα (α⁻¹ g)
    rw [MulAut.apply_inv_self] at this
    exact this.symm

theorem conj_mem_miyamotoAutStabA1_iff (s : gramSU h (miyamotoJ4 K)) :
    MulAut.conj s ∈ miyamotoAutStabA1 h ↔ (s : GL (Fin 4) K) ∈ miyamotoNormA1 h := by
  constructor
  · intro hs
    refine ⟨s.2, mem_normalizer_iff.mpr fun g => ?_⟩
    by_cases hg : g ∈ gramSU h (miyamotoJ4 K)
    · exact ((hs ⟨g, hg⟩).symm.trans (by rfl))
    · have h1 : g ∉ miyamotoA1 h := fun hg' => hg (miyamotoUnipotent_le_SU h true false hg')
      have h2 : (s : GL (Fin 4) K) * g * (s : GL (Fin 4) K)⁻¹ ∉ miyamotoA1 h := fun hg' => hg (by
        have := miyamotoUnipotent_le_SU h true false hg'
        rw [show g = (s : GL (Fin 4) K)⁻¹ * ((s : GL (Fin 4) K) * g * (s : GL (Fin 4) K)⁻¹) *
          (s : GL (Fin 4) K) by group]
        exact mul_mem (mul_mem (inv_mem s.2) this) s.2)
      exact ⟨fun hg' => absurd hg' h1, fun hg' => absurd hg' h2⟩
  · intro hs g
    exact (mem_normalizer_iff.mp hs.2 g).symm

theorem card_miyamotoAutStabA1 :
    Nat.card (miyamotoAutStabA1 h) = Nat.card (miyamotoNormA1 h) * (2 * f) := by
  set σ' := (miyamotoFieldFactor h).comp (miyamotoAutStabA1 h).subtype with hσ'
  have hsurj : Function.Surjective σ' := fun φ => ⟨⟨miyamotoFieldAut h φ, fun g =>
    glAut_mem_A1_iff h φ⟩, miyamotoFieldFactor_fieldAut h φ⟩
  have hker : Nat.card σ'.ker = Nat.card (miyamotoNormA1 h) := by
    refine (Nat.card_congr (Equiv.ofBijective (fun s : miyamotoNormA1 h =>
      (⟨⟨MulAut.conj ⟨s, s.2.1⟩, (conj_mem_miyamotoAutStabA1_iff h ⟨s, s.2.1⟩).mpr s.2⟩,
        miyamotoFieldFactor_conj h _⟩ : σ'.ker)) ⟨fun s t hst => ?_, fun α => ?_⟩)).symm
    · have := congrArg (fun x : σ'.ker => ((x : miyamotoAutStabA1 h) :
        MulAut (gramSU h (miyamotoJ4 K)))) hst
      exact Subtype.ext (congrArg (fun x : gramSU h (miyamotoJ4 K) => (x : GL (Fin 4) K))
        ((conj_inj h).mp this))
    · obtain ⟨⟨α, hα⟩, hαk⟩ := α
      obtain ⟨s, rfl⟩ := (miyamotoFieldFactor_eq_one_iff h α).mp hαk
      exact ⟨⟨s, (conj_mem_miyamotoAutStabA1_iff h s).mp hα⟩, rfl⟩
  rw [← Subgroup.card_mul_index σ'.ker, hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, card_ringAut h]

end Orders

section Ambient

theorem not_sq_dvd_of_dvd_two_mul (hf : 1 ≤ f) {n : ℕ}
    (hn : n ∣ 2 * ((2 ^ f) ^ 4 * (2 ^ f - 1) * ((2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1)) * (2 * f))) :
    ¬(2 ^ f + 1) ^ 2 ∣ n := by
  intro hq
  set q := 2 ^ f with hqdef
  have hq1 : 2 ≤ q := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have hev : Even q := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hodd1 : Odd (q + 1) := hev.add_one
  have hodd2 : Odd (q - 1) := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  have hfac : (q ^ 4 - 1) = (q + 1) * ((q - 1) * (q ^ 2 + 1)) := by
    have h1 : 1 ≤ q := by omega
    have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h4]
    ring
  have hdvd : (q + 1) ^ 2 ∣ (q + 1) * (4 * f * (q ^ 6 * (q - 1) ^ 2 * (q ^ 2 + 1))) := by
    refine hq.trans (hn.trans ?_)
    rw [hfac]
    exact ⟨1, by ring⟩
  rw [sq, mul_dvd_mul_iff_left (by omega)] at hdvd
  have hc1 : Nat.Coprime (q + 1) q := Nat.coprime_self_add_left.mpr (Nat.coprime_one_left q)
  have hc2 : Nat.Coprime (q + 1) (q - 1) := by
    rw [show q + 1 = (q - 1) + 2 by omega]
    exact Nat.coprime_self_add_left.mpr (Nat.coprime_two_left.mpr hodd2)
  have hc3 : Nat.Coprime (q + 1) (q ^ 2 + 1) := by
    rw [show q ^ 2 + 1 = (q - 1) * (q + 1) + 2 by
      have h1 : 1 ≤ q := by omega
      zify [h1]
      ring, Nat.coprime_mul_right_add_right]
    exact Nat.coprime_two_right.mpr hodd1
  have hc4 : Nat.Coprime (q + 1) 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd1)
  have hc : Nat.Coprime (q + 1) (q ^ 6 * (q - 1) ^ 2 * (q ^ 2 + 1)) :=
    ((hc1.pow_right 6).mul_right (hc2.pow_right 2)).mul_right hc3
  have h4f : q + 1 ∣ 4 * f := hc.dvd_of_dvd_mul_right hdvd
  have hff : q + 1 ∣ f := hc4.dvd_of_dvd_mul_left h4f
  have := Nat.le_of_dvd (by omega) hff
  have : f < 2 ^ f := Nat.lt_two_pow_self
  omega

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem card_dvd_of_le_normalizer_A1 {X : Subgroup G} (hXL : X ≤ normalizer (L : Set G))
    (hXA : X ≤ normalizer (miyamotoA1G h L η : Set G)) :
    Nat.card X ∣ Nat.card (X ⊓ centralizer (L : Set G) : Subgroup G) *
      ((2 ^ f) ^ 4 * (2 ^ f - 1) * ((2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1)) * (2 * f)) := by
  set ψ : X →* MulAut (gramSU h (miyamotoJ4 K)) :=
    (miyamotoAct h L η).comp (Subgroup.inclusion hXL) with hψ
  have hker : ψ.ker = (centralizer (L : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact miyamotoAct_eq_one_iff h L η _
  have hkc : Nat.card ψ.ker = Nat.card (X ⊓ centralizer (L : Set G) : Subgroup G) := by
    rw [hker, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : ψ.range ≤ miyamotoAutStabA1 h := by
    rintro _ ⟨x, rfl⟩ g
    exact miyamotoAct_mem_iff_of_mem_normalizer h L η _ (hXA x.2) g
  rw [← Subgroup.card_mul_index ψ.ker, hkc, Subgroup.index_ker]
  refine mul_dvd_mul_left _ ((Subgroup.card_dvd_of_le hrange).trans ?_)
  rw [card_miyamotoAutStabA1, card_miyamotoNormA1]

theorem not_sq_dvd_card_of_le_normalizer_A1 {X : Subgroup G}
    (hXL : X ≤ normalizer (L : Set G)) (hXA : X ≤ normalizer (miyamotoA1G h L η : Set G))
    (hX2 : Nat.card (X ⊓ centralizer (L : Set G) : Subgroup G) ∣ 2) :
    ¬(2 ^ f + 1) ^ 2 ∣ Nat.card X :=
  not_sq_dvd_of_dvd_two_mul h.one_le ((card_dvd_of_le_normalizer_A1 h L η hXL hXA).trans
    (mul_dvd_mul_right hX2 _))

end Ambient

section CentralizerA1

theorem conj_Z2_entries {s : GL (Fin 4) K} {φ : K ≃+* K} {c d : K}
    (e : s * glAut φ (miyamotoXGL h 0 0 c d) = miyamotoXGL h 0 0 c d * s) :
    (s : Matrix (Fin 4) (Fin 4) K) 0 2 * φ c + (s : Matrix (Fin 4) (Fin 4) K) 0 3 * φ d = 0 ∧
    (s : Matrix (Fin 4) (Fin 4) K) 1 2 * φ c + (s : Matrix (Fin 4) (Fin 4) K) 1 3 * φ d = 0 ∧
    (s : Matrix (Fin 4) (Fin 4) K) 2 2 * φ c + (s : Matrix (Fin 4) (Fin 4) K) 2 3 * φ d =
      c * (s : Matrix (Fin 4) (Fin 4) K) 0 0 ∧
    (s : Matrix (Fin 4) (Fin 4) K) 3 2 * φ c + (s : Matrix (Fin 4) (Fin 4) K) 3 3 * φ d =
      d * (s : Matrix (Fin 4) (Fin 4) K) 0 0 + h.bar c * (s : Matrix (Fin 4) (Fin 4) K) 1 0 ∧
    (s : Matrix (Fin 4) (Fin 4) K) 3 3 * h.bar (φ c) =
      d * (s : Matrix (Fin 4) (Fin 4) K) 0 1 + h.bar c * (s : Matrix (Fin 4) (Fin 4) K) 1 1 := by
  rw [glAut_miyamotoXGL, map_zero] at e
  have hM := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) e
  simp only [Units.val_mul, coe_miyamotoXGL] at hM
  have E00 := congrFun (congrFun hM 0) 0
  have E10 := congrFun (congrFun hM 1) 0
  have E20 := congrFun (congrFun hM 2) 0
  have E30 := congrFun (congrFun hM 3) 0
  have E31 := congrFun (congrFun hM 3) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoX] at E00 E10 E20 E30 E31
  refine ⟨by linear_combination E00, by linear_combination E10, by linear_combination E20,
    by linear_combination E30, by linear_combination E31⟩

theorem fixes_miyamotoZ2_iff (α : MulAut (gramSU h (miyamotoJ4 K))) :
    (∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoZ2 h → α g = g) ↔
      ∃ a : gramSU h (miyamotoJ4 K), (a : GL (Fin 4) K) ∈ miyamotoA1 h ∧ α = MulAut.conj a := by
  have : CharP K 2 := h.charP
  have hbb := h.bar_bar
  constructor
  · intro hZ
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h α
    set φ := miyamotoFieldFactor h α with hφdef
    have hc : ∀ c d : K, h.bar d = d → (s : GL (Fin 4) K) * glAut φ (miyamotoXGL h 0 0 c d) =
        miyamotoXGL h 0 0 c d * s := by
      intro c d hd
      have hz : miyamotoXGL h 0 0 c d ∈ miyamotoZ2 h := (miyamotoXGL_mem_Z2 h).mpr ⟨rfl, rfl, hd⟩
      have e := congrArg (fun g : gramSU h (miyamotoJ4 K) => (g : GL (Fin 4) K))
        (hZ ⟨_, miyamotoUnipotent_le_SU h true true hz⟩ hz)
      rw [hs] at e
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_miyamotoFieldAut_apply] at e
      calc (s : GL (Fin 4) K) * glAut φ (miyamotoXGL h 0 0 c d) =
          (s * glAut φ (miyamotoXGL h 0 0 c d) * (s : GL (Fin 4) K)⁻¹) * s := by group
        _ = _ := by rw [e]
    obtain ⟨-, -, A20, A30, A31⟩ := conj_Z2_entries h (hc 0 1 (map_one _))
    obtain ⟨B02, B12, B20, B30, B31⟩ := conj_Z2_entries h (hc 1 0 (map_zero _))
    obtain ⟨C03, C13, -, -, -⟩ := conj_Z2_entries h (hc 0 1 (map_one _))
    simp only [map_zero, map_one, mul_zero, mul_one, zero_mul, one_mul, add_zero,
      zero_add] at A20 A30 A31 B02 B12 B20 B30 B31 C03 C13
    have hdet := (mem_gramSU.mp s.2).2
    rw [det_fin_four_expand, B02, C03, B12, C13, ← A31] at hdet
    have hl0 : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 ≠ 0 := by
      intro e0
      rw [e0] at hdet
      simp at hdet
    have hφc : ∀ c : K, φ c = c := by
      intro c
      obtain ⟨-, -, D20, -, -⟩ := conj_Z2_entries h (hc c 0 (map_zero _))
      simp only [map_zero, mul_zero, add_zero] at D20
      rw [B20] at D20
      exact mul_left_cancel₀ hl0 (D20.trans (mul_comm _ _))
    have hφ : φ = RingEquiv.refl K := RingEquiv.ext hφc
    obtain ⟨ω, hω⟩ := h.exists_bar_ne
    have h10 : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 = 0 := by
      obtain ⟨-, -, -, D30, -⟩ := conj_Z2_entries h (hc ω 0 (map_zero _))
      simp only [mul_zero, add_zero, zero_mul, zero_add, hφc] at D30
      rw [B30] at D30
      have : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 * (ω - h.bar ω) = 0 := by
        linear_combination D30
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hω.symm)
    have hs11 : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1 =
        ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 := B31.symm.trans A30
    have hs32 : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 2 = 0 := B30.trans h10
    have hl4 : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 ^ 4 = 1 := by
      rw [A20, B20, A30, hs11, hs32] at hdet
      linear_combination hdet
    have hl1 : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 = 1 :=
      eq_one_of_pow_four_eq_one hl4
    rw [hφ, miyamotoFieldAut_refl, mul_one] at hs
    refine ⟨s, mem_A1_of_block h s.2
      (b := ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 1)
      (c := ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 0)
      (d := ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 0)
      (e := ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 1) ?_, hs⟩
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [hl1, A31.symm, B02, C03, h10, hs11, B12, C13, B20, A20, hs32, A30]
  · rintro ⟨a, ha, rfl⟩ g hg
    apply Subtype.ext
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      miyamotoA1_mul_comm h ha (miyamotoZ2_le_A1 h hg)]
    group

theorem fixes_miyamotoA1_iff (α : MulAut (gramSU h (miyamotoJ4 K))) :
    (∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoA1 h → α g = g) ↔
      ∃ a : gramSU h (miyamotoJ4 K), (a : GL (Fin 4) K) ∈ miyamotoA1 h ∧ α = MulAut.conj a := by
  have : CharP K 2 := h.charP
  constructor
  · intro hA
    exact (fixes_miyamotoZ2_iff h α).mp fun g hg => hA g (miyamotoZ2_le_A1 h hg)
  · rintro ⟨a, ha, rfl⟩ g hg
    apply Subtype.ext
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      miyamotoA1_mul_comm h ha hg]
    group

end CentralizerA1

end CFSG.LocalAnalysis.EvenBN.U4
