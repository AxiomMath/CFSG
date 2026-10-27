module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Generation

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section SL2

variable {k : Type*} [Field k]

@[expose] def diagSL2 (l : kˣ) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![(l : k), 0; 0, (l : k)⁻¹], by simp [Matrix.det_fin_two]⟩

theorem coe_diagSL2 (l : kˣ) :
    ((diagSL2 l : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(l : k), 0; 0, (l : k)⁻¹] :=
  rfl

theorem commutator_diagSL2_upperSL2 (l : kˣ) (s : k) :
    ⁅diagSL2 l, upperSL2 s⁆ = upperSL2 (((l : k) ^ 2 - 1) * s) := by
  have hl : (l : k) ≠ 0 := l.ne_zero
  ext i j
  simp only [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, coe_diagSL2, coe_upperSL2, Matrix.adjugate_fin_two_of]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

theorem commutator_diagSL2_lowerSL2 (l : kˣ) (b : k) :
    ⁅diagSL2 l, lowerSL2 b⁆ = lowerSL2 ((((l : k) ^ 2)⁻¹ - 1) * b) := by
  have hl : (l : k) ≠ 0 := l.ne_zero
  ext i j
  simp only [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, coe_diagSL2, coe_lowerSL2, Matrix.adjugate_fin_two_of]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

theorem mem_commutator_range_of_SL2 {G : Type*} [Group G] (φ : SpecialLinearGroup (Fin 2) k →* G)
    {l : kˣ} (hl : (l : k) ^ 2 ≠ 1) (m : SpecialLinearGroup (Fin 2) k) :
    φ m ∈ ⁅φ.range, φ.range⁆ := by
  have hl0 : (l : k) ≠ 0 := l.ne_zero
  have hl1 : (l : k) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hl
  have hl2 : ((l : k) ^ 2)⁻¹ - 1 ≠ 0 := by
    refine sub_ne_zero.2 fun e => hl ?_
    rw [inv_eq_one.1 e]
  refine mem_of_lowerSL2_upperSL2 φ (fun b => ?_) (fun s => ?_) m
  · have e : lowerSL2 b = ⁅diagSL2 l, lowerSL2 (b / (((l : k) ^ 2)⁻¹ - 1))⁆ := by
      rw [commutator_diagSL2_lowerSL2, mul_div_cancel₀ _ hl2]
    rw [e, map_commutatorElement]
    exact commutator_mem_commutator ⟨_, rfl⟩ ⟨_, rfl⟩
  · have e : upperSL2 s = ⁅diagSL2 l, upperSL2 (s / ((l : k) ^ 2 - 1))⁆ := by
      rw [commutator_diagSL2_upperSL2, mul_div_cancel₀ _ hl1]
    rw [e, map_commutatorElement]
    exact commutator_mem_commutator ⟨_, rfl⟩ ⟨_, rfl⟩

end SL2

theorem conj_mem_commutator_self {G : Type*} [Group G] {H : Subgroup G} {x y : G} (hx : x ∈ H)
    (hy : y ∈ ⁅H, H⁆) : x⁻¹ * y * x ∈ ⁅H, H⁆ := by
  have hyH : y ∈ H := commutator_le_self H hy
  have : x⁻¹ * y * x = y * ⁅y⁻¹, x⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [this]
  exact mul_mem hy (commutator_mem_commutator (inv_mem hyH) (inv_mem hx))

section Perfect

variable [CharP K 2]

omit [CharP K 2] in
theorem miyamotoN2_le_commutator (hf : 2 ≤ f) : miyamotoN2 h ≤ ⁅miyamotoN2 h, miyamotoN2 h⁆ := by
  obtain ⟨t, htF, ht⟩ := exists_fixed_unit_sq_ne_one h hf
  have ht0 : (⟨t, htF⟩ : h.fixedField) ≠ 0 := fun e => t.ne_zero (congrArg Subtype.val e)
  have ht' : ((Units.mk0 _ ht0 : h.fixedFieldˣ) : h.fixedField) ^ 2 ≠ 1 := fun e =>
    ht (by simpa using congrArg Subtype.val e)
  rintro _ ⟨m, rfl⟩
  exact mem_commutator_range_of_SL2 (miyamotoN2Hom h) ht' m

theorem miyamotoZ2_le_commutator {H : Subgroup (GL (Fin 4) K)} (hP : miyamotoP h ≤ H) :
    miyamotoZ2 h ≤ ⁅H, H⁆ := by
  rw [← commutator_miyamotoP h]
  exact commutator_mono hP hP

theorem commutator_miyamotoA2_sup_N2 (hf : 2 ≤ f) :
    ⁅miyamotoA2 h ⊔ miyamotoN2 h, miyamotoA2 h ⊔ miyamotoN2 h⁆ = miyamotoA2 h ⊔ miyamotoN2 h := by
  set H := miyamotoA2 h ⊔ miyamotoN2 h with hH
  refine le_antisymm (commutator_le_self H) (sup_le (fun x hx => ?_)
    ((miyamotoN2_le_commutator h hf).trans (commutator_mono le_sup_right le_sup_right)))
  have hP : miyamotoP h ≤ H := by
    rw [hH, miyamotoA2_sup_N2_eq h]
    exact le_sup_left
  have hZ2 := miyamotoZ2_le_commutator h hP
  rw [← SetLike.mem_coe, ← miyamotoZ2_mul_rootA h] at hx
  obtain ⟨z, hz, a, ⟨a', rfl⟩, rfl⟩ := hx
  refine mul_mem (hZ2 hz) ?_
  rw [← miyamotoR2_conj_rootC h a']
  exact conj_mem_commutator_self (mem_sup_right (miyamotoR2_mem_N2 h))
    (hZ2 (miyamotoRootC_le_Z2 h ⟨a', rfl⟩))

end Perfect

section Pull

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

variable [CharP K 2]

theorem commutator_miyamotoA2G_sup_N2G (hf : 2 ≤ f) :
    ⁅miyamotoA2G h L η ⊔ miyamotoN2G h L η, miyamotoA2G h L η ⊔ miyamotoN2G h L η⁆ =
      miyamotoA2G h L η ⊔ miyamotoN2G h L η := by
  have hle := sup_le (miyamotoUnipotent_le_SU h false true) (miyamotoN2_le_gramSU h)
  rw [← miyamotoPull_sup h L η (miyamotoUnipotent_le_SU h false true) (miyamotoN2_le_gramSU h),
    ← miyamotoPull_commutator h L η hle hle, commutator_miyamotoA2_sup_N2 h hf]

end Pull

end CFSG.LocalAnalysis.EvenBN.U4
