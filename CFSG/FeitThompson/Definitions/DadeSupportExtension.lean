module

public import CFSG.FeitThompson.Definitions.TotalDadeSupport
public import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.DadeSupportPacketsLocalClasses

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

open Classical in
noncomputable def dadeRep (A : Set G) (H : G → Subgroup G) (x : G) : G :=
  if hx : x ∈ totalDadeSupport A H then (mem_totalDadeSupport_iff.1 hx).choose else 1

variable {A : Set G} {H : G → Subgroup G} {f g : G → ℂ} {x : G}

theorem dadeRep_mem (hx : x ∈ totalDadeSupport A H) : dadeRep A H x ∈ A := by
  classical
  rw [dadeRep, dif_pos hx]
  exact (mem_totalDadeSupport_iff.1 hx).choose_spec.1

theorem mem_dadeSupport_dadeRep (hx : x ∈ totalDadeSupport A H) :
    x ∈ dadeSupport H (dadeRep A H x) := by
  classical
  rw [dadeRep, dif_pos hx]
  exact (mem_totalDadeSupport_iff.1 hx).choose_spec.2

theorem exists_mem_H_conj_eq_of_mem_totalDadeSupport (hx : x ∈ totalDadeSupport A H) :
    ∃ u ∈ H (dadeRep A H x), ∃ c : G, x = c⁻¹ * (u * dadeRep A H x) * c := by
  obtain ⟨y, hy, hc⟩ := mem_dadeSupport_iff.1 (mem_dadeSupport_dadeRep hx)
  obtain ⟨c, hcx⟩ := isConj_iff.1 hc
  refine ⟨y * (dadeRep A H x)⁻¹, mem_dadeCoset_iff.1 hy, c⁻¹, ?_⟩
  rw [← hcx]
  group

theorem dadeRep_eq_one_of_notMem (hx : x ∉ totalDadeSupport A H) : dadeRep A H x = 1 := by
  classical
  rw [dadeRep, dif_neg hx]

noncomputable def dadeSupportExtension (A : Set G) (H : G → Subgroup G) (f : G → ℂ) : G → ℂ :=
  (totalDadeSupport A H).indicator fun x => f (dadeRep A H x)

theorem dadeSupportExtension_apply_of_mem (hx : x ∈ totalDadeSupport A H) (f : G → ℂ) :
    dadeSupportExtension A H f x = f (dadeRep A H x) := Set.indicator_of_mem hx _

theorem dadeSupportExtension_eq_zero_of_notMem (hx : x ∉ totalDadeSupport A H) :
    dadeSupportExtension A H f x = 0 := Set.indicator_of_notMem hx _

theorem support_dadeSupportExtension_subset :
    Function.support (dadeSupportExtension A H f) ⊆ totalDadeSupport A H :=
  Set.support_indicator_subset

theorem dadeSupportExtension_congr (h : Set.EqOn f g A) :
    dadeSupportExtension A H f = dadeSupportExtension A H g := by
  funext x
  by_cases hx : x ∈ totalDadeSupport A H
  · rw [dadeSupportExtension_apply_of_mem hx, dadeSupportExtension_apply_of_mem hx,
      h (dadeRep_mem hx)]
  · rw [dadeSupportExtension_eq_zero_of_notMem hx, dadeSupportExtension_eq_zero_of_notMem hx]

@[simp]
theorem dadeSupportExtension_zero : dadeSupportExtension A H (0 : G → ℂ) = 0 := by
  funext x
  by_cases hx : x ∈ totalDadeSupport A H
  · rw [dadeSupportExtension_apply_of_mem hx]; rfl
  · rw [dadeSupportExtension_eq_zero_of_notMem hx, Pi.zero_apply]

theorem dadeSupportExtension_add (f g : G → ℂ) :
    dadeSupportExtension A H (f + g)
      = dadeSupportExtension A H f + dadeSupportExtension A H g := by
  funext x
  by_cases hx : x ∈ totalDadeSupport A H
  · simp [dadeSupportExtension_apply_of_mem hx]
  · simp [dadeSupportExtension_eq_zero_of_notMem hx]

theorem dadeSupportExtension_smul (c : ℂ) (f : G → ℂ) :
    dadeSupportExtension A H (c • f) = c • dadeSupportExtension A H f := by
  funext x
  by_cases hx : x ∈ totalDadeSupport A H
  · simp [dadeSupportExtension_apply_of_mem hx]
  · simp [dadeSupportExtension_eq_zero_of_notMem hx]

section WellDefined

variable [Finite G] {L : Subgroup G} {a : G}

theorem dadeSupportExtension_apply_of_mem_dadeSupport (hD : IsDadeData L A H)
    (hf : ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L → f (l * b * l⁻¹) = f b)
    (ha : a ∈ A) (hx : x ∈ dadeSupport H a) : dadeSupportExtension A H f x = f a := by
  have hxD : x ∈ totalDadeSupport A H := dadeSupport_subset_totalDadeSupport ha hx
  obtain ⟨l, hl, hlr⟩ := hD.exists_conj_of_dadeSupport_inter_nonempty ha
    (dadeRep_mem hxD) ⟨x, hx, mem_dadeSupport_dadeRep hxD⟩
  rw [dadeSupportExtension_apply_of_mem hxD, ← hlr, hf ha hl]

theorem dadeSupportExtension_apply_mem (hD : IsDadeData L A H)
    (hf : ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L → f (l * b * l⁻¹) = f b) (ha : a ∈ A) :
    dadeSupportExtension A H f a = f a :=
  dadeSupportExtension_apply_of_mem_dadeSupport hD hf ha (self_mem_dadeSupport H a)

theorem dadeSupportExtension_apply_conj_mul (hD : IsDadeData L A H)
    (hf : ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L → f (l * b * l⁻¹) = f b) (ha : a ∈ A)
    {u : G} (hu : u ∈ H a) (c : G) :
    dadeSupportExtension A H f (c⁻¹ * (u * a) * c) = f a :=
  dadeSupportExtension_apply_of_mem_dadeSupport hD hf ha
    (mem_dadeSupport_iff.2 ⟨u * a, mul_mem_dadeCoset hu, isConj_iff.2 ⟨c⁻¹, by group⟩⟩)

theorem dadeSupportExtension_eq_of_forall_rep (hD : IsDadeData L A H)
    (hf : ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L → f (l * b * l⁻¹) = f b) {r : G → G}
    (hr : ∀ y ∈ totalDadeSupport A H, r y ∈ A ∧ y ∈ dadeSupport H (r y)) :
    dadeSupportExtension A H f = (totalDadeSupport A H).indicator fun y => f (r y) := by
  funext y
  by_cases hy : y ∈ totalDadeSupport A H
  · rw [Set.indicator_of_mem hy,
      dadeSupportExtension_apply_of_mem_dadeSupport hD hf (hr y hy).1 (hr y hy).2]
  · rw [dadeSupportExtension_eq_zero_of_notMem hy, Set.indicator_of_notMem hy]

theorem isClassFun_dadeSupportExtension (hD : IsDadeData L A H)
    (hf : ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L → f (l * b * l⁻¹) = f b) :
    IsClassFun (dadeSupportExtension A H f) := by
  refine isClassFun_iff.2 fun c y => ?_
  by_cases hy : y ∈ totalDadeSupport A H
  · have hcy : c * y * c⁻¹ ∈ dadeSupport H (dadeRep A H y) := by
      have := conj_mem_dadeSupport (mem_dadeSupport_dadeRep hy) c⁻¹
      rwa [show c⁻¹⁻¹ * y * c⁻¹ = c * y * c⁻¹ by group] at this
    rw [dadeSupportExtension_apply_of_mem_dadeSupport hD hf (dadeRep_mem hy) hcy,
      dadeSupportExtension_apply_of_mem hy]
  · have hcy : c * y * c⁻¹ ∉ totalDadeSupport A H := by
      intro hc
      have := conj_mem_totalDadeSupport hc c
      rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group] at this
      exact hy this
    rw [dadeSupportExtension_eq_zero_of_notMem hcy, dadeSupportExtension_eq_zero_of_notMem hy]

theorem dadeSupportExtension_mem_classFun (hD : IsDadeData L A H)
    (hf : ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L → f (l * b * l⁻¹) = f b) :
    dadeSupportExtension A H f ∈ classFun G :=
  mem_classFun.2 fun _ _ h => (isClassFun_dadeSupportExtension hD hf).apply_eq h

theorem dadeSupportExtension_one_eq_zero (hD : IsDadeData L A H) :
    dadeSupportExtension A H f 1 = 0 :=
  dadeSupportExtension_eq_zero_of_notMem hD.one_notMem_totalDadeSupport

end WellDefined

end CFSG.FeitThompson
