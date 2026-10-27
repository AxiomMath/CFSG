module

public import CFSG.FeitThompson.Definitions.DadeSupportExtension
public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexConjugate

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G}

theorem star_mem_classFun {X : Type*} [Group X] {f : X → ℂ} (hf : f ∈ classFun X) :
    star f ∈ classFun X :=
  mem_classFun.2 fun x y h => by
    simp only [Pi.star_apply, RCLike.star_def, mem_classFun.1 hf x y h]

def dadeDomain (L : Subgroup G) (A : Set G) : Submodule ℂ (↥L → ℂ) where
  carrier := {f | f ∈ classFun ↥L ∧ ∀ x : ↥L, (x : G) ∉ A → f x = 0}
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, fun x hx => by simp [hf.2 x hx, hg.2 x hx]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c f hf := ⟨Submodule.smul_mem _ c hf.1, fun x hx => by simp [hf.2 x hx]⟩

variable {f : ↥L → ℂ}

@[simp]
theorem mem_dadeDomain :
    f ∈ dadeDomain L A ↔ f ∈ classFun ↥L ∧ ∀ x : ↥L, (x : G) ∉ A → f x = 0 := Iff.rfl

theorem dadeDomain_le_classFun (L : Subgroup G) (A : Set G) :
    dadeDomain L A ≤ classFun ↥L := fun _ hf => hf.1

theorem dadeDomain.apply_eq_of_isConj (hf : f ∈ dadeDomain L A) {x y : ↥L} (h : IsConj x y) :
    f x = f y := _root_.CFSG.FeitThompson.mem_classFun.1 hf.1 x y h

theorem dadeDomain.apply_eq_zero (hf : f ∈ dadeDomain L A) {x : ↥L} (hx : (x : G) ∉ A) :
    f x = 0 := hf.2 x hx

theorem star_mem_dadeDomain (hf : f ∈ dadeDomain L A) : star f ∈ dadeDomain L A :=
  ⟨star_mem_classFun hf.1, fun x hx => by simp [hf.2 x hx]⟩

theorem extendByZero_of_mem (f : ↥L → ℂ) {x : G} (hx : x ∈ L) :
    extendByZero L f x = f ⟨x, hx⟩ := extendByZero_apply_coe L f ⟨x, hx⟩

theorem extendByZero_add (f g : ↥L → ℂ) :
    extendByZero L (f + g) = extendByZero L f + extendByZero L g := by
  funext x
  by_cases hx : x ∈ L
  · simp only [Pi.add_apply, extendByZero_of_mem _ hx]
  · simp only [Pi.add_apply, extendByZero_of_notMem L _ hx, add_zero]

theorem extendByZero_smul (c : ℂ) (f : ↥L → ℂ) :
    extendByZero L (c • f) = c • extendByZero L f := by
  funext x
  by_cases hx : x ∈ L
  · simp only [Pi.smul_apply, extendByZero_of_mem _ hx]
  · simp only [Pi.smul_apply, extendByZero_of_notMem L _ hx, smul_zero]

theorem extendByZero_star (f : ↥L → ℂ) :
    extendByZero L (star f) = star (extendByZero L f) := by
  funext x
  by_cases hx : x ∈ L
  · simp only [Pi.star_apply, extendByZero_of_mem _ hx]
  · simp only [Pi.star_apply, extendByZero_of_notMem L _ hx, star_zero]

section

variable [Finite G]

theorem dadeDomain.extendByZero_conj (hD : IsDadeData L A H) (hf : f ∈ dadeDomain L A) :
    ∀ ⦃b : G⦄, b ∈ A → ∀ ⦃l : G⦄, l ∈ L →
      extendByZero L f (l * b * l⁻¹) = extendByZero L f b := by
  intro b hb l hl
  have hbL : b ∈ L := hD.mem_of_mem hb
  have hcL : l * b * l⁻¹ ∈ L := mul_mem (mul_mem hl hbL) (inv_mem hl)
  rw [extendByZero_of_mem _ hcL, extendByZero_of_mem _ hbL]
  exact dadeDomain.apply_eq_of_isConj hf (isConj_iff.2 ⟨⟨l, hl⟩⁻¹, Subtype.ext (by simp; group)⟩)

noncomputable def dadeMap (hD : IsDadeData L A H) : dadeDomain L A →ₗ[ℂ] classFun G where
  toFun f := ⟨dadeSupportExtension A H (extendByZero L (f : ↥L → ℂ)),
    dadeSupportExtension_mem_classFun hD (dadeDomain.extendByZero_conj hD f.2)⟩
  map_add' f g := by
    refine Subtype.ext ?_
    simp only [Submodule.coe_add, extendByZero_add, dadeSupportExtension_add]
  map_smul' c f := by
    refine Subtype.ext ?_
    simp only [SetLike.val_smul, extendByZero_smul, dadeSupportExtension_smul, RingHom.id_apply]

theorem dadeMap_apply_coe (hD : IsDadeData L A H) (f : dadeDomain L A) :
    ((dadeMap hD f : classFun G) : G → ℂ)
      = dadeSupportExtension A H (extendByZero L (f : ↥L → ℂ)) := (rfl)

theorem dadeMap_apply_of_mem_dadeSupport (hD : IsDadeData L A H) (f : dadeDomain L A)
    {a : G} (ha : a ∈ A) {x : G} (hx : x ∈ dadeSupport H a) :
    ((dadeMap hD f : classFun G) : G → ℂ) x = (f : ↥L → ℂ) ⟨a, hD.mem_of_mem ha⟩ := by
  rw [dadeMap_apply_coe, dadeSupportExtension_apply_of_mem_dadeSupport hD
    (dadeDomain.extendByZero_conj hD f.2) ha hx, extendByZero_of_mem _ (hD.mem_of_mem ha)]

theorem dadeMap_apply_mem (hD : IsDadeData L A H) (f : dadeDomain L A) {a : G} (ha : a ∈ A) :
    ((dadeMap hD f : classFun G) : G → ℂ) a = (f : ↥L → ℂ) ⟨a, hD.mem_of_mem ha⟩ :=
  dadeMap_apply_of_mem_dadeSupport hD f ha (self_mem_dadeSupport H a)

theorem dadeMap_apply_conj_mul (hD : IsDadeData L A H) (f : dadeDomain L A) {a : G} (ha : a ∈ A)
    {u : G} (hu : u ∈ H a) (c : G) :
    ((dadeMap hD f : classFun G) : G → ℂ) (c⁻¹ * (u * a) * c)
      = (f : ↥L → ℂ) ⟨a, hD.mem_of_mem ha⟩ :=
  dadeMap_apply_of_mem_dadeSupport hD f ha
    (mem_dadeSupport_iff.2 ⟨u * a, mul_mem_dadeCoset hu, isConj_iff.2 ⟨c⁻¹, by group⟩⟩)

theorem dadeMap_eq_zero_of_notMem (hD : IsDadeData L A H) (f : dadeDomain L A) {x : G}
    (hx : x ∉ totalDadeSupport A H) : ((dadeMap hD f : classFun G) : G → ℂ) x = 0 := by
  rw [dadeMap_apply_coe, dadeSupportExtension_eq_zero_of_notMem hx]

theorem support_dadeMap_subset (hD : IsDadeData L A H) (f : dadeDomain L A) :
    Function.support ((dadeMap hD f : classFun G) : G → ℂ) ⊆ totalDadeSupport A H := by
  rw [dadeMap_apply_coe]; exact support_dadeSupportExtension_subset

theorem dadeMap_one_eq_zero (hD : IsDadeData L A H) (f : dadeDomain L A) :
    ((dadeMap hD f : classFun G) : G → ℂ) 1 = 0 :=
  dadeMap_eq_zero_of_notMem hD f hD.one_notMem_totalDadeSupport

end

theorem dadeSupportExtension_star (A : Set G) (H : G → Subgroup G) (f : G → ℂ) :
    dadeSupportExtension A H (star f) = star (dadeSupportExtension A H f) := by
  funext x
  by_cases hx : x ∈ totalDadeSupport A H
  · simp only [Pi.star_apply, dadeSupportExtension_apply_of_mem hx]
  · simp only [Pi.star_apply, dadeSupportExtension_eq_zero_of_notMem hx, star_zero]

theorem dadeMap_star [Finite G] (hD : IsDadeData L A H) (hf : f ∈ dadeDomain L A) :
    ((dadeMap hD ⟨star f, star_mem_dadeDomain hf⟩ : classFun G) : G → ℂ)
      = star ((dadeMap hD ⟨f, hf⟩ : classFun G) : G → ℂ) := by
  rw [dadeMap_apply_coe, dadeMap_apply_coe]
  exact (congrArg _ (extendByZero_star f)).trans (dadeSupportExtension_star A H _)

theorem dadeMap_conj_apply [Finite G] (hD : IsDadeData L A H) (hf : f ∈ dadeDomain L A) (x : G) :
    ((dadeMap hD ⟨fun y => conj (f y), star_mem_dadeDomain hf⟩ : classFun G) : G → ℂ) x
      = conj (((dadeMap hD ⟨f, hf⟩ : classFun G) : G → ℂ) x) :=
  congrFun (dadeMap_star hD hf) x

end CFSG.FeitThompson

end
