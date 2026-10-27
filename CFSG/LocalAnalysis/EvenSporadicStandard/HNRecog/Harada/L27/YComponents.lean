module

public import CFSG.LocalAnalysis.ComponentClassification.RadicalFreeLayer
public import CFSG.LargeExtraspecial.S12TriG2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.Open CFSG.ComponentClassification

theorem component_center_eq_bot {Y : Type*} [Group Y] [Finite Y]
    (hfree : SolvableRadical.Free Y) {C : Subgroup Y} (hC : IsComponentOf C ⊤) :
    Subgroup.center C = ⊥ :=
  CFSG.ComponentClassification.RadicalFreeLayer.component_center_eq_bot hfree C hC

theorem component_isSimpleGroup {Y : Type*} [Group Y] [Finite Y]
    (hfree : SolvableRadical.Free Y) {C : Subgroup Y} (hC : IsComponentOf C ⊤) :
    IsSimpleGroup C :=
  CFSG.ComponentClassification.RadicalFreeLayer.component_simple hfree C hC

theorem component_equiv_a5 {Y : Type} [Group Y] [Finite Y] (hfree : SolvableRadical.Free Y)
    {C : Subgroup Y} (hC : IsComponentOf C ⊤) (hcard : Nat.card C = 60) :
    Nonempty (C ≃* alternatingGroup (Fin 5)) := by
  haveI : IsSimpleGroup C := component_isSimpleGroup hfree hC
  exact CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcard

theorem component_commute_of_ne {Y : Type*} [Group Y] [Finite Y] {A B : Subgroup Y}
    (hA : IsComponentOf A ⊤) (hB : IsComponentOf B ⊤) (hne : A ≠ B) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  have hle : A ≤ Subgroup.centralizer (B : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne A B hA hB hne)
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm

theorem component_inf_eq_bot {Y : Type*} [Group Y] [Finite Y]
    (hfree : SolvableRadical.Free Y) {A B : Subgroup Y} (hA : IsComponentOf A ⊤)
    (hB : IsComponentOf B ⊤) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have hcenter : (⟨a, ha.1⟩ : A) ∈ Subgroup.center A := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    exact Subtype.ext (component_commute_of_ne hA hB hne x x.2 a ha.2)
  rw [component_center_eq_bot hfree hA, Subgroup.mem_bot] at hcenter
  exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hcenter)

theorem component_inf_sup_eq_bot {Y : Type*} [Group Y] [Finite Y]
    (hfree : SolvableRadical.Free Y) {A B C : Subgroup Y} (hA : IsComponentOf A ⊤)
    (hB : IsComponentOf B ⊤) (hC : IsComponentOf C ⊤) (hAB : A ≠ B) (hAC : A ≠ C) :
    A ⊓ (B ⊔ C) = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have hBc : B ≤ Subgroup.centralizer (A : Set Y) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr (fun x hx =>
      component_commute_of_ne hA hB hAB x hx b hb)
  have hCc : C ≤ Subgroup.centralizer (A : Set Y) := fun c hc =>
    Subgroup.mem_centralizer_iff.mpr (fun x hx =>
      component_commute_of_ne hA hC hAC x hx c hc)
  have hmem : a ∈ Subgroup.centralizer (A : Set Y) := (sup_le hBc hCc) ha.2
  have hcenter : (⟨a, ha.1⟩ : A) ∈ Subgroup.center A := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hmem x x.2)
  rw [component_center_eq_bot hfree hA, Subgroup.mem_bot] at hcenter
  exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hcenter)

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
