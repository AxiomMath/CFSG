module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32CaseA
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32CaseB

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.Asc76 CFSG.ComponentClassification.Asc76X.Hall32
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)

theorem hall32For_of (hgold : GoldschmidtTheoremA) (hcore : Hall32Core) (G : Type) [Group G]
    [Finite G] (IH : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → Hall32For H) :
    Hall32For G := by
  intro S T hS hTS hT4 hTel hwc
  by_cases hsc : ∀ t ∈ T, ∀ g : G, g⁻¹ * t * g ∈ S → g⁻¹ * t * g ∈ T
  · rcases caseA hgold hS hTS hT4 hTel hwc hsc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · push Not at hsc
    exact Or.inr (Or.inr (forall_dihedral_of_core hcore IH hS hTS hT4 hTel hwc hsc))

theorem hallFusionThm32_of (hgold : GoldschmidtTheoremA) (hcore : Hall32Core) :
    HallFusionThm32 := by
  rw [hallFusionThm32_iff]
  suffices h : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → Hall32For G by
    intro G _ _
    exact h _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hG
    exact hall32For_of hgold hcore G fun H _ _ hH => ih (Nat.card H) (hG ▸ hH) H rfl

end CFSG.ComponentClassification.Asc76X
