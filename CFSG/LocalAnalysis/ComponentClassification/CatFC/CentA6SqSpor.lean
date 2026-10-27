module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArms

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

theorem a6sq_spor_numeric (s : TauCeti.SporadicName)
    (hrow : SporadicInnerRow s 360 ∨ SporadicOuterRow s 360)
    (hS : s ≠ .M → 129600 ∣ AGLEmbedding.sporOrd s) : False := by
  cases s <;> first
    | exact absurd hrow (by simp only [SporadicInnerRow, SporadicOuterRow]; decide)
    | exact absurd (hS (by decide)) (by simp only [AGLEmbedding.sporOrd]; decide)

theorem a6sq_sporadic_false (I : ArmInputs) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {s : TauCeti.SporadicName} (es : S ≃* Carrier s)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D)
    (hD360 : Nat.card (↥D ⧸ center ↥D) = 360) (hS : 129600 ∣ Nat.card S) : False := by
  obtain ⟨-, hin, hout⟩ := I.table ‹IsSimpleGroup S› hna es hσ hD
  rw [hD360] at hin hout
  have hrow : SporadicInnerRow s 360 ∨ SporadicOuterRow s 360 := by
    by_cases hinn : σ ∈ (MulAut.conj : S →* MulAut S).range
    · exact Or.inl (hin hinn)
    · exact Or.inr (hout hinn)
  refine a6sq_spor_numeric s hrow fun hsM => ?_
  have hc : Nat.card S = sporOrder s := by
    rw [Nat.card_congr es.toEquiv, I.card s hsM]
  rw [hc, sporOrder_eq_sporOrd] at hS
  exact hS

end CFSG.ComponentClassification.CatFC
