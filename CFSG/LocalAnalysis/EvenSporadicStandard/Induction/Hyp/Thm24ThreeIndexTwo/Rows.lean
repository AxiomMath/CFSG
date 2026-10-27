module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArms

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

theorem pinnedOrder_eq_sporOrder {s : TauCeti.SporadicName} (hs : s ∈ pinnedNames) :
    pinnedOrder s = sporOrder s := by
  rw [sporOrder_eq_sporOrd]
  simp only [pinnedNames, Sol78Rows, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem not_inner_outer_rows {s s' : TauCeti.SporadicName} (hs' : s' ∈ Sol78Rows)
    (hd : pinnedOrder s' ∣ AGLEmbedding.sporOrd s) :
    ¬ (SporadicInnerRow s (pinnedOrder s') ∧ SporadicOuterRow s (pinnedOrder s')) := by
  simp only [Sol78Rows, List.mem_cons, List.not_mem_nil, or_false] at hs'
  rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hd <;>
    cases s <;>
    simp only [pinnedOrder, AGLEmbedding.sporOrd, SporadicInnerRow, SporadicOuterRow] <;>
    decide

theorem sporadicRep_of_innerFixedComponent (I : ArmInputs) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hin : σ ∈ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) {s : TauCeti.SporadicName}
    (hs : s ∈ pinnedNames) (hc : Nat.card (↥D ⧸ center ↥D) = pinnedOrder s) :
    SporadicRep S := by
  rcases catalog_fixed_component I.gls I.evenInner I.evenOuter hna hcat hσ hD with
    ⟨n, k, -, hk5, -, -, -, ⟨e⟩⟩ | ⟨hodd, -⟩ | ⟨-, hout, -⟩ | hsp
  · have hcard : Nat.card (↥D ⧸ center ↥D) = k.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv]
      rw [CFSG.EvenSporadicStandard.Induction.Balance.card_alternatingGroup_of_five_le
        (F := Fin k) (by rwa [Nat.card_fin]), Nat.card_fin]
    exact ((orderCriterion_of_mem hs).1 k (hcard.symm.trans hc)).elim
  · have hcs : Nat.card (↥D ⧸ center ↥D) = sporOrder s :=
      hc.trans (pinnedOrder_eq_sporOrder hs)
    exact (false_of_oddLie_fixedComponent I.gls I.order hodd hσ hD hcs).elim
  · exact (hout hin).elim
  · exact hsp

end CFSG.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo
