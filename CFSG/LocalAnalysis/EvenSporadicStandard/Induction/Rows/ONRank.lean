module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RankFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONKFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.ONSchreier CFSG.Sporadic.ONOddCore

section ON


theorem on_three_le_pRank {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .ONan) :
    3 ≤ CFSG.pRank 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ : Nonempty (Y ≃* Carrier .ONan) := h
  obtain ⟨-, hA, hcard, -⟩ := glq_on_sylow_characteristic_elementary_eight
  set D := Subgroup.closure {x | ∃ t ∈ onT, t ^ 2 = x} with hD
  set A := Subgroup.closure {x | x ∈ D ∧ x ^ 2 = 1} with hAdef
  have hDT : D ≤ onT := by
    rw [hD, Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact pow_mem ht 2
  have hAP : A ≤ Pv := by
    have hAD : A ≤ D := by
      rw [hAdef, Subgroup.closure_le]
      exact fun x hx => hx.1
    exact hAD.trans (hDT.trans onT_le)
  have hA' : CFSG.IsElementaryAbelian 2 (A.subgroupOf Pv) :=
    CFSG.IsElementaryAbelian.subgroupOf hAP
  have hcard' : Nat.card (A.subgroupOf Pv) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hcard]
  let φ : ↥Pv ≃* Y := onEquivPv.symm.trans e.symm
  have hE : CFSG.IsElementaryAbelian 2 ((A.subgroupOf Pv).map φ.toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  exact three_le_pRank_of_eight' hE (by
    rw [Subgroup.card_map_of_injective φ.injective, hcard'])

theorem on_pRank_L (X : Type) [Group X] (hX : IsLS [.ONan] X) : 3 ≤ CFSG.pRank 2 X :=
  three_le_pRank_of_isLS on_pinned.1 (fun Y _ h => by
    have hf : Finite (Carrier .ONan) := on_pinned.1
    have : Finite Y := Finite.of_equiv _ h.some.symm.toEquiv
    exact on_three_le_pRank h) hX

end ON

end CFSG.EvenSporadicStandard.Induction
