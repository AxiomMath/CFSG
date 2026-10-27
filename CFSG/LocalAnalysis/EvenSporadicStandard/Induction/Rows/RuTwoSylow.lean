module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverE8Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Parts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Assemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOne

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic

theorem ru_pRank_L (X : Type) [Group X] (hX : IsLS [.Ru] X) :
    3 ≤ CFSG.pRank 2 X := by
  obtain ⟨s, hs, -, hodd, ⟨e⟩⟩ := hX
  rcases List.mem_singleton.1 hs with rfl
  have : Finite (Carrier .Ru) := CFSG.Sporadic.finite_carrier_of_ne_M .Ru (by decide)
  have : Finite (center X) := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have : Finite (X ⧸ center X) := Finite.of_equiv _ e.symm.toEquiv
  have : Finite X := Finite.of_subgroup_quotient (center X)
  exact three_le_pRank_ru_cover e

theorem twoSylowStd_ru
    (h25 : Finkelstein77.Asc76Lemma25) : TwoSylowStd [.Ru] :=
  twoSylowStd_of_lemma25 h25 ru_pRank_L fun _ _ h =>
    TwoRu.hypothesisOne_of_isSporadic_ru h TwoRu.HypOne.hypothesisOne_native

end CFSG.EvenSporadicStandard.Induction
