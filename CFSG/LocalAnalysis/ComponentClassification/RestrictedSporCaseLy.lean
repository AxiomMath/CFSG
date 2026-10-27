module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs
public import CFSG.Sporadic.Schreier.LyOuter

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.LySchreier
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_isSmallOrder_A11 : ¬ IsSmallOrder 19958400 :=
  not_isSmallOrder_of_between (q₀ := 341) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sporadicCase_Ly_of_inputs (hout : LyOuterTrivialInput) : SporadicCase .Ly := by
  refine sporadicCase_of_comps (fun G _ _ hG t ht => ?_)
    (outer_of_forall_inner fun α => by
      show α ∈ inner NativeSporadic.Ly
      rw [hout]
      trivial)
  obtain ⟨hq, -, ⟨eA⟩⟩ := involution_centralizers_quasisimple hG t ht
  have hcard : Nat.card (centralizer ({t} : Set G) ⧸ center (centralizer ({t} : Set G))) =
      19958400 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  refine (compsSatisfy_of_isQuasisimple hq (isoInvariant_card_quotient_center {19958400})
    hcard).mono fun Y _ h => not_small_of_card_quotient ?_
  rw [Set.mem_singleton_iff.1 h]
  exact not_isSmallOrder_A11

end CFSG.ComponentClassification.RestrictedStd.Spor
