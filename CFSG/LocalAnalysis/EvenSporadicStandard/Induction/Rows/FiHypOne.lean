module

public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiTwoSylowFinkelstein
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Defs

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem card_sylow_eq_two_of_oddCover (h25 : Finkelstein77.Asc76Lemma25)
    {s : TauCeti.SporadicName} (hr : ∀ (X : Type) [Group X], IsLS [s] X → 3 ≤ CFSG.pRank 2 X)
    (hI : HypothesisOne (Carrier s)) {H : Type} [Group H] [Finite H] {N L : Subgroup H}
    (hN : FStarSimple N) (hidx : N.index ≤ 2) (hcov : OddCover s L) (hstd : SolStd L)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S) {t : H}
    (htC : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) :
    ∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2 := by
  obtain ⟨e⟩ := hcov.2.2
  exact card_sylow_eq_two_of_finkelstein_of_lemma25_of_pRank h25 hN hidx hstd hcov.1 hcov.2.1
    hcyc (CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hI)
    (hr _ (isLS_iff.2 ⟨_, List.mem_singleton_self _, hcov⟩)) htC ht2

end CFSG.EvenSporadicStandard.Induction
