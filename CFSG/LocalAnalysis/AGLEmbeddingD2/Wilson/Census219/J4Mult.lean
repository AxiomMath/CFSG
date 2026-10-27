module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows
public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensus

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

theorem ks219J4Mult :
    KS219J4Mult := by
  intro Q _ _ hQ ⟨e⟩ _
  have hd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier (X := NativeSporadic.J4) hQ e
  have h1 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier NativeSporadic.J4) = 1 :=
    nativeRow_J4
  rw [h1] at hd
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 hd)

end CFSG.AGLEmbeddingD2.Wilson.Census219
