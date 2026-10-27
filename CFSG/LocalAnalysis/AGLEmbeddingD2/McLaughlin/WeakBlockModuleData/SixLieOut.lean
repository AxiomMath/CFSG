module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL5Proof
public import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

theorem card_eq_two_units {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card Kˣ = 1 := by
  rw [Nat.card_units, hK]

theorem autThreePowInner_psp_two {X : Type} [Group X] {r : ℕ} (hr : 3 ≤ r)
    (h : StatedClassicalModel X .PSp r 2 1) : AutThreePowInner X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  have h1 := CFSG.RankThree.PartTwo.Sec19.Step1919EndProof.card_outer_statedSp_le (r := r) hr
    (card_eq_two_units hK)
  have h2 := CFSG.RankThree.PartTwo.Sec19.Step1919EndProof.card_ringEquiv_le K
  have hpos : 0 < Nat.card (Outer (StatedProj (StatedSp r K))) := Nat.card_pos
  refine autThreePowInner_of_mulEquiv e
    (autThreePowInner_of_not_three_dvd_outer fun h3 => ?_)
  have := Nat.le_of_dvd hpos h3
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
