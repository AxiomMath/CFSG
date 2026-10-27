module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BCoxeterB
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicBetaOf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.RankThree.OddKernel.SporadicKernelRestrictionB
public import CFSG.RankThree.PartOne.SPOR.OuterB

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.AGLEmbedding.BCox CFSG.RankThree.PartOne.CTP.Fus

theorem primeFactors_card_B :
    Nat.primeFactors 4154781481226426191177580544000000 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 47} := by
  norm_num [Nat.primeFactors]

section

theorem card_B_carrier :
    Nat.card (NativeSporadic.Carrier .B) = 4154781481226426191177580544000000 :=
  CFSG.RankThree.OddKernel.card_B_eq

theorem card_B_pos : 2 < Nat.card NativeSporadic.B := by
  rw [CFSG.RankThree.OddKernel.card_B_eq]
  norm_num

theorem three_le_pRank_B_three [Finite (NativeSporadic.Carrier .B)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .B)) :=
  three_le_pRank_B card_B_pos

theorem sporadicCaseThreeData_B_of
    (h5 : ∀ [Finite NativeSporadic.B] [Fact (Nat.Prime 5)],
      SporCaseThreePrimeData NativeSporadic.B 5) :
    SporadicCaseThreeData (NativeSporadic.Carrier .B) := by
  refine sporadicCaseThreeData_of_card (X := NativeSporadic.Carrier .B) card_B_carrier
    (by norm_num) ?_
  intro p hp hp2 _ _
  rw [primeFactors_card_B] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · exact sporCaseThreePrimeData_B_three card_B_pos
  · exact h5
  all_goals exact sporCaseThreePrimeData_of_not_dvd (by rw [card_B_carrier]; norm_num)

theorem sporadicBetaData_B_of (h5 : FusionGenerationOf NativeSporadic.B 5) :
    SporadicBetaData (NativeSporadic.Carrier .B) := by
  refine sporadicBetaData_of_card (X := NativeSporadic.Carrier .B) card_B_carrier (by norm_num)
    (by rw [CFSG.RankThree.PartOne.SPOR.card_outer_B]; norm_num) ?_
  intro p hp hp2
  rw [primeFactors_card_B] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · exact Or.inr (Or.inr (fusionGenerationOf_B_three card_B_pos))
  · exact Or.inr (Or.inr h5)
  all_goals exact Or.inl (by norm_num)

end

end CFSG.AGLEmbedding
