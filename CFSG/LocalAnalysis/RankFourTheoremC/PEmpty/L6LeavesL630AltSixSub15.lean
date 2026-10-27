module

public import CFSG.LargeExtraspecial.S45QSix
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630SigmaRed

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

theorem not_comm_of_isSimpleGroup {G : Type} [Group G] [IsSimpleGroup G]
    (hcard : Nat.card G = 60 ∨ Nat.card G = 360) : ¬ ∀ a b : G, a * b = b * a := by
  intro hcomm
  haveI : IsMulCommutative G := ⟨⟨hcomm⟩⟩
  have hp : (Nat.card G).Prime := (Group.is_simple_iff_prime_card (α := G)).mp inferInstance
  rcases hcard with h | h <;> rw [h] at hp <;> norm_num at hp

theorem kFactAltSixSub15_holds : KFactAltSixSub15 := by
  unfold KFactAltSixSub15
  intro K hKA h15
  obtain ⟨hs, hcard⟩ := CFSG.LargeExtraspecial.S45Q.simple_of_le_alternatingGroup hKA h15
  haveI := hs
  refine ⟨hs, ?_, not_comm_of_isSimpleGroup hcard⟩
  rcases hcard with h | h <;> rw [h] <;> norm_num

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
