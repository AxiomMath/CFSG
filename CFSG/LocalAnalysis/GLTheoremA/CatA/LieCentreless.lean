module

public import CFSG.Assembly.InCatalogConverse
public import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier

public section

namespace CFSG.LocalAnalysis.GLTheoremA

theorem g2_center_eq_bot
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) :
    Subgroup.center (TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) = ⊥ := by
  obtain ⟨-, hsimp⟩ := CFSG.Assembly.lie_finite_simple ⟨.G2 q, hv⟩
  have hperf : Group.IsPerfect (TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :=
    CFSG.RankThree.PartTwo.Sec11.SetUp1118Proof.isPerfect_lie_G2 q hv
  rcases Subgroup.Normal.eq_bot_or_eq_top
      (Subgroup.center (TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩)) with h | h
  · exact h
  · exfalso
    have hcomm : IsMulCommutative (TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a ∈ Subgroup.center (TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
        rw [h]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    exact Group.IsPerfect.not_isMulCommutative _ hcomm

end CFSG.LocalAnalysis.GLTheoremA
