module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5111
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111K1

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem stmt5_1_11_three_of_F4 (hF : FactL2LieParabolic)
    (hG : FactRank2CartanGraph) (h38 : Vol2Native.A38ForSQTKCat) (hRL : RankOneListedFacts.{0})
    (hU3 : FactU3Cover) (h510 : Stmt5_1_10_F4) : Stmt5_1_11_three_F4 := by
  intro G _ _ T M L H B D n hyp hN _
  obtain ⟨k, hk, hBorel, -, K₁, hK₁, hKeq, hcases⟩ := h510 G T M L H B D n hyp hN
  rcases hcases with ⟨hlt, hX⟩ | ⟨-, hbend⟩ | ⟨-, htype, -⟩
  · exact Or.inl (three_two h38 hRL hyp hBorel hK₁ hKeq hlt hk.1 hX)
  ·
    refine Or.inl fun P hP => ?_
    have h := hyp.toHyp5_0_1
    have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
    have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
      A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
    have hRS := hRL _ (isRankOneListed_of_isBenderAny hU3 ⟨k, hk.1, hbend⟩)
    rcases le_or_le_borelOf hRS hTK
      ((le_inf inf_le_right Subgroup.le_normalizer).trans hP.1.le) hP.2.1 with h1 | h1
    · rw [le_antisymm hP.2.1 h1]
      exact ((pCoreOf_le 2 _).trans inf_le_right).trans (le_normalizer_oTwoUpper H)
    · exact absurd (lt_of_lt_of_le hP.1 h1) (lt_irrefl _)
  · exact three_rank2 hF hG hyp hBorel hk.1 htype

theorem stmt5_1_11_of_inputs_F4 (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) (hF : FactL2LieParabolic) (hG : FactRank2CartanGraph)
    (h38 : Vol2Native.A38ForSQTKCat) (hRL : RankOneListedFacts.{0}) (hU3 : FactU3Cover)
    (h510 : Stmt5_1_10_F4) : Stmt5_1_11_F4 :=
  stmt5_1_11_of_F4 h331 hR h510 (stmt5_1_11_three_of_F4 hF hG h38 hRL hU3 h510)

end CFSG.Quasithin.H13
