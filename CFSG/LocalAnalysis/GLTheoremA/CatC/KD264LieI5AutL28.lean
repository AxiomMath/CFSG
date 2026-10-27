module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5AutGen
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTypes
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open

theorem kd264I5Aut_l28 (e : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie e).Group]
    (q : TauCeti.PrimePower) (he : e.1 = .A 1 q) (hq : q.card = 8) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group)) ≤ 2 := by
  have hq8 : q.p ^ q.exponent = 8 := (TauCeti.PrimePower.card_def q).symm.trans hq
  obtain ⟨hp2, hk3⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.I5Aut.prime_pow_eq_eight
    q.prime_p q.exponent_pos hq8
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : CFSG.AGLEmbedding.IsLinTwoIndex 2 3 e := ⟨q, he, hp2, hk3⟩
  obtain ⟨φ⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hL : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd
      (TauCeti.CFSGIndex.lie e).Group :=
    ⟨3, ⟨1, by norm_num⟩, by norm_num, ⟨φ⟩⟩
  exact CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_L2 hL

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
