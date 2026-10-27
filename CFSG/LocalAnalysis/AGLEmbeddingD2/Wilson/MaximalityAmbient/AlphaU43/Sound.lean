
module


public import Certificates.Certificate12650
public import CFSG.Assembly.GL83LieDefs
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43AutData
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43InvData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43Perm
public import Certificates.Data.CFSGNative.Schreier.Merge

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.AlphaU43

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Certificates
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv CFSG.LieType.Multipliers.U43
  CFSG.RankThree.PartTwo.Sec6.Res611Res6.U43P

theorem outer_not_fix {b : X₀} (hb : orderOf b = 3)
    (τ : MulAut X₀) (hτ2 : τ ^ 2 = 1) (hτo : τ ∉ (MulAut.conj : X₀ →* MulAut X₀).range) :
    ¬ ∀ c ∈ Subgroup.centralizer ({b} : Set X₀), τ c = c :=
  Certificates.certificate12650 b hb τ hτ2 hτo

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.AlphaU43
