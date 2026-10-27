module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6MinusculeFixedField
public import CFSG.LocalAnalysis.StandardType.GGFinModelExists
public import CFSG.LocalAnalysis.StandardType.GGFinModelTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer

public noncomputable section

namespace CFSG.StandardType.GGFinModel

open CFSG.Open CFSG.StandardType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP CFSG.LieType.Universal.Unitary
  CFSG.StandardType.CompactA2Pair CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.E6
  CFSG.RankThree.PartOne.TCX.E CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open scoped MatrixGroups commutatorElement

set_option maxHeartbeats 1000000

@[expose] noncomputable def twFinEmbedding (n f : ℕ) [NeZero f] :
    (ggU .twistedE6 n f).K →* e6Data_valid.minGroup GGL :=
  (minBC e6Data_valid (ggRatEmb (2 * f))).comp
    (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
      (GaloisField 2 (2 * f))
      (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)).subtype

theorem twFinEmbedding_injective (n f : ℕ) [NeZero f] :
    Function.Injective (twFinEmbedding n f) :=
  (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux.minBC_injective
    e6Data_valid (ggRatEmb (2 * f))).comp
    (Subgroup.subtype_injective (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
      (GaloisField 2 (2 * f))
      (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)))

end CFSG.StandardType.GGFinModel

