module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Reduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.RankThree.Lattice
open scoped Matrix

@[expose] noncomputable def langModelMulEquiv (τ : Tag) (K : Type) [Field K] (L : Type)
    [Field L] [Algebra K L] (g0 : ModGL τ L) : adjointGroup τ K ≃* langModel τ K L g0 :=
  ((adjointGroup τ K).equivMapOfInjective _ (baseChangeGL_injective _)).trans
    ((MulAut.conj g0⁻¹).subgroupMap _)

theorem coe_langModelMulEquiv (τ : Tag) (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]
    (g0 : ModGL τ L) (x : adjointGroup τ K) :
    ((langModelMulEquiv τ K L g0 x : langModel τ K L g0) : ModGL τ L) =
      g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * g0⁻¹⁻¹ :=
  rfl

end CFSG.HardMathSupport.Timmesfeld.CrossChar
