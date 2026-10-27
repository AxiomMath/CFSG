module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6AdjointA2Algebraic
public import CFSG.LocalAnalysis.StandardType.GGActualQuadraticField
public import CFSG.LocalAnalysis.StandardType.GGUnitaryTwoResidual
public import CFSG.LocalAnalysis.StandardType.GGFinModelIndex
public import CFSG.ClassicalInvolution.Balance.BootstrapDischarge
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Chain
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6AdjointA2

public noncomputable section

namespace CFSG.StandardType.GGFinModel

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.CompactA2Pair CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.E6
  CFSG.RankThree.PartOne.TCX.E
open scoped MatrixGroups

noncomputable instance actualQuadraticSubfieldAlgebra {f : ℕ} [NeZero f] :
    Algebra (ZMod 2) (actualQuadraticSubfield f) :=
  RingHom.toAlgebra ((algebraMap (ZMod 2) GGL).codRestrict (actualQuadraticSubfield f) (fun x => by
    rw [mem_actualQuadraticSubfield_iff]
    rw [← map_pow]
    congr 1
    have hval : x.val = 0 ∨ x.val = 1 := by
      have := ZMod.val_lt x
      omega
    rcases hval with h | h
    · rw [← ZMod.natCast_zmod_val x, h]; simp
    · rw [← ZMod.natCast_zmod_val x, h]; simp))

noncomputable instance actualQuadraticSubfieldIsAlgebraic {f : ℕ} [NeZero f] :
    Algebra.IsAlgebraic (ZMod 2) (actualQuadraticSubfield f) :=
  Algebra.IsAlgebraic.of_finite _ _

theorem e6IsogenyAlgebraic_minBC_algebraic_square_actualQuadraticSubfield
    {f : ℕ} [NeZero f]
    (Ψ : SL(3, actualQuadraticSubfield f) →*
        e6Data_valid.minGroup (actualQuadraticSubfield f))
    (ρ : SL(3, actualQuadraticSubfield f) →*
        adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f))
    (hρ : ρ = (e6IsogenyT (actualQuadraticSubfield f)).comp Ψ) :
    e6IsogenyAlgebraic.comp
        ((minBC e6Data_valid (actualQuadraticSubfield f).subtype).comp Ψ) =
      (baseChangeGL ((actualQuadraticSubfield f).subtype)).comp
        ((adjointGroup TwistTag.E6.tag (actualQuadraticSubfield f)).subtype.comp ρ) := by
  exact CFSG.ClassicalInvolution.WeakCT.e6IsogenyAlgebraic_minBC_algebraic_square
    (k := actualQuadraticSubfield f) (Ω := GGL)
    (ι := (actualQuadraticSubfield f).subtype) Ψ ρ hρ

end CFSG.StandardType.GGFinModel

end
