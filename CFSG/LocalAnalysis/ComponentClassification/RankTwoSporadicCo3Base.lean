
module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo3CheckBase
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjWY
public import CFSG.Sporadic.Schreier.Co3Order
public import CFSG.Sporadic.Schreier.Co3Faithful
public import CFSG.Sporadic.SmallOddCore.Co3Aut
public import CFSG.Sporadic.Co3
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo3Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjW
public import Certificates.Data.CFSGNative.Mathieu.M12
public import CFSG.Sporadic.Schreier.Co3Arrays
public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3Cert
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.Co3CentralizerCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3SylowCheck
public meta import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import CFSG.Sporadic.Schreier.Co3FaithfulCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3FaithfulData
public meta import Certificates.Data.CFSGNative.Co3.Data
public import CFSG.Sporadic.Schreier.Co3FirstCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public meta import CFSG.Sporadic.Schreier.Co3Sp6Check
public import CFSG.Sporadic.Schreier.Co3GenerationCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3SecondCheck
public meta import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.CountSpec
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Count
public import CFSG.Sporadic.Schreier.Co3StabItInputs
public meta import CFSG.Sporadic.Schreier.Co3StabItInputs
public import CFSG.Sporadic.Schreier.Co3OrbitZCheckInputs
public meta import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public import CFSG.Sporadic.Schreier.Co3SecondCheckInputs
public meta import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Monster.B.Mathieu.Order
public import CFSG.Sporadic.Schreier.Co3SecondImageCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3GenerationCheck
public import CFSG.Sporadic.Schreier.Co3Sp6CheckInputs
public meta import CFSG.Sporadic.Schreier.Co3Outer
public meta import Mathlib.Data.Matrix.Block
public import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3OrderCheck
public import CFSG.Sporadic.Schreier.M12Data
public import CFSG.Sporadic.Schreier.M12PinnedInputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM12Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM12Derivs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M12
public meta import CFSG.Sporadic.Schreier.M12Pinned
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Certificates.Data.CFSGNative.Co3.Data
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.Monster.Code.Weights
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.Th.F2Spec

@[expose] public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co3

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier.Co3
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem co3InP_iff (a : Array ℕ) (g : Equiv.Perm (Fin 276)) (h : Rep 276 a g) :
    co3InP a = true ↔ g ∈ co3P :=
  siftA_iff_mem_originalSubgroup co3ChainArrays (by norm_num) co3Order_check.1 h

theorem co3P_center_eq_bot : center ↥co3P = ⊥ := by
  have : IsSimpleGroup ↥co3P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co3.isSimpleGroup_Co3 co3PermEquiv.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥co3P) with h | h
  · exact h
  · exfalso
    let _ : CommGroup ↥co3P :=
      { (inferInstance : Group ↥co3P) with
        mul_comm := fun a b => mem_center_iff.mp (h ▸ mem_top b) a }
    have hp := IsSimpleGroup.prime_card (α := ↥co3P)
    rw [card_co3P] at hp
    exact absurd hp (by norm_num)

theorem co3AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .Co3) ↥co3P (co3P.subgroupOf co3P) :=
  autModel_of_allInner co3PermEquiv.symm co3P_center_eq_bot
    CFSG.Sporadic.SmallOddCore.co3P_allInner

end CFSG.ComponentClassification.RankTwoSporadic.Co3
