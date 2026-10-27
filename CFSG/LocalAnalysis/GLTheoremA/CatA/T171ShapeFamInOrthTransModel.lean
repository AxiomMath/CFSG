module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOrthTransMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOmGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundBase
public import CFSG.LieType.SeitzGeneration.StandardTypeOrthModel
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Extra
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamOutBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.ClassicalInvolution.Generic.StepLayer
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.LieType.SeitzGeneration.OrthStatementScopes
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
import CFSG.ClassicalInvolution.Generic.StepDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus)
open CFSG.RankThree.Classical2

noncomputable def orthModelEquivPlus (m : ℕ) (K : Type) [Field K] :
    LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)) ≃*
      ProjOrthDerived (quadPlus m K) :=
  CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.projOrthEquiv (coe_quadPlus m K)

noncomputable def orthModelEquivMinus (m : ℕ) (K : Type) [Field K] (b c : K) :
    LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (m - 1) b c)) ≃*
      ProjOrthDerived (quadMinus m K b c) :=
  (CFSG.LieType.SeitzGeneration.standardTypeOmegaMinusEquiv (m - 1) K b c).trans
    (CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.projOrthEquiv
      (coe_quadMinus m K b c))

theorem isComponentOf_map_piCenterQuot_of_conj {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J : Subgroup G} {d : G} {R : Type} [Group R] [Finite R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (hd : d ∈ Subgroup.normalizer (L : Set G)) (x : R)
    (hind : LargeEvenInduces θ (conjRel d) (MulAut.conj x))
    (hJ : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G))) :
    CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
      (Subgroup.centralizer ({x} : Set R)) := by
  have h := componentDescent_component θ hd hind ((CFSG.Assembly.isComponentOf_iff_open).2 hJ)
  rwa [CFSG.ClassicalInvolution.Generic.fixedSubgroup_conj_eq_centralizer] at h

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
