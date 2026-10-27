module

public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

theorem le_centralizer_isPComponent_normal_of_isStandardSubgroup {G : Type} [Group G] [Finite G]
    {t : G} {J : Subgroup G} (hst : IsStandardSubgroup J) (ht : orderOf t = 2)
    (htJ : t ∈ centralizer (J : Set G)) :
    J ≤ centralizer ({t} : Set G) ∧ IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set G))) ∧
      (J.subgroupOf (centralizer ({t} : Set G))).Normal := by
  have hstd : Assembly.ComponentType.IsStandardSubgroup J :=
    CFSG.StandardSubgroupAPI.isStandardSubgroup_iff_assembly.1 hst
  obtain ⟨-, hJt, hJn, hComp, -⟩ :=
    LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hstd htJ ht
  refine ⟨hJt, ?_, hJn⟩
  have hK : CFSG.IsComponent (J.subgroupOf (centralizer ({t} : Set G))) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hComp.1).1 hComp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable (CFSG.pPrimeCore 2 ↥(centralizer ({t} : Set G))) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.1
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := centralizer ({t} : Set G))))
  exact (LocalAnalysis.ComponentInitial.solvable_prime_core_ordinary_components 2
    Nat.prime_two hsolv).1 _ hK

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
