module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4Sz
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup
open CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem K1_le_canonicalPerfectLift
    {H K1 : Subgroup G} {A : Subgroup (H ⧸ pPrimeCore 2 ↥H)}
    (hK1H : K1 ≤ H)
    (hAeq : A = (K1.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)))
    (hK1perf : Group.IsPerfect K1) :
    K1 ≤ canonicalPerfectLift H A := by
  classical
  let π : ↥H →* (↥H ⧸ pPrimeCore 2 ↥H) := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  let V : Subgroup ↥H := A.comap π
  have hK1V : K1.subgroupOf H ≤ V := by
    intro k hk
    rw [Subgroup.mem_comap]
    rw [hAeq]
    exact Subgroup.mem_map_of_mem π hk
  have hK1com : ⁅K1, K1⁆ = K1 := (Subgroup.isPerfect_iff).mp hK1perf
  have hK1Hperf : Group.IsPerfect ↥(K1.subgroupOf H) :=
    CFSG.Quasithin.H13.isPerfect_subgroupOf hK1H hK1com
  have hK1W : K1.subgroupOf H ≤ CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf V :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
      (K1.subgroupOf H) V hK1Hperf hK1V
  have hmap : K1 = (K1.subgroupOf H).map H.subtype :=
    (Subgroup.map_subgroupOf_eq_of_le hK1H).symm
  rw [hmap]
  calc (K1.subgroupOf H).map H.subtype
      ≤ (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf V).map H.subtype :=
        Subgroup.map_mono hK1W
    _ = canonicalPerfectLift H A := rfl

end CFSG.ComponentClassification.FooteMarked
