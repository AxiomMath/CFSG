module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientRoot

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFchapter1section1 CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

theorem not_isCyclic_sylow_two_of_commutator_eq_top {L : Type*} [Group L] [Finite L]
    (hperf : commutator L = ⊤) (heven : 2 ∣ Nat.card L) (T : Sylow 2 L) :
    ¬ IsCyclic (T : Subgroup L) := by
  intro hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin : (Nat.card L).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr heven
  have hcomp := IsCyclic.isComplement' hmin hT
  have hker : (MonoidHom.transferSylow T (hT.normalizer_le_centralizer hmin)).ker = ⊤ := by
    refine eq_top_iff.mpr (hperf ▸ (commutator_def L) ▸ Subgroup.commutator_le.mpr ?_)
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    have := IsCyclic.isMulCommutative (α := (T : Subgroup L))
    exact mul_comm' _ _
  rw [hker, Subgroup.isComplement'_top_left] at hcomp
  exact T.ne_bot_of_dvd_card heven hcomp

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {x : G}

namespace EscapingQuotientData

variable (hq : EscapingQuotientData H x) {J : Subgroup (EscapingQuotient x)}
  (hJ : CFSG.IsComponent J) (hxJ : escapingBar x ∉ J)
include hq hJ hxJ

theorem component_isSimpleBenderGroup : IsSimpleBenderGroup J :=
  CFSG.BenderSuzuki.theorem_SE_simple _ (hq.component_isStronglyEmbedded hJ hxJ)
    (hq.component_isSimpleGroup hJ hxJ)

theorem component_centralizer_normal :
    (Subgroup.centralizer (J : Set (EscapingQuotient x))).Normal := by
  have := hq.component_normal hJ hxJ
  infer_instance

end EscapingQuotientData

end CFSG.ProperTwoGeneratedCore.Assembly
