module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Defs
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem invariantTwoMaximalWithin_coprime_transitivity
    (prime : ℕ) (hprime : prime.Prime) (actingGroup overgroup first second Y : Subgroup G)
    (hactor : IsPGroup prime actingGroup) (hacting : actingGroup ≤ overgroup)
    (hfirst : invariantTwoMaximalWithin actingGroup overgroup first)
    (hsecond : invariantTwoMaximalWithin actingGroup overgroup second)
    (hY : Y ≤ overgroup) (hYc : prime.Coprime (Nat.card Y))
    (hYinv : actingGroup ≤ normalizer (Y : Set G))
    (hfY : first ≤ Y) (hsY : second ≤ Y) :
    ∃ conjugator : G, conjugator ∈ overgroup ∧
      conjugator ∈ centralizer (actingGroup : Set G) ∧
      first.map (MulAut.conj conjugator).toMonoidHom = second := by
  have hactorInternal := hactor.of_equiv (Subgroup.subgroupOfEquivOfLe hacting).symm
  have hfirstInternal := invariantTwoMaximalWithin_internal_global actingGroup overgroup first
    hacting hfirst
  have hsecondInternal := invariantTwoMaximalWithin_internal_global actingGroup overgroup second
    hacting hsecond
  have hcoprime : prime.Coprime (Nat.card (Y.subgroupOf overgroup)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv]
    exact hYc
  have hinvariant : actingGroup.subgroupOf overgroup ≤
      normalizer ((Y.subgroupOf overgroup : Subgroup overgroup) : Set overgroup) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hY]
    intro x hx
    exact hYinv hx
  obtain ⟨conjugator, hcentral, hequal⟩ :=
    rank_two_maximal_two_subgroups_common_signalizer_transitivity prime hprime
      (actingGroup.subgroupOf overgroup) (first.subgroupOf overgroup)
      (second.subgroupOf overgroup) (Y.subgroupOf overgroup) hactorInternal hfirstInternal
      hsecondInternal hcoprime hinvariant (fun x hx => hfY hx) (fun x hx => hsY hx)
  refine ⟨conjugator.val, conjugator.property, ?_, ?_⟩
  · apply Subgroup.mem_centralizer_iff.mpr
    intro actor hactorMem
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hcentral
      ⟨actor, hacting hactorMem⟩ hactorMem)
  · have hmapped := congrArg (Subgroup.map overgroup.subtype) hequal
    have hmaps : overgroup.subtype.comp (MulAut.conj conjugator).toMonoidHom =
        (MulAut.conj conjugator.val).toMonoidHom.comp overgroup.subtype := by
      ext element
      rfl
    rw [Subgroup.map_map, hmaps, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hfirst.1,
      Subgroup.map_subgroupOf_eq_of_le hsecond.1] at hmapped
    exact hmapped

theorem prime_dvd_card_invariantTwoJoinIn_normalizer_inf
    (prime : ℕ) (hprime : prime.Prime)
    (actingGroup overgroup first second : Subgroup G)
    (hactor : IsPGroup prime actingGroup) (hacting : actingGroup ≤ overgroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup second)
    (hfirstEscape : ¬ first ≤ overgroup) (hsecondLe : second ≤ overgroup)
    (hintersection : first ⊓ overgroup = first ⊓ second)
    (hcentralizer : centralizer (actingGroup : Set G) ≤ overgroup)
    (hmaximal : ∀ largerFirst largerSecond : Subgroup G,
      rankTwoMaximalInvariantTwoSubgroup actingGroup largerFirst →
      rankTwoMaximalInvariantTwoSubgroup actingGroup largerSecond →
      ¬ largerFirst ≤ overgroup → largerSecond ≤ overgroup →
      Nat.card (largerFirst ⊓ largerSecond : Subgroup G) ≤ Nat.card (first ⊓ second : Subgroup G))
    (hglobalize : ∀ localSecond : Subgroup G,
      invariantTwoMaximalWithin actingGroup overgroup localSecond →
      rankTwoMaximalInvariantTwoSubgroup actingGroup localSecond) :
    prime ∣ Nat.card (invariantTwoJoinIn actingGroup
      (normalizer ((first ⊓ second : Subgroup G) : Set G))) := by
  let intersection := first ⊓ second
  let localGroup := normalizer (intersection : Set G)
  have hlocalActor : actingGroup ≤ localGroup := common_normalizer_le_normalizer_inf
    actingGroup first second hfirst.2.1 hsecond.2.1
  have hproper : intersection < first := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hequal
    exact hfirstEscape (hequal.symm.le.trans (inf_le_right.trans hsecondLe))
  have hgrows := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two
    first intersection hfirst.1 hproper
  have hfirstNormalizingEscape : ¬ first ⊓ localGroup ≤ overgroup := by
    intro hbound
    have hsmaller : first ⊓ localGroup ≤ intersection := by
      change first ⊓ localGroup ≤ first ⊓ second
      rw [← hintersection]
      exact le_inf inf_le_left hbound
    exact hgrows.not_ge hsmaller
  obtain ⟨firstLocal, hfirstLe, hfirstLocal⟩ := exists_invariantTwoMaximalWithin_containing
    actingGroup localGroup (first ⊓ localGroup) inf_le_right hfirst.1.to_inf_left
    (invariant_normalizer_intersection actingGroup first second hfirst.2.1 hsecond.2.1)
  obtain ⟨secondLocal, hsecondLeLocal, hsecondLocal⟩ :=
    exists_invariantTwoMaximalWithin_containing actingGroup localGroup (second ⊓ localGroup)
      inf_le_right hsecond.1.to_inf_left (by
        simpa only [localGroup, intersection, inf_comm second first] using
          invariant_normalizer_intersection actingGroup second first hsecond.2.1 hfirst.2.1)
  by_contra hcop
  have hcoprime : prime.Coprime (Nat.card (invariantTwoJoinIn actingGroup localGroup)) :=
    hprime.coprime_iff_not_dvd.mpr hcop
  obtain ⟨conjugator, hconjugatorLocal, hconjugatorCentral, hconjugate⟩ :=
    invariantTwoMaximalWithin_coprime_transitivity prime hprime actingGroup localGroup
      firstLocal secondLocal (invariantTwoJoinIn actingGroup localGroup) hactor hlocalActor
      hfirstLocal hsecondLocal (invariantTwoJoinIn_le _ _) hcoprime
      (le_normalizer_invariantTwoJoinIn _ _)
      (le_invariantTwoJoinIn hfirstLocal.1 hfirstLocal.2.1 hfirstLocal.2.2.1)
      (le_invariantTwoJoinIn hsecondLocal.1 hsecondLocal.2.1 hsecondLocal.2.2.1)
  have hfirstLocalEscape : ¬ firstLocal ≤ overgroup :=
    fun hbound => hfirstNormalizingEscape (hfirstLe.trans hbound)
  have hsecondLocalEscape : ¬ secondLocal ≤ overgroup := by
    intro hbound
    exact hfirstLocalEscape ((conjugate_subgroup_le_iff_of_conjugator_mem firstLocal overgroup
      conjugator (hcentralizer hconjugatorCentral)).mp (hconjugate.le.trans hbound))
  obtain ⟨largerFirst, hsecondLocalLe, hlargerFirst⟩ :=
    exists_maximal_invariant_two_subgroup_containing actingGroup secondLocal
      hsecondLocal.2.1 hsecondLocal.2.2.1
  have hlargerFirstEscape : ¬ largerFirst ≤ overgroup :=
    fun hbound => hsecondLocalEscape (hsecondLocalLe.trans hbound)
  let commonInside := secondLocal ⊓ overgroup
  have hcommonInvariant : actingGroup ≤ normalizer (commonInside : Set G) :=
    common_normalizer_le_normalizer_inf actingGroup secondLocal overgroup
      hsecondLocal.2.2.1 (hacting.trans le_normalizer)
  obtain ⟨largerSecond, hcommonLe, hlargerSecondWithin⟩ :=
    exists_invariantTwoMaximalWithin_containing actingGroup overgroup commonInside inf_le_right
      hsecondLocal.2.1.to_inf_left hcommonInvariant
  have hlargerSecond := hglobalize largerSecond hlargerSecondWithin
  have hbound := hmaximal largerFirst largerSecond hlargerFirst hlargerSecond
    hlargerFirstEscape hlargerSecondWithin.1
  have hcommonLeBoth : commonInside ≤ largerFirst ⊓ largerSecond :=
    le_inf (inf_le_left.trans hsecondLocalLe) hcommonLe
  have hsmall := Subgroup.card_le_of_le hcommonLeBoth
  have hintersectionLeCommon : intersection ≤ commonInside := by
    exact le_inf ((le_inf inf_le_right le_normalizer).trans hsecondLeLocal)
      (inf_le_right.trans hsecondLe)
  have hcommonEq := Subgroup.eq_of_le_of_card_ge hintersectionLeCommon (hsmall.trans hbound)
  have hsecondLocalNormalizerLe : second ⊓ localGroup ≤ intersection := by
    rw [hcommonEq]
    exact le_inf hsecondLeLocal (inf_le_left.trans hsecondLe)
  have hsecondProper : intersection < second := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro hequal
    have hsecondContained : second ≤ first := hequal.symm.le.trans inf_le_left
    have hequalGroups := hsecond.2.2 first hfirst.1 hfirst.2.1 hsecondContained
    exact hfirstEscape (hequalGroups.le.trans hsecondLe)
  have hsecondGrows := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two
    second intersection hsecond.1 hsecondProper
  exact hsecondGrows.not_ge hsecondLocalNormalizerLe

theorem MaximalRelativePair.isRelPairCandidate {p : ℕ} (hS : Setting G) (hD1 : TheoremD1 G)
    (hp : p ∈ rankThreeSigmaA G) (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    {P : Sylow p G} {M D R T : Subgroup G} (hd : MaximalRelativePair p P M D R T) :
    IsRelPairCandidate p D R T (normalizer ((R ⊓ T : Subgroup G) : Set G)) := by
  have hprime := sigmaA_prime p hp
  obtain ⟨-, z, hzD, hz1, hzc, hzp, hN₀M, hCD, hglob⟩ :=
    hd.ext.transitivity_data hS hD1 hp hd.not_le_normalizer hR h13
  obtain ⟨hM, hDP, -, -⟩ := hd.ext.obstruction
  have hDM : D ≤ M := hDP.trans (sylow_le_of_isCoreMaxLocal hS hp hM).1
  refine ⟨hd.twoLocal, sup_le inf_le_right hd.le_normalizer, ?_⟩
  exact prime_dvd_card_invariantTwoJoinIn_normalizer_inf p hprime D M R T
    (P.isPGroup'.to_le hDP) hDM hd.maxR hd.maxT hd.not_le_R hd.le_T hd.inf_eq hCD hd.maximal
    (fun T₁ hT₁ => (hglob T₁ hT₁).1)

theorem MaximalRelativePair.exists_optimal {p : ℕ} (hS : Setting G)
    (hD1 : TheoremD1 G) (hp : p ∈ rankThreeSigmaA G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) {P : Sylow p G} {M D R T : Subgroup G}
    (hd : MaximalRelativePair p P M D R T) :
    ∃ H V : Subgroup G, IsOptimalRelPair p M D R T H V := by
  obtain ⟨V, hV⟩ := (hd.isRelPairCandidate hS hD1 hp hR h13).exists_pair hd.le_T hd.maxT.1
    hd.maxT.2.1 hd.le_normalizer
  exact exists_isOptimalRelPair hV

end CFSG.LocalAnalysis.RankThreeTheoremC
