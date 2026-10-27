module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullThetaFixedPoints
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullCommutatorRank
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalNormalizerOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properHull_normalizer_orbit_class_flip
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (X : Subgroup G) (hzX : z ∈ Subgroup.normalizer (X : Set G))
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H)
    (delta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1))
    (hne : delta.val ≠ rightCosetMk H 1) :
    ∃ y : Subgroup.normalizer (X : Set G),
      pointRightCosetMul H (rightCosetMk H 1) (rightConjugateElem z (y : G)) = delta.val ∧
      pointRightCosetMul H delta.val (rightConjugateElem z (y : G)) = rightCosetMk H 1 := by
  let Y := Subgroup.normalizer (X : Set G)
  let zY : Y := ⟨z, hzX⟩
  let e := localNormalizerCosetOrbitEquiv H Y
  have hlocal := local_datum_subgroup_inheritance h Y hzX hescape
  let betaY := e.symm delta
  have hbase : e (rightCosetMk (H.subgroupOf Y) 1) =
      (⟨rightCosetMk H 1, numeratorRightOrbit_base H Y _⟩ : numeratorRightOrbit H Y _) := by
    apply Subtype.ext
    change (localNormalizerCosetOrbitEquiv H Y (rightCosetMk (H.subgroupOf Y) 1)).val =
      rightCosetMk H 1
    rw [localNormalizerCosetOrbitEquiv_apply, subgroupRightCosetInclusion_mk, Subgroup.coe_one]
  have hbetaY : betaY ≠ rightCosetMk (H.subgroupOf Y) 1 := by
    intro heq
    apply hne
    have he := congrArg (fun a => (e a).val) heq
    rw [e.apply_symm_apply, hbase] at he
    exact he
  obtain ⟨s, hs⟩ := original_pair_flip_exists hlocal betaY hbetaY
  obtain ⟨y, hy⟩ := hs.1
  have hfirst : rightCosetTranslate (H.subgroupOf Y)
      (rightCosetMk (H.subgroupOf Y) 1) s = betaY := hs.2
  have hsecond : rightCosetTranslate (H.subgroupOf Y) betaY s =
      rightCosetMk (H.subgroupOf Y) 1 :=
    (involution_point_uniform_pair_flips hlocal betaY hbetaY).2.1 s hs
  have hsG : (s : G) = rightConjugateElem z (y : G) :=
    (congrArg Subtype.val hy).symm
  have hfirstG := localNormalizerCosetOrbitEquiv_translate H Y
    (rightCosetMk (H.subgroupOf Y) 1) s
  have hsecondG := localNormalizerCosetOrbitEquiv_translate H Y betaY s
  rw [hfirst, e.apply_symm_apply, hbase] at hfirstG
  rw [hsecond, hbase, e.apply_symm_apply] at hsecondG
  exact ⟨y, hsG ▸ hfirstG.symm, hsG ▸ hsecondG.symm⟩

omit [Finite G] in
theorem properHull_pair_normalizer_of_involution_swap
    (H : Subgroup G) (s : G) (hs : s * s = 1)
    (alpha delta : pointRightCosetSpace H)
    (hfirst : pointRightCosetMul H alpha s = delta)
    (hsecond : pointRightCosetMul H delta s = alpha) :
    s ∈ Subgroup.normalizer
      ((rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H delta : Subgroup G) : Set G) := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  have hconj := properHull_point_stabilizer_right_conjugate H alpha s
  have hconj' := properHull_point_stabilizer_right_conjugate H delta s
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (rightCosetStabilizer H alpha).map (MulAut.conj s⁻¹).toMonoidHom =
    rightCosetStabilizer H (pointRightCosetMul H alpha s) at hconj
  change (rightCosetStabilizer H delta).map (MulAut.conj s⁻¹).toMonoidHom =
    rightCosetStabilizer H (pointRightCosetMul H delta s) at hconj'
  rw [hsinv, hfirst] at hconj
  rw [hsinv, hsecond] at hconj'
  change (rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H delta).map
    (MulAut.conj s).toMonoidHom = rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H delta
  rw [Subgroup.map_inf _ _ _ (MulAut.conj s).injective, hconj, hconj', inf_comm]

theorem properHull_theta_second_pair_centralizing_sylow
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (X : Subgroup G)
    (hX : IsPGroup p X) (hXH : X ≤ H)
    (hzX : z ∈ Subgroup.normalizer (X : Set G))
    (hself : ⁅X, Subgroup.zpowers z⁆ = X)
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H)
    (delta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1))
    (hdelta : delta.val ≠ rightCosetMk H 1)
    (hqB : q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (pairPointStabilizer H beta)))
    (hqE : ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (triplePointStabilizer H z beta))) :
    ∃ Q : Sylow q (minimalLocalFailurePairConfinementTheta p
        (pairPointStabilizer H delta.val)),
      let QG := (Q : Subgroup (minimalLocalFailurePairConfinementTheta p
        (pairPointStabilizer H delta.val))).map
          (minimalLocalFailurePairConfinementTheta p
            (pairPointStabilizer H delta.val)).subtype
      QG ≠ ⊥ ∧ IsPGroup q QG ∧
        QG ≤ minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H delta.val) ∧
        QG ≤ Subgroup.centralizer (X : Set G) := by
  obtain ⟨y, hyfirst, hysecond⟩ := properHull_normalizer_orbit_class_flip h X hzX hescape
    delta hdelta
  let s := rightConjugateElem z (y : G)
  have hsclass : s ∈ involutionPointClass z := ⟨(y : G), rfl⟩
  have hsorder : orderOf s = 2 := order_two_of_mem_pointClass h.distinguished_order hsclass
  have hssq : s * s = 1 := by
    simpa only [hsorder, pow_two] using pow_orderOf_eq_one s
  have hsX : s ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).mul_mem
      ((Subgroup.normalizer (X : Set G)).mul_mem
        ((Subgroup.normalizer (X : Set G)).inv_mem y.property) hzX) y.property
  let D := pairPointStabilizer H delta.val
  have hXD : X ≤ D := le_inf
    (by simpa only [rightCosetStabilizer_base] using hXH)
    (normalizer_orbit_stabilizer_contains hXH (by
      obtain ⟨a, ha, heq⟩ := delta.property
      exact ⟨⟨a, ha⟩, heq⟩))
  have hsD : s ∈ Subgroup.normalizer (D : Set G) :=
    properHull_pair_normalizer_of_involution_swap H s hssq (rightCosetMk H 1)
      delta.val hyfirst hysecond
  have hpaircard := properHull_pair_theta_card_of_double_transitivity H p hdoubly
    (rightCosetMk H 1) beta (rightCosetMk H 1) delta.val hbeta.symm hdelta.symm
  have hqD : q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p D) :=
    hpaircard ▸ hqB
  obtain ⟨Q, hQne, hQ, hQC, hXQ, hsQ⟩ := properHull_theta_nontrivial_joint_sylow
    p q hp hq D X s hX hsorder hsX (hXD.trans Subgroup.le_normalizer) hsD hqD
  let QG := (Q : Subgroup (minimalLocalFailurePairConfinementTheta p D)).map
    (minimalLocalFailurePairConfinementTheta p D).subtype
  obtain ⟨epsilon, hfix, huniq⟩ :=
    (((involution_point_unique_containment_action h.distinguished_mem
      h.distinguished_order).2 h.unique_containment).2.1 s hsclass)
  have hbaseNe : rightCosetMk H 1 ≠ epsilon := by
    intro heq
    rw [← heq] at hfix
    exact hdelta ((hfix.symm.trans hyfirst).symm)
  have hcard := properHull_distinguished_triple_theta_card h S hzS hzcenter hdoubly p
    beta hbeta s hsclass epsilon (rightCosetMk H 1) hfix hbaseNe
  have hthird : pointRightCosetMul H (rightCosetMk H 1) s = delta.val := hyfirst
  rw [hthird] at hcard
  have hEcomm : (D ⊓ rightCosetStabilizer H epsilon) =
      ((rightCosetStabilizer H epsilon ⊓ rightCosetStabilizer H (rightCosetMk H 1)) ⊓
        rightCosetStabilizer H delta.val) := by
    ext a
    change ((a ∈ rightCosetStabilizer H (rightCosetMk H 1) ∧
        a ∈ rightCosetStabilizer H delta.val) ∧ a ∈ rightCosetStabilizer H epsilon) ↔
      ((a ∈ rightCosetStabilizer H epsilon ∧
        a ∈ rightCosetStabilizer H (rightCosetMk H 1)) ∧
          a ∈ rightCosetStabilizer H delta.val)
    tauto
  have hqFix : ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (D ⊓ rightCosetStabilizer H epsilon)) := by
    rw [hEcomm, hcard]
    exact hqE
  have hselfs := properHull_self_commutator_right_conjugate X z (y : G) y.property hself
  have hcentral := properHull_theta_self_commutator_centralizes h hsclass epsilon hfix
    p q hp hq D X QG hQ hQC hXQ hsQ hqFix hselfs
  exact ⟨Q, hQne, hQ, hQC, hcentral.2⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
