module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPairs

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem pair_sylow_ambient_of_whole_fixed_pair
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (P : Sylow p (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G))
    (hpair : pointFixedSet H
      ((P : Subgroup (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
        (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G).subtype) = {a, b}) :
    ∃ T : Sylow p G, (T : Subgroup G) =
      (P : Subgroup (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
        (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G).subtype := by
  let : Fact p.Prime := ⟨hp⟩
  let B := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  let PG : Subgroup G := (P : Subgroup B).map B.subtype
  have hPGp : IsPGroup p PG := P.isPGroup'.map B.subtype
  obtain ⟨T, hPGT⟩ := hPGp.exists_le_sylow
  refine ⟨T, ?_⟩
  apply le_antisymm
  · by_contra hnot
    have hproper : PG < (T : Subgroup G) := lt_iff_le_not_ge.mpr ⟨hPGT, hnot⟩
    let U : Subgroup G := (T : Subgroup G) ⊓ Subgroup.normalizer (PG : Set G)
    have hgrowth : PG < U := pSubgroup_lt_normalizer_intersection p hp PG
      (T : Subgroup G) T.isPGroup' hproper
    have hUp : IsPGroup p U := T.isPGroup'.of_injective
      (Subgroup.inclusion (show U ≤ (T : Subgroup G) from inf_le_left))
      (Subgroup.inclusion_injective _)
    have hUB : U ≤ B := odd_p_normalizer_fixes_whole_pair H PG U p hp hodd hUp
      inf_le_right a b hab hpair
    have hUinternal : IsPGroup p (U.subgroupOf B) := hUp.of_injective
      (Subgroup.subgroupOfEquivOfLe hUB).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hUB).injective
    have hPU : (P : Subgroup B) ≤ U.subgroupOf B := by
      intro x hx
      exact hgrowth.le (Subgroup.mem_map_of_mem B.subtype hx)
    have hUeq := P.is_maximal' hUinternal hPU
    have hmap := congrArg (Subgroup.map B.subtype) hUeq
    rw [Subgroup.map_subgroupOf_eq_of_le hUB] at hmap
    exact hgrowth.ne hmap.symm
  · exact hPGT

theorem pair_sylow_ambient_and_whole_fixed_set
    {H Q : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q)
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Nat.card (conjugacyWithin H z))
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (P : Sylow p (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)) :
    (∃ T : Sylow p G, (T : Subgroup G) =
      (P : Subgroup (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
        (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G).subtype) ∧
      pointFixedSet H
        ((P : Subgroup (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
          (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G).subtype) = {a, b} := by
  have hpair := pair_sylow_whole_fixed_set h S hzS hzcenter hQH hQnormal hQtwo hzQ
    p hp hdiv a b hab P
  have hodd := (prime_dividing_point_class_odd_part_gt_one h S hzS hzcenter p hp hdiv).1
  exact ⟨pair_sylow_ambient_of_whole_fixed_pair H p hp hodd a b hab P hpair, hpair⟩

theorem every_sylow_two_fixed_of_one
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) (P : Sylow p G)
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (hpair : pointFixedSet H (P : Subgroup G) = {a, b}) (T : Sylow p G) :
    ∃ lambda mu : pointRightCosetSpace H, lambda ≠ mu ∧
      pointFixedSet H (T : Subgroup G) = {lambda, mu} := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P T
  let lambda := pointRightCosetMul H a g⁻¹
  let mu := pointRightCosetMul H b g⁻¹
  have hmap : ((g • P : Sylow p G) : Subgroup G) = rightConjugate (P : Subgroup G) g⁻¹ := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    simp only [rightConjugate, Subgroup.conjBy, inv_inv]
    rfl
  have hfixed : ∀ omega : pointRightCosetSpace H,
      omega ∈ pointFixedSet H (P : Subgroup G) ↔
        pointRightCosetMul H omega g⁻¹ ∈ pointFixedSet H ((g • P : Sylow p G) : Subgroup G) := by
    intro omega
    constructor
    · intro homega x hx
      rw [hmap, rightConjugate, Subgroup.conjBy] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hh := point_right_fixed_conjugate (homega y hy) g⁻¹
      simpa only [rightConjugateElem, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv] using hh
    · intro homega x hx
      have hxmap : rightConjugateElem x g⁻¹ ∈ ((g • P : Sylow p G) : Subgroup G) := by
        rw [hmap, rightConjugate, Subgroup.conjBy]
        simpa only [rightConjugateElem, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply, inv_inv] using
          Subgroup.mem_map_of_mem (MulAut.conj (g⁻¹)⁻¹).toMonoidHom hx
      have hh := homega _ hxmap
      have hhback := point_right_fixed_conjugate hh g
      simpa only [pointRightCosetMul_mul, inv_mul_cancel, pointRightCosetMul_one,
        rightConjugateElem, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, mul_one] using hhback
  have habnew : lambda ≠ mu := by
    intro heq
    have hh := congrArg (fun omega => pointRightCosetMul H omega g) heq
    have hh' : a = b := by
      simpa only [lambda, mu, pointRightCosetMul_mul, inv_mul_cancel, pointRightCosetMul_one] using hh
    exact hab hh'
  refine ⟨lambda, mu, habnew, ?_⟩
  ext omega
  constructor
  · intro homega
    have hback : pointRightCosetMul H omega g ∈ pointFixedSet H (P : Subgroup G) := by
      apply (hfixed _).mpr
      simpa only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one] using homega
    rw [hpair] at hback
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hback ⊢
    rcases hback with ha | hb
    · left
      have hh := congrArg (fun omega => pointRightCosetMul H omega g⁻¹) ha
      simpa only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one, lambda] using hh
    · right
      have hh := congrArg (fun omega => pointRightCosetMul H omega g⁻¹) hb
      simpa only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one, mu] using hh
  · intro homega
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at homega
    rcases homega with rfl | rfl
    · exact (hfixed a).mp (hpair.symm ▸ Set.mem_insert a {b})
    · exact (hfixed b).mp (hpair.symm ▸ Set.mem_insert_of_mem a rfl)

theorem every_ambient_sylow_whole_two_fixed_set
    {H Q : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q)
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Nat.card (conjugacyWithin H z))
    (T : Sylow p G) :
    ∃ lambda mu : pointRightCosetSpace H, lambda ≠ mu ∧
      pointFixedSet H (T : Subgroup G) = {lambda, mu} := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hgH⟩ : ∃ g : G, g ∉ H := by
    by_contra hnone
    apply h.proper
    apply top_unique
    intro g _
    by_contra hgH
    exact hnone ⟨g, hgH⟩
  let alpha := rightCosetMk H 1
  let beta := rightCosetMk H g
  have hab : alpha ≠ beta := by
    intro heq
    apply hgH
    apply (point_right_base_fixed_iff H g).mp
    rw [pointRightCosetMul_eq_translate, rightCosetTranslate_mk, one_mul]
    exact heq.symm
  let B := rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H beta
  let P : Sylow p B := default
  obtain ⟨⟨R, hR⟩, hpair⟩ := pair_sylow_ambient_and_whole_fixed_set
    h S hzS hzcenter hQH hQnormal hQtwo hzQ p hp hdiv alpha beta hab P
  rw [← hR] at hpair
  exact every_sylow_two_fixed_of_one H p hp R alpha beta hab hpair T

theorem every_ambient_sylow_fixed_card_two
    {H Q : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q)
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Nat.card (conjugacyWithin H z))
    (T : Sylow p G) : Nat.card (pointFixedSet H (T : Subgroup G)) = 2 := by
  obtain ⟨lambda, mu, hne, hpair⟩ := every_ambient_sylow_whole_two_fixed_set
    h S hzS hzcenter hQH hQnormal hQtwo hzQ p hp hdiv T
  rw [hpair]
  exact Set.ncard_pair hne

end CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
