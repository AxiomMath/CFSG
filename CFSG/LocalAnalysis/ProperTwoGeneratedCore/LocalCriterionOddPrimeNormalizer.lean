module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddPrimeNormalizerIsolation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStarFactorization

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] [Finite G]

theorem local_point_odd_subgroup_normalizer_sylow_central_class
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (M : Subgroup G) (hModd : Odd (Nat.card M))
    (hzM : z ∈ Subgroup.normalizer (M : Set G)) (hMH : ¬ M ≤ H)
    (S : Sylow 2 (Subgroup.normalizer (M : Set G)))
    (hzS : (⟨z, hzM⟩ : Subgroup.normalizer (M : Set G)) ∈ (S : Subgroup _)) :
    (⟨(⟨z, hzM⟩ : Subgroup.normalizer (M : Set G)), hzS⟩ : (S : Subgroup _)) ∈
        Subgroup.center (S : Subgroup _) ∧
      involutionPointClass z ∩
        (((S : Subgroup (Subgroup.normalizer (M : Set G))).map
          (Subgroup.normalizer (M : Set G)).subtype : Subgroup G) : Set G) = {z} := by
  let N := Subgroup.normalizer (M : Set G)
  let zN : N := ⟨z, hzM⟩
  let zS : (S : Subgroup N) := ⟨zN, hzS⟩
  have hc : zS ∈ Subgroup.center (S : Subgroup N) := by
    apply central_of_no_distinct_commuting_conjugate S.isPGroup' zS
    intro g hcomm
    apply Subtype.ext
    apply Subtype.ext
    apply local_point_odd_subgroup_normalizer_class_isolation h M hModd hzM hMH
      (show (g : G)⁻¹ * z * g ∈ involutionPointClass z from ⟨(g : G), rfl⟩)
      (N.mul_mem (N.mul_mem (N.inv_mem g.val.property) hzM) g.val.property)
    exact congrArg (fun a : (S : Subgroup N) => (a : G)) hcomm.eq
  refine ⟨hc, ?_⟩
  ext s
  constructor
  · rintro ⟨hsClass, hsImage⟩
    obtain ⟨a, ha, hsa⟩ := hsImage
    have haComm : Commute (a : G) z := by
      exact congrArg (fun b : (S : Subgroup N) => (b : G))
        ((Subgroup.mem_center_iff.mp hc) (⟨a, ha⟩ : (S : Subgroup N)))
    apply Set.mem_singleton_iff.mpr
    exact local_point_odd_subgroup_normalizer_class_isolation h M hModd hzM hMH
      hsClass (hsa ▸ a.property) (hsa ▸ haComm)
  · intro hs
    have heq := Set.mem_singleton_iff.mp hs
    subst s
    exact ⟨distinguished_mem_pointClass z,
      Subgroup.mem_map_of_mem N.subtype hzS⟩

theorem local_point_odd_subgroup_normalizer_full_class
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (M : Subgroup G) (hModd : Odd (Nat.card M))
    (hzM : z ∈ Subgroup.normalizer (M : Set G)) (hMH : ¬ M ≤ H) :
    involutionPointClass z ∩ (Subgroup.normalizer (M : Set G) : Set G) =
      conjugacyWithin (Subgroup.normalizer (M : Set G)) z := by
  let N := Subgroup.normalizer (M : Set G)
  let zN : N := ⟨z, hzM⟩
  have hzNorder : orderOf zN = 2 := (Subgroup.orderOf_coe zN).symm.trans
    h.distinguished_order
  have hzTwo : IsPGroup 2 (Subgroup.zpowers zN) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers, pow_one] using hzNorder)
  obtain ⟨S, hS⟩ := hzTwo.exists_le_sylow
  have hzS := hS (Subgroup.mem_zpowers zN)
  have hinter := (local_point_odd_subgroup_normalizer_sylow_central_class
    h M hModd hzM hMH S hzS).2
  ext s
  constructor
  · rintro ⟨hsClass, hsN⟩
    let sN : N := ⟨s, hsN⟩
    have hsOrder : orderOf sN = 2 := (Subgroup.orderOf_coe sN).symm.trans
      (order_two_of_mem_pointClass h.distinguished_order hsClass)
    obtain ⟨a, ha⟩ := LocalCriterionGeometry.involution_conjugate_into_sylow S hsOrder
    have hconjClass : (a : G)⁻¹ * s * a ∈ involutionPointClass z :=
      pointClass_right_conjugate_mem hsClass (a : G)
    have hconjImage : (a : G)⁻¹ * s * a ∈ (S : Subgroup N).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype ha
    have heq : (a : G)⁻¹ * s * a = z := by
      have hm := hinter ▸ (show (a : G)⁻¹ * s * a ∈ involutionPointClass z ∩
        (((S : Subgroup N).map N.subtype : Subgroup G) : Set G) from
          ⟨hconjClass, hconjImage⟩)
      exact Set.mem_singleton_iff.mp hm
    refine ⟨a⁻¹, ?_⟩
    change (a : G)⁻¹⁻¹ * z * (a : G)⁻¹ = s
    rw [inv_inv, ← heq]
    group
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(a : G), rfl⟩,
      N.mul_mem (N.mul_mem (N.inv_mem a.property) hzM) a.property⟩

theorem local_point_odd_subgroup_normalizer_zStar
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (M : Subgroup G) (hModd : Odd (Nat.card M))
    (hzM : z ∈ Subgroup.normalizer (M : Set G)) (hMH : ¬ M ≤ H) :
    let N := Subgroup.normalizer (M : Set G)
    let zN : N := ⟨z, hzM⟩
    (QuotientGroup.mk zN : N ⧸ CFSG.oddCore N) ∈
        Subgroup.center (N ⧸ CFSG.oddCore N) ∧
      (∀ a : N, ∃ c ∈ Subgroup.centralizer ({zN} : Set N),
        ∃ x ∈ CFSG.oddCore N, a = c * x) := by
  let N := Subgroup.normalizer (M : Set G)
  let zN : N := ⟨z, hzM⟩
  apply native_zStar_of_isolated_involution
    ((Subgroup.orderOf_coe zN).symm.trans h.distinguished_order)
  intro a hcomm
  apply Subtype.ext
  apply local_point_odd_subgroup_normalizer_class_isolation h M hModd hzM hMH
    (show (a : G)⁻¹ * z * a ∈ involutionPointClass z from ⟨(a : G), rfl⟩)
    (N.mul_mem (N.mul_mem (N.inv_mem a.property) hzM) a.property)
  exact congrArg Subtype.val hcomm.eq

theorem local_involution_point_odd_prime_normalizer_isolation
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (M : Subgroup G) (hM : IsPGroup p M)
    (hzM : z ∈ Subgroup.normalizer (M : Set G)) (hMH : ¬ M ≤ H) :
    let N := Subgroup.normalizer (M : Set G)
    let zN : N := ⟨z, hzM⟩
    (∀ s ∈ involutionPointClass z ∩ (N : Set G), Commute s z → s = z) ∧
      (∀ (S : Sylow 2 N) (hzS : zN ∈ (S : Subgroup N)),
        (⟨zN, hzS⟩ : (S : Subgroup N)) ∈ Subgroup.center (S : Subgroup N) ∧
          involutionPointClass z ∩
            (((S : Subgroup N).map N.subtype : Subgroup G) : Set G) = {z}) ∧
      involutionPointClass z ∩ (N : Set G) = conjugacyWithin N z ∧
      (QuotientGroup.mk zN : N ⧸ CFSG.oddCore N) ∈
        Subgroup.center (N ⧸ CFSG.oddCore N) ∧
      (∀ a : N, ∃ c ∈ Subgroup.centralizer ({zN} : Set N),
        ∃ x ∈ CFSG.oddCore N, a = c * x) := by
  have hModd := odd_prime_subgroup_card_odd p hp hodd M hM
  refine ⟨fun s hs hc => local_point_odd_subgroup_normalizer_class_isolation
    h M hModd hzM hMH hs.1 hs.2 hc, ?_, ?_, ?_⟩
  · exact local_point_odd_subgroup_normalizer_sylow_central_class h M hModd hzM hMH
  · exact local_point_odd_subgroup_normalizer_full_class h M hModd hzM hMH
  · exact local_point_odd_subgroup_normalizer_zStar h M hModd hzM hMH

end CFSG.ProperTwoGeneratedCore
