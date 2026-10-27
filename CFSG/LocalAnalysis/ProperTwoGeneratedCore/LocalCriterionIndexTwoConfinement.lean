module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalSubgroups
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStar
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoStrongEmbedding
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.External CFSG.SignalizerFunctor.Helpers
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem even_normal_subgroup_contains_central_sylow_involution
    (S : Sylow 2 G) (M : Subgroup G) [M.Normal]
    (heven : Even (Nat.card M)) :
    ∃ v : G, v ∈ M ∧ v ∈ (S : Subgroup G) ∧
      (∀ s ∈ (S : Subgroup G), Commute v s) ∧ orderOf v = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Sylow 2 M := hallSylowSubgroupOfNormal S M
  have hTne : (T : Subgroup M) ≠ ⊥ :=
    T.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven)
  let N : Subgroup S := M.subgroupOf (S : Subgroup G)
  have hNne : N ≠ ⊥ := by
    intro hNbot
    have hmeet : (S : Subgroup G) ⊓ M = ⊥ := by
      have hmap : N.map (S : Subgroup G).subtype = ⊥ := by
        rw [hNbot, Subgroup.map_bot]
      change (M.subgroupOf (S : Subgroup G)).map (S : Subgroup G).subtype = ⊥ at hmap
      rw [Subgroup.subgroupOf_map_subtype, inf_comm] at hmap
      exact hmap
    apply hTne
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_bot]
    exact (normal_sylow_intersection_eq S M).trans hmeet
  obtain ⟨v, hvM, hvcenter, hvorder⟩ :=
    normal_two_subgroup_contains_central_involution S.isPGroup' N hNne
  refine ⟨(v : G), hvM, v.property, ?_, (Subgroup.orderOf_coe v).trans hvorder⟩
  intro s hs
  exact (show Commute (v : G) s from
    (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hvcenter) (⟨s, hs⟩ : S))).symm)

theorem sylow_involution_centralizer_escape_of_not_strongly_embedded
    (H : Subgroup G) (hproper : H ≠ ⊤) (heven : Even (Nat.card H))
    (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ H)
    (hNS : Subgroup.normalizer (S : Set G) ≤ H)
    (hnot : ¬ CFSG.BenderSuzuki.IsStronglyEmbedded H) :
    ∃ u : G, u ∈ (S : Subgroup G) ∧ orderOf u = 2 ∧
      ¬ Subgroup.centralizer ({u} : Set G) ≤ H := by
  have hexists : ∃ u : G, u ∈ H ∧ orderOf u = 2 ∧
      ¬ Subgroup.centralizer ({u} : Set G) ≤ H := by
    by_contra hnone
    apply hnot
    apply native_strong_embedding_of_sylow_normalizer_involution_centralizers
      H hproper heven S hSH hNS
    intro u hu huorder
    by_contra hescape
    exact hnone ⟨u, hu, huorder, hescape⟩
  obtain ⟨u, huH, huorder, huescape⟩ := hexists
  let uH : H := ⟨u, huH⟩
  have huHorder : orderOf uH = 2 := (Subgroup.orderOf_coe uH).symm.trans huorder
  obtain ⟨a, ha⟩ := LocalCriterionGeometry.involution_conjugate_into_sylow
    (S.subtype hSH) huHorder
  let v := (a : G)⁻¹ * u * a
  have hvS : v ∈ (S : Subgroup G) := by
    simpa only [Sylow.coe_subtype, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_inv, uH] using ha
  have hvorder : orderOf v = 2 := by
    simpa only [MulAut.conj_apply, inv_inv, v] using
      ((MulAut.conj (a : G)⁻¹).orderOf_eq u).trans huorder
  refine ⟨v, hvS, hvorder, ?_⟩
  intro hvcentral
  apply huescape
  intro c hc
  have hconj : (a : G)⁻¹ * c * a ∈ Subgroup.centralizer ({v} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj (a : G)⁻¹)
      (Subgroup.mem_centralizer_singleton_iff.mp hc)
    simpa only [map_mul, MulAut.conj_apply, inv_inv, v] using hh
  have hmem := H.mul_mem (H.mul_mem a.property (hvcentral hconj)) (H.inv_mem a.property)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
    mul_inv_cancel, mul_one] using hmem

theorem odd_subgroup_le_of_central_sylow_four_group
    (H : Subgroup G) (S : Sylow 2 G) (A X : Subgroup G)
    (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 4)
    (hcentral : A ≤ Subgroup.centralizer (S : Set G))
    (hnormalizes : A ≤ Subgroup.normalizer (X : Set G))
    (hXodd : Odd (Nat.card X))
    (htrap : ∀ a : G, orderOf a = 2 →
      (∀ s ∈ (S : Subgroup G), Commute a s) →
        Subgroup.centralizer ({a} : Set G) ≤ H) : X ≤ H := by
  rw [← elementary_abelian_centralizer_generation 2 1 Nat.prime_two A X hA
    (by simpa using hcard.ge) hnormalizes (Nat.coprime_two_left.mpr hXodd)]
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  have hUcard : Nat.card U = 2 := by simpa using hU.2
  obtain ⟨a, haorder⟩ := exists_prime_orderOf_dvd_card' (G := U) 2
    (by simp only [hUcard, dvd_refl])
  have haGorder : orderOf (a : G) = 2 := (Subgroup.orderOf_coe a).trans haorder
  have haA : (a : G) ∈ A := hU.1 a.property
  have hatrap := htrap a haGorder (fun s hs =>
    (show Commute (a : G) s from
      (Subgroup.mem_centralizer_iff.mp (hcentral haA) s hs).symm))
  exact (inf_le_right.trans (Subgroup.centralizer_le
    (Set.singleton_subset_iff.mpr a.property))).trans hatrap

end CFSG.ProperTwoGeneratedCore
