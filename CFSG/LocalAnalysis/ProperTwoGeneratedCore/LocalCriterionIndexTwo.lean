module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoConfinement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoCentralizers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCoreCover

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem local_point_mem_normal_index_two
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcentral : ∀ s ∈ (S : Subgroup G), Commute z s)
    (hodd : oddCore G = ⊥) (M : Subgroup G) [M.Normal]
    (hindex : M.index = 2) : z ∈ M := by
  by_contra hzM
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    exact point_centralizer_le h
      (Subgroup.mem_centralizer_singleton_iff.mpr (hzcentral s hs).symm)
  have hHeven : Even (Nat.card H) := even_iff_two_dvd.mpr
    (h.distinguished_order ▸ Subgroup.orderOf_dvd_natCard H h.distinguished_mem)
  have hNS := local_point_sylow_normalizer_le h S hzS hSH
  obtain ⟨u, huS, huorder, huescape⟩ :=
    sylow_involution_centralizer_escape_of_not_strongly_embedded H h.proper hHeven S hSH hNS
      (local_point_not_strongly_embedded_of_index_two h hodd M hindex hzM)
  obtain ⟨v, hvM, hvS, hvcentral, hvorder⟩ :=
    even_normal_subgroup_contains_central_sylow_involution S M
      (local_point_normal_index_two_even h hodd M hindex)
  have hvne : v ≠ z := fun heq => hzM (heq ▸ hvM)
  let A : Subgroup G := Subgroup.zpowers z ⊔ Subgroup.zpowers v
  obtain ⟨hA, hAcard, _⟩ := commuting_distinct_involutions_four_group
    h.distinguished_order hvorder (hzcentral v hvS) hvne
  have hAC : A ≤ Subgroup.centralizer (S : Set G) := by
    apply sup_le
    · apply Subgroup.zpowers_le.mpr
      exact Subgroup.mem_centralizer_iff.mpr (fun s hs => (hzcentral s hs).symm.eq)
    · apply Subgroup.zpowers_le.mpr
      exact Subgroup.mem_centralizer_iff.mpr (fun s hs => (hvcentral s hs).symm.eq)
  have hkernel := local_point_index_two_odd_kernel h M hindex hzM huorder
    (hzcentral u huS).symm huescape
  let X := localInvolutionPointHull z u ⊓ M
  have hXodd : Odd (Nat.card X) := hkernel.1
  have hXN : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    hkernel.2.2.1
  have hXnot : ¬ X ≤ H := hkernel.2.2.2.2.2
  have hAN : A ≤ Subgroup.normalizer (X : Set G) := by
    apply le_trans ?_ hXN
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hAC ha) u huS).symm
  apply hXnot
  exact odd_subgroup_le_of_central_sylow_four_group H S A X hA hAcard hAC hAN hXodd
    (fun a ha hacentral => local_point_central_sylow_involution_centralizer_le
      h S hzS hzcentral hodd M hindex hzM ha hacentral)

theorem involution_point_odd_core_free_index_two_obstruction
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hSylow : ∃ S : Sylow 2 G, ∃ hzS : z ∈ (S : Subgroup G),
      (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hodd : oddCore G = ⊥) :
    ∀ M : Subgroup G, M.Normal → M.index = 2 → z ∈ M := by
  obtain ⟨S, hzS, hzcenter⟩ := hSylow
  intro M hM hindex
  let : M.Normal := hM
  apply local_point_mem_normal_index_two h S hzS ?_ hodd M hindex
  intro s hs
  exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzcenter)
    (⟨s, hs⟩ : (S : Subgroup G)))).symm

end CFSG.ProperTwoGeneratedCore
