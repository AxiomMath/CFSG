module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorParameter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOddInvolutions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.BenderSuzuki.PFAppendixIII

universe u v

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem original_local_hull_center_le_point
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (huz : Commute u z) :
    Subgroup.center (localInvolutionPointHull z u) ≤
      H.subgroupOf (localInvolutionPointHull z u) := by
  let L := localInvolutionPointHull z u
  let zL : L := ⟨z, distinguished_mem_localInvolutionPointHull huz⟩
  intro c hc
  apply point_centralizer_le h
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc) zL)).symm

theorem original_point_parameter_of_central_odd_stabilizer_surjection
    {F : Type v} [Group F]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (huz : Commute u z)
    (hP : fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u)))
    (f : localInvolutionPointHull z u →* F) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker))
    (hcentral : f.ker ≤ Subgroup.center (localInvolutionPointHull z u))
    (B : Subgroup F)
    (hPB : (H.subgroupOf (localInvolutionPointHull z u)).map f = B)
    (q : ℕ) (hq : 1 ≤ q)
    (hcount : Nat.card {x : F // x ∈ B ∧ IsInvolution x} = q - 1) :
    q = Nat.card ↥(({1} : Set G) ∪
      (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
        (H : Set G))) := by
  classical
  let L := localInvolutionPointHull z u
  let P := H.subgroupOf L
  let S : Set G := involutionPointClass z ∩
    (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G)
  have hker : f.ker ≤ P := hcentral.trans (original_local_hull_center_le_point h u huz)
  have hPcomap : P = B.comap f := by
    rw [← hPB, Subgroup.comap_map_eq_self hker]
  have hS : Nat.card S = q - 1 := by
    rw [← original_point_involution_intersection_card h u huz hP]
    change Nat.card {x : L // x ∈ P ∧ IsInvolution x} = q - 1
    rw [hPcomap]
    exact (whole_involution_card_comap_of_central_odd_kernel f hf hodd hcentral B).trans hcount
  have hone : (1 : G) ∉ S := by
    intro h1
    have horder := order_two_of_mem_pointClass h.distinguished_order h1.1.1
    rw [orderOf_one] at horder
    omega
  have hcard : Nat.card ↥(({1} : Set G) ∪ S) = Nat.card S + 1 := by
    rw [Set.singleton_union, Nat.card_congr (Equiv.Set.insert hone), Nat.card_sum]
    rw [Nat.card_unique (α := PUnit.{u + 1})]
  rw [hcard, hS]
  omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
