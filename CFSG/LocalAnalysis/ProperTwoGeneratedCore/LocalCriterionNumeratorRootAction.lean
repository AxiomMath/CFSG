module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingConsequences
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem original_point_centralizer_preserves_distinguished_set
    (H : Subgroup G) (z u g x : G)
    (hg : g ∈ H ⊓ Subgroup.centralizer ({u} : Set G))
    (hx : x ∈ involutionPointClass z ∩
      (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G)) :
    rightConjugateElem x g ∈ involutionPointClass z ∩
      (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G) := by
  have hclass : rightConjugateElem x g ∈ involutionPointClass z := by
    obtain ⟨a, ha⟩ := hx.1.1
    change rightConjugateElem z a = x at ha
    refine ⟨a * g, ?_⟩
    change rightConjugateElem z (a * g) = rightConjugateElem x g
    rw [← rightConjugateElem_comp, ha]
  have hcentralizer : rightConjugateElem x g ∈
      Subgroup.centralizer ({u} : Set G) := by
    exact (Subgroup.centralizer ({u} : Set G)).mul_mem
      ((Subgroup.centralizer ({u} : Set G)).mul_mem
        ((Subgroup.centralizer ({u} : Set G)).inv_mem hg.2) hx.1.2) hg.2
  have hpoint : rightConjugateElem x g ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem hg.1) hx.2) hg.1
  exact ⟨⟨hclass, hcentralizer⟩, hpoint⟩

theorem original_point_centralizer_transitive_distinguished_set
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (_huz : Commute u z)
    (hP : fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u)))
    (x y : G)
    (hx : x ∈ involutionPointClass z ∩
      (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G))
    (hy : y ∈ involutionPointClass z ∩
      (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G)) :
    ∃ g : G, g ∈ H ⊓ Subgroup.centralizer ({u} : Set G) ∧
      rightConjugateElem x g = y := by
  let L := localInvolutionPointHull z u
  let P := H.subgroupOf L
  let xL : L := ⟨x, Subgroup.subset_closure hx.1⟩
  let yL : L := ⟨y, Subgroup.subset_closure hy.1⟩
  have hxorder : orderOf xL = 2 := (Subgroup.orderOf_coe xL).symm.trans
    (order_two_of_mem_pointClass h.distinguished_order hx.1.1)
  have hyorder : orderOf yL = 2 := (Subgroup.orderOf_coe yL).symm.trans
    (order_two_of_mem_pointClass h.distinguished_order hy.1.1)
  have hxI : IsInvolution xL :=
    ⟨(orderOf_eq_prime_iff.mp hxorder).2, (orderOf_eq_prime_iff.mp hxorder).1⟩
  have hyI : IsInvolution yL :=
    ⟨(orderOf_eq_prime_iff.mp hyorder).2, (orderOf_eq_prime_iff.mp hyorder).1⟩
  obtain ⟨g, hg, hgxy⟩ :=
    (native_strong_embedding_of_order_conditions hP).involutions_conjugate_in
      hx.2 hxI hy.2 hyI
  exact ⟨g, ⟨hg, localInvolutionPointHull_le_centralizer z u g.property⟩,
    congrArg Subtype.val hgxy⟩

omit [Finite G] in
theorem original_whole_point_root_normal_in_point_centralizer
    (H : Subgroup G) (z u : G) (A : Subgroup G)
    (hA : (A : Set G) = {1} ∪
      (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
        (H : Set G))) :
    A ≤ H ⊓ Subgroup.centralizer ({u} : Set G) ∧
      (A.subgroupOf (H ⊓ Subgroup.centralizer ({u} : Set G))).Normal := by
  let J := H ⊓ Subgroup.centralizer ({u} : Set G)
  have hAJ : A ≤ J := by
    intro x hx
    change x ∈ (A : Set G) at hx
    rw [hA] at hx
    rcases hx with hx | hx
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact J.one_mem
    · exact ⟨hx.2, hx.1.2⟩
  refine ⟨hAJ, (Subgroup.normal_subgroupOf_iff hAJ).mpr ?_⟩
  intro x g hx hg
  change x ∈ (A : Set G) at hx
  change g * x * g⁻¹ ∈ (A : Set G)
  rw [hA] at hx ⊢
  rcases hx with hx | hx
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact Or.inl (by simp)
  · right
    simpa only [rightConjugateElem, inv_inv] using
      original_point_centralizer_preserves_distinguished_set H z u g⁻¹ x
        (J.inv_mem hg) hx

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
