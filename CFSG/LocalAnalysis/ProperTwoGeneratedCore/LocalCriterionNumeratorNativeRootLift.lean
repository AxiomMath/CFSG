module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorOriginalRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorRootAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeRecognition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeRoot

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

@[expose] def originalPointRoot (H : Subgroup G) (z u : G) : Subgroup G :=
  Subgroup.closure (involutionPointClass z ∩
    (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G))

theorem originalPointRoot_eq_of_whole_set (H : Subgroup G) (z u : G)
    (A : Subgroup G)
    (hAset : (A : Set G) = {1} ∪
      (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
        (H : Set G))) : originalPointRoot H z u = A := by
  apply le_antisymm
  · apply (Subgroup.closure_le A).mpr
    intro x hx
    exact hAset.symm ▸ (show x ∈ {1} ∪
      (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
        (H : Set G)) from Or.inr hx)
  · intro x hx
    have hxset : x ∈ (A : Set G) := hx
    rw [hAset] at hxset
    rcases hxset with hxone | hxclass
    · obtain rfl := Set.mem_singleton_iff.mp hxone
      exact (originalPointRoot H z u).one_mem
    · exact Subgroup.subset_closure hxclass

variable [Finite G]

theorem original_native_whole_point_root_of_central_oddCore
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hcentral : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    let F := L ⧸ CFSG.oddCore L
    let B := (H.subgroupOf L).map (QuotientGroup.mk' (CFSG.oddCore L))
    let A := originalPointRoot H z u
    ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
      IsSimpleBenderGroupAtExponent a F ∧
      IsElementaryAbelian 2 A ∧ A ≤ H ⊓ L ∧
      (A : Set G) = {1} ∪
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
          (H : Set G)) ∧
      Nat.card A = 2 ^ a ∧ 4 ≤ Nat.card A ∧ B.index = (2 ^ a) ^ i + 1 ∧
      A ≤ H ⊓ Subgroup.centralizer ({u} : Set G) ∧
      (A.subgroupOf (H ⊓ Subgroup.centralizer ({u} : Set G))).Normal ∧
      (∀ (x y : G), x ∈ A → x ≠ 1 → y ∈ A → y ≠ 1 →
        ∃ g : G, g ∈ H ⊓ Subgroup.centralizer ({u} : Set G) ∧
          rightConjugateElem x g = y) := by
  let L := localInvolutionPointHull z u
  let F := L ⧸ CFSG.oddCore L
  let f := QuotientGroup.mk' (CFSG.oddCore L)
  let B := (H.subgroupOf L).map f
  let U := Subgroup.closure {x : F | x ∈ B ∧ IsInvolution x}
  have hP := h.local_embedding u hu huz hescape
  obtain ⟨hmodel, _hcore, hB⟩ :=
    original_local_hull_native_model_and_borel h u hu huz hescape hrank
  obtain ⟨a, ha, hmodelAt⟩ := hmodel.exists_exponent
  obtain ⟨i, hi, helem, _hUB, hUset, hUcard, hfour, hindex⟩ :=
    native_borel_whole_elementary_root_at_exponent a ha hmodelAt hmodel B hB
  have hodd : Odd (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card L
  have hkercentral : f.ker ≤ Subgroup.center L := by
    rw [QuotientGroup.ker_mk']
    exact hcentral
  obtain ⟨A, hAelem, hAle, hAset, hAcard⟩ :=
    original_whole_point_root_of_central_odd_surjection h u huz hP f
      (QuotientGroup.mk'_surjective (CFSG.oddCore L)) hodd hkercentral B U rfl helem hUset
  have hroot := originalPointRoot_eq_of_whole_set H z u A hAset
  have hnormal := original_whole_point_root_normal_in_point_centralizer H z u A hAset
  have htrans : ∀ (x y : G), x ∈ A → x ≠ 1 → y ∈ A → y ≠ 1 →
      ∃ g : G, g ∈ H ⊓ Subgroup.centralizer ({u} : Set G) ∧
        rightConjugateElem x g = y := by
    intro x y hx hxone hy hyone
    have hxset : x ∈ {1} ∪
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
          (H : Set G)) := hAset ▸ hx
    have hyset : y ∈ {1} ∪
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
          (H : Set G)) := hAset ▸ hy
    exact original_point_centralizer_transitive_distinguished_set h u huz hP x y
      (hxset.resolve_left (fun h => hxone (Set.mem_singleton_iff.mp h)))
      (hyset.resolve_left (fun h => hyone (Set.mem_singleton_iff.mp h)))
  dsimp only
  rw [hroot]
  exact ⟨a, i, ha, hi, hmodelAt, hAelem, hAle, hAset, hAcard.trans hUcard,
    hAcard.symm ▸ hfour, hindex, hnormal.1, hnormal.2, htrans⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
