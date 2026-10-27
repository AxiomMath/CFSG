module

public import CFSG.GroupTheory.TitsSystem.Basic

public section

namespace CFSG.GroupTheory.TitsSystem

open CFSG.GH74.BNPair

variable {G : Type*} [Group G]

namespace IsBNPair

variable {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

theorem covBy_parabolic_singleton (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S) :
    B ⋖ parabolic B N {s} := by
  have hle : B ≤ parabolic B N {s} := h.le_parabolic (Set.singleton_subset_iff.2 hs)
  have hne : B ≠ parabolic B N {s} := by
    intro hEq
    have h' : ({s} : Set (WeylGroup B N)) = ∅ :=
      h.parabolic_injOn (Set.singleton_subset_iff.2 hs) (Set.empty_subset S)
        (hEq.symm.trans (parabolic_empty (B := B) (N := N)).symm)
    exact Set.singleton_ne_empty s h'
  refine covBy_of_eq_or_eq (lt_of_le_of_ne hle hne) ?_
  intro c hBc hcP
  obtain ⟨K, hK, hcK⟩ := h.exists_parabolic hBc
  have hKs : K ⊆ {s} := by
    rw [← h.parabolic_le_iff hK (Set.singleton_subset_iff.2 hs)]
    rwa [hcK] at hcP
  rcases Set.subset_singleton_iff_eq.1 hKs with rfl | rfl
  · left
    rw [hcK, parabolic_empty]
  · right
    rw [hcK]

theorem covBy_iff (h : IsBNPair B N S) {A : Subgroup G} :
    B ⋖ A ↔ ∃ s ∈ S, A = parabolic B N {s} := by
  constructor
  · intro hBA
    obtain ⟨J, hJ, hAJ⟩ := h.exists_parabolic hBA.le
    have hJne : J.Nonempty := by
      rcases J.eq_empty_or_nonempty with h0 | hne
      · rw [h0, parabolic_empty] at hAJ
        exact absurd hAJ.symm hBA.ne
      · exact hne
    obtain ⟨s, hsJ⟩ := hJne
    refine ⟨s, hJ hsJ, ?_⟩
    have hle : parabolic B N {s} ≤ A := by
      rw [hAJ]
      exact (h.parabolic_le_iff (Set.singleton_subset_iff.2 (hJ hsJ)) hJ).2
        (Set.singleton_subset_iff.2 hsJ)
    rcases hBA.eq_or_eq (h.le_parabolic (Set.singleton_subset_iff.2 (hJ hsJ))) hle with
      h1 | h1
    · exact absurd h1.symm (h.covBy_parabolic_singleton (hJ hsJ)).ne
    · exact h1.symm
  · rintro ⟨s, hs, rfl⟩
    exact h.covBy_parabolic_singleton hs

theorem parabolic_singleton_le_iff (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S)
    {J : Set (WeylGroup B N)} (hJ : J ⊆ S) :
    parabolic B N {s} ≤ parabolic B N J ↔ s ∈ J :=
  (h.parabolic_le_iff (Set.singleton_subset_iff.2 hs) hJ).trans Set.singleton_subset_iff

theorem parabolic_eq_sup_iSup (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S) :
    parabolic B N J = B ⊔ ⨆ s ∈ J, parabolic B N {s} := by
  refine le_antisymm ?_ (sup_le (h.le_parabolic hJ) ?_)
  · obtain ⟨K, hK, hRK⟩ := h.exists_parabolic le_sup_left
    have hJK : J ⊆ K := by
      intro s hs
      have hle : parabolic B N {s} ≤ B ⊔ ⨆ s ∈ J, parabolic B N {s} :=
        le_sup_of_le_right (le_iSup₂ (f := fun s (_ : s ∈ J) => parabolic B N {s}) s hs)
      rw [← h.parabolic_singleton_le_iff (hJ hs) hK, ← hRK]
      exact hle
    calc parabolic B N J ≤ parabolic B N K := (h.parabolic_le_iff hJ hK).2 hJK
      _ = B ⊔ ⨆ s ∈ J, parabolic B N {s} := hRK.symm
  · refine iSup₂_le fun s hs => ?_
    exact (h.parabolic_singleton_le_iff (hJ hs) hJ).2 hs

theorem le_sup_sSup_covBy (h : IsBNPair B N S) {Q : Subgroup G} (hBQ : B ≤ Q) :
    Q ≤ B ⊔ sSup {A | B ⋖ A ∧ A ≤ Q} := by
  obtain ⟨J, hJ, hQJ⟩ := h.exists_parabolic hBQ
  rw [hQJ, h.parabolic_eq_sup_iSup hJ]
  refine sup_le le_sup_left ?_
  refine iSup₂_le fun s hs => le_sup_of_le_right (le_sSup ⟨h.covBy_parabolic_singleton (hJ hs), ?_⟩)
  exact le_sup_of_le_right (le_iSup₂ (f := fun s (_ : s ∈ J) => parabolic B N {s}) s hs)

end IsBNPair

end CFSG.GroupTheory.TitsSystem
