module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Lin2Final

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup

namespace C56

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem c61_single
    (hc : ∀ M₀ : Subgroup G, S ≤ M₀ → M₀ ≤ T → S.relIndex M₀ = 2 → C56_7Concl S H L M₀)
    (hT : C61SingleTail) (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) (h5 : ¬ IsAltType L 5) :
    C61Concl T H S L := by
  obtain ⟨M₀, hSM, hMT, h2⟩ := exists_index_two hcs
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  obtain ⟨c1, -, c3, c4, -, c6, hx⟩ := hc M₀ hSM hMT h2
  have hL' : IsAltType L 3 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n := hL.symm
  have hNT : normT T S = M₀ :=
    normT_eq hcs hSM hMT h2 hx₀ ((hx x₀ hx₀ hx₀S).2.2.1 hj hL')
  obtain ⟨hT3, hT6⟩ := hT G T M H S L hcs hj hL h5
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, hT6⟩
  · rw [hNT]
    exact h2
  · intro x hxN hxS
    rw [hNT] at hxN
    obtain ⟨-, c8, -⟩ := hx x hxN hxS
    exact ⟨c6.symm, baum_eq_sup_conj (normalizer_of_relIndex_two hSM h2 hxN) c4 c8⟩
  · intro _ _
    refine ⟨fun x hxN hxS => ?_, hT3⟩
    rw [hNT] at hxN
    exact (hx x hxN hxS).2.2.1 hj hL'
  · intro h
    rcases h with ⟨h5', -⟩ | ⟨-, hne'⟩
    · exact absurd h5' h5
    · exact absurd hj hne'
  · rw [c4, c3, ← c1]

theorem c56_7_lin2
    (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type L n) (h5 : ¬ IsAltType L 5) {M₀ : Subgroup G} (hSM : S ≤ M₀)
    (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) : C56_7Concl S H L M₀ :=
  c56_7_single naturalModuleStructure hcs hj (Or.inl ⟨n, hn, hlin⟩) h5 hSM hMT h2

theorem c61_lin2
    (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type L n) (h5 : ¬ IsAltType L 5) : C61Concl T H S L :=
  c61_single (fun _ hSM hMT h2 => c56_7_lin2 hcs hj hn hlin h5 hSM hMT h2)
    (c61SingleTail naturalModuleStructure (c61SingleAlternatives c61Lin2Alternatives))
    hcs hj (Or.inl ⟨n, hn, hlin⟩) h5

end C56

theorem lemma245_3
    (h567 : Lemma245_C56_7) (hO : C61OtherCases) : Lemma245_3 := by
  rw [lemma245_3_iff]
  intro G _ _ T M H S L hcs hhyp
  by_cases hs : conjJoin S L = L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) ∧
      ¬ IsAltType L 5
  · exact C56.c61_single
      (fun M₀ hSM hMT h2 => lemma245_C56_7_iff.1 h567 G T M H S L hcs M₀ hSM hMT h2)
      (C56.c61SingleTail naturalModuleStructure (c61SingleAlternatives c61Lin2Alternatives)) hcs
      hs.1 hs.2.1 hs.2.2
  · exact hO G T M H S L hcs hhyp hs

end CFSG.QuasithinUnique
