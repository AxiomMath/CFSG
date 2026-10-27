module

public import CFSG.Sporadic.SchreierLemmas.MoorePresentation

public section

namespace CFSG.GH74.GLS.Layer3

open CFSG.Sporadic.SchreierLemmas

theorem exists_subgroup_alt_of_moore {n : ℕ} (hn : 5 ≤ n) {G : Type*} [Group G] (x : ℕ → G)
    (hx : IsMooreFamily (n - 2) x) (hne : ∃ i ∈ Set.Icc 1 (n - 2), x i ≠ 1) :
    ∃ G₀ : Subgroup G, Nonempty (G₀ ≃* alternatingGroup (Fin n)) := by
  obtain ⟨e⟩ := (moore_alternating_presentation (by omega) x hx).2.2.2.2.2 hn hne |>.2
  exact ⟨Subgroup.closure (x '' Set.Icc 1 (n - 2)), ⟨e.symm⟩⟩

end CFSG.GH74.GLS.Layer3
