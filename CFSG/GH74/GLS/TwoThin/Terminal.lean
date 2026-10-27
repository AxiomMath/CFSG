module

public import CFSG.GH74.GLS.TwoThin.Swap

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank

section

variable {G : Type} [Group G] [Finite G]

theorem exists_mu_max (hne : ∃ (x : G) (K : Subgroup G), IsB2Pair x K) :
    ∃ (x : G) (K : Subgroup G), IsB2Pair x K ∧ ∀ (x' : G) (K' : Subgroup G), IsB2Pair x' K' →
      hatCard K' < hatCard K ∨ (hatCard K' = hatCard K ∧ sylVal x' K' ≤ sylVal x K) := by
  have : Nonempty {p : G × Subgroup G // IsB2Pair p.1 p.2} := by
    obtain ⟨x, K, h⟩ := hne
    exact ⟨⟨(x, K), h⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_max (fun p : {p : G × Subgroup G // IsB2Pair p.1 p.2} =>
    toLex (hatCard p.1.2, sylVal p.1.1 p.1.2))
  refine ⟨p.1.1, p.1.2, p.2, fun x' K' h => ?_⟩
  have h1 := hp ⟨(x', K'), h⟩
  rw [Prod.Lex.le_iff] at h1
  exact h1

end

theorem terminalExists : TerminalExists := by
  intro G _ _ hR hC hne
  obtain ⟨x, K, hP, hmax⟩ := exists_mu_max hne
  obtain ⟨u, M, hPu, huM, hcard, hsyl⟩ := exists_dpair_mu_max hR hC hP hmax
  have hmax' : ∀ (x' : G) (K' : Subgroup G), IsB2Pair x' K' →
      hatCard K' < hatCard M ∨ (hatCard K' = hatCard M ∧ sylVal x' K' ≤ sylVal u M) := by
    intro x' K' h
    rw [hcard, hsyl]
    exact hmax x' K' h
  exact ⟨u, M, isTwoTerminal_of_mu_max hC hPu huM hmax', hPu.2⟩

end CFSG.GH74.GLS.TwoThin
