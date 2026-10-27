module

public import CFSG.GH74.Generic.S3.LyB2TermS

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem exists_mu_maxC (Cls : G → Subgroup G → Prop)
    (hne : ∃ (x : G) (K : Subgroup G), IsB2Pair x K ∧ Cls x K) :
    ∃ (x : G) (K : Subgroup G), IsB2Pair x K ∧ Cls x K ∧
      ∀ (x' : G) (K' : Subgroup G), IsB2Pair x' K' → Cls x' K' →
        hatCard K' < hatCard K ∨ (hatCard K' = hatCard K ∧ sylVal x' K' ≤ sylVal x K) := by
  have : Nonempty {p : G × Subgroup G // IsB2Pair p.1 p.2 ∧ Cls p.1 p.2} := by
    obtain ⟨x, K, h⟩ := hne
    exact ⟨⟨(x, K), h⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_max
    (fun p : {p : G × Subgroup G // IsB2Pair p.1 p.2 ∧ Cls p.1 p.2} =>
      toLex (hatCard p.1.2, sylVal p.1.1 p.1.2))
  refine ⟨p.1.1, p.1.2, p.2.1, p.2.2, fun x' K' h hc => ?_⟩
  have h1 := hp ⟨(x', K'), h, hc⟩
  rw [Prod.Lex.le_iff] at h1
  exact h1

theorem terminalExistsC (Cls : G → Subgroup G → Prop)
    (hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    (hC : ClsClosed Cls) (hne : ∃ (x : G) (K : Subgroup G), IsB2Pair x K ∧ Cls x K) :
    ∃ (x : G) (K : Subgroup G), IsTwoTerminal x K ∧ InB2 (↥K ⧸ pPrimeCore 2 ↥K) := by
  obtain ⟨x, K, hP, hcls, hmax⟩ := exists_mu_maxC Cls hne
  obtain ⟨u, M, hPu, hclsu, huM, hcard, hsyl⟩ := exists_dpair_mu_maxC Cls hR hC hP hcls hmax
  have hmax' : ∀ (x' : G) (K' : Subgroup G), IsB2Pair x' K' → Cls x' K' →
      hatCard K' < hatCard M ∨ (hatCard K' = hatCard M ∧ sylVal x' K' ≤ sylVal u M) := by
    intro x' K' h hc
    rw [hcard, hsyl]
    exact hmax x' K' h hc
  exact ⟨u, M, isTwoTerminal_of_mu_maxC Cls hC hPu hclsu huM hmax', hPu.2⟩

theorem hasTwoThinConfiguration_of_cls (Cls : G → Subgroup G → Prop)
    (hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    (hC : ClsClosed Cls) (hne : ∃ (x : G) (K : Subgroup G), IsB2Pair x K ∧ Cls x K) :
    CFSG.GH74.GLS.HasTwoThinConfiguration G :=
  terminalExistsC Cls hR hC hne

end CFSG.GH74.GLS.TwoThin
