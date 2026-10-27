module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding
open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def AGL81SevenFourTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → CatalogSimpleSections X →
    primeComplementCore (G := X) p = ⊥ → ∀ P : Sylow p X, 3 ≤ Open.pRank p (P : Subgroup X) →
    ¬ IsCyclic ((P : Subgroup X) ⊓ CFSG.layer X : Subgroup X) →
    CFSG.layer X ⊔ GLBWeakCore p (P : Subgroup X) = ⊤

variable {G : Type} [Group G] [Finite G]

theorem _root_.CFSG.AGLEmbedding.D1Escape.hasPrimeConstraint_of_forall_component_le
    (h74 : AGL81SevenFourTwo) (hOut : KFactOutCyclic) (hK : Open.IsKProper G) {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G} (he : D1Escape p P M H R)
    (hle : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      L ≤ d1X0 p M H) :
    HasPrimeConstraint (G := H) p := by
  by_contra hcon
  obtain ⟨Rbar, -, hred, hX, -, -, -, -, K, hKc, -⟩ :=
    he.exists_reducedNongeneration_of_not_hasPrimeConstraint hK hcon
  by_cases hcyc : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))
  · obtain ⟨L, hL, hLX⟩ := hred.exists_not_le_of_caseTwo_of_aut
      (hred.cycAutRankLeTwo_of_kFactOutCyclic hX hOut) hcyc hKc
    exact hLX (hle L hL)
  push Not at hcyc
  obtain ⟨L, hL, hLnc⟩ := hcyc
  have hLE : L ≤ CFSG.layer (H ⧸ primeComplementCore (G := H) p) := by
    rw [CFSG.layer.eq_sSup]
    exact le_sSup ((CFSG.isComponent_iff_open L).mpr hL)
  have hnc : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      CFSG.layer (H ⧸ primeComplementCore (G := H) p) :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) := fun hc =>
    hLnc (Subgroup.isCyclic_of_le (inf_le_inf_left _ hLE))
  have hEX : CFSG.layer (H ⧸ primeComplementCore (G := H) p) ≤ d1X0 p M H := by
    rw [CFSG.layer.eq_sSup]
    exact sSup_le fun L' hL' => hle L' ((CFSG.isComponent_iff_open L').mp hL')
  have htop := h74 _ p hred.prime hred.ne_two hX hred.core_eq_bot Rbar hred.three_le_pRank hnc
  exact hred.ne_top (top_le_iff.mp (htop ▸ sup_le hEX hred.weakCore_le))

end CFSG.LocalAnalysis.RankThreeTheoremC
