module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111OneSmallKappa
import CFSG.ClassicalInvolution.PerfectCase.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def D1KappaIH (p : ℕ) (M H : Subgroup G) : Prop :=
  ∀ (P' : Sylow p G) (M' N R' : Subgroup G), D1Extremal p P' M' N R' →
    d1Kappa p M H < d1Kappa p M' N → False

theorem false_of_d1At3_of_extremal {q : ℕ} {Q : Sylow q G} {M H R : Subgroup G}
    (hD : D1At3 G q) (hM : IsCoreMaxLocal q Q M) (hext : D1Extremal q Q M H R) : False := by
  have esc := hext.toD1Escape
  have hRHM : R ≤ H ⊓ M := le_inf esc.le_H (esc.le_P.trans esc.sylow_le)
  exact esc.not_le (hD Q M hM H esc.maxTwoLocal_H.1
    (esc.three_le_pRank.trans (CFSG.SectionRank.pRank_mono esc.prime.one_lt hRHM)))

theorem not_isComponentOf_of_hasPrimeConstraint {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hc : HasPrimeConstraint (G := H) p)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤) : False := by
  obtain ⟨N, hN, hNp, hC⟩ := hc
  have : Group.IsNilpotent N := hNp.isNilpotent
  have hcomm := CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal L N
    hL (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hN.isSubnormal)
  have hLN : L ≤ N := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hC
  have hLp : IsPGroup p L := hNp.to_le hLN
  have : Group.IsNilpotent L := hLp.isNilpotent
  exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hL.2.2 inferInstance

theorem d1Kappa_eq_one_of_hasPrimeConstraint {p : ℕ} [Fact p.Prime] {M H : Subgroup G}
    (hc : HasPrimeConstraint (G := H) p) : d1Kappa p M H = 1 := by
  have hbot : d1KBar p M H = ⊥ :=
    le_bot_iff.mp (iSup₂_le fun L hL => (not_isComponentOf_of_hasPrimeConstraint hc hL.1).elim)
  simp only [d1Kappa, hbot, Subgroup.card_bot]

theorem one_le_d1Kappa (p : ℕ) (M H : Subgroup G) : 1 ≤ d1Kappa p M H :=
  Nat.card_pos

end CFSG.LocalAnalysis.RankThreeTheoremC
