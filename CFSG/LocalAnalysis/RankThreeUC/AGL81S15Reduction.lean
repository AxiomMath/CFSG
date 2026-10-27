module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Witness
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Transfer
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual7

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def NoU4All (G : Type) [Group G] [Finite G] (_p : ℕ) (M : Subgroup G) : Prop :=
  ∀ q ∈ rankThreeSigmaA G, 2 ≤ CFSG.Open.pRank q M → ¬ U4Shape q M

theorem agl81Residual7NoU4_of_core (hS : Standing G) (h16 : AGL81Residual7U4 G)
    (hcore : AGL81Residual7With G (NoU4All G)) : AGL81Residual7NoU4 G := by
  intro hUC p hp P M hw hshape T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10
  by_contra hN
  by_cases hmix : ∃ q ∈ rankThreeSigmaA G, 2 ≤ CFSG.Open.pRank q M ∧ U4Shape q M
  · obtain ⟨q, hq, hq2, hshq⟩ := hmix
    have hns : ¬ Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T)) := fun hs =>
      hcon (CFSG.ABGLocalTools.isPConstrained_of_isSolvable hs)
    have hMns : ¬ Group.IsSolvable ↥M :=
      not_isSolvable_of_not_isSolvable_autOn (le_normalizer_uCore M T) hns
    obtain ⟨Q, hwq⟩ := exists_isWitness_of_two_le_pRank hS hUC hq hw.maxLocal hMns hq2
    obtain ⟨hH4, hH7, hH8, hH9, hH10⟩ := transfer_residual_hyps hS hq hwq hT H2 hns hN
    exact hN (h16 hUC q hq Q M hwq hshq T hT H1 H2 H3 hH4 hcon H6 hH7 hH8 hH9 hH10)
  · push Not at hmix
    exact hN (hcore hUC p hp P M hw (fun q hq h2 => hmix q hq h2) T hT H1 H2 H3 H4 hcon H6 H7 H8
      H9 H10)

end CFSG.LocalAnalysis.RankThreeUC.S15
