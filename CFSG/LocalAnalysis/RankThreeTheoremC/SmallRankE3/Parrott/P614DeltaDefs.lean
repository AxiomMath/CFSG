module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K278Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open scoped MatrixGroups

@[expose] def KFactL34DiagGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X) (Q : Sylow 3 X), N.Normal →
    Nonempty (↥N ≃* PSL(3, GaloisField 2 2)) → centralizer (N : Set X) = ⊥ →
    Nat.card (Q : Subgroup X) = 27 →
    ∀ z ∈ (Q : Subgroup X), orderOf z = 3 → (∀ q ∈ (Q : Subgroup X), q * z = z * q) →
      ∃ d ∈ (Q : Subgroup X), orderOf d = 3 ∧ d ∉ zpowers z ∧
        ∃ t ∈ N, t * d = d * t ∧ t * z * t⁻¹ = z⁻¹ ∧
        N ≤ (N ⊓ normalizer (((Q : Subgroup X) ⊓ N : Subgroup X) : Set X)) ⊔
          (N ⊓ centralizer ({d} : Set X))

@[expose] def PieceDeltaOmegaL34 : Prop :=
  KFact278L34 → KFactL34DiagGen → KFactProofs.T29.GL83I291Three →
    KFactProofs.T29.NoncyclicCentreRank → KFactThreeComponentsQRank →
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G)
    (H S : Subgroup G), Hyp P M x z H S → ¬ HasPrimeConstraint (G := M) 3 → OmegaLe x z H

theorem pieceDeltaOmega_of_l34 (h : PieceDeltaOmegaL34) (k278 : KFact278L34)
    (kL : KFactL34DiagGen) : PieceDeltaOmega :=
  fun _ _ _ kT29 kNC kQ G _ _ _ P M x z H S hyp hα =>
    h k278 kL kT29 kNC kQ G P M x z H S hyp hα

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
