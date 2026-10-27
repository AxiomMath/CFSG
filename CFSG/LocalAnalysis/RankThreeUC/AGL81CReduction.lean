module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
public import CFSG.LocalAnalysis.AGL81TheoremC.SigmaPrimes

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15
  CFSG.LocalAnalysis.AGL81TheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_QSet_iff {M : Subgroup G} {p : ℕ} {Q : Subgroup G} :
    Q ∈ QSet M p ↔ p.Prime ∧ p ≠ 2 ∧ Q ≤ M ∧ IsPGroup p Q ∧
      ((p ∈ sigmaM G M ∧ 2 < CFSG.Open.pRank p Q) ∨
        ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
          rankThreeGamma 1 p E ≤ M) :=
  Iff.rfl

theorem mem_HFam_iff {M Q H : Subgroup G} : H ∈ HFam M Q ↔ H ≠ ⊤ ∧ Q ≤ H ∧ ¬ H ≤ M :=
  Iff.rfl

theorem mem_H2Fam_iff {M Q H : Subgroup G} :
    H ∈ H2Fam M Q ↔ H ≠ ⊤ ∧ Q ≤ H ∧ ¬ H ≤ M ∧
      H ⊓ centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H :=
  Iff.rfl

theorem mem_H2StarFam_iff {M Q H : Subgroup G} :
    H ∈ H2StarFam M Q ↔ H ∈ H2Fam M Q ∧ ∀ H' ∈ H2Fam M Q, H ≤ H' → H' = H :=
  Iff.rfl

structure CStarSetting (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop where
  standing : Standing G
  uc : rankThreeUC G
  maxLocal : rankThreeIsMaxTwoLocal M
  witness : ∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
