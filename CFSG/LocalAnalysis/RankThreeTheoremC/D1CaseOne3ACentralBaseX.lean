module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111BaseIndexKappa
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KappaTop

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open Hyp111

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

section Residues

variable (G) in
@[expose] def D1SmallCentralBaseX : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmall3Data p P M H R Rbar K →
    ¬ (p = 3 ∧ (IsLinThreeFour K ∨ IsAltTwoP 3 K)) →
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) : Subgroup _) = p →
    D1KappaIH p M H → D1UniqueOver H R (nclIn H (d1LiftX p H R K)) →
    ∀ z : G, D1SmallCZElt p H R K z → (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M →
    IsAGLQ p M (d1LiftX p H R K) ∧ AGLRankTwoFactorAt p M H (d1LiftX p H R K) K ∧
      ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ (L.subgroupOf M).Normal ∧
        ∀ b ∈ d1LiftX p H R K, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M

end Residues

end CFSG.LocalAnalysis.RankThreeTheoremC
