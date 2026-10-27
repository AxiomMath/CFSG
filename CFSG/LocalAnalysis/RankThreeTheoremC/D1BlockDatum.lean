module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111BaseIndexKappa
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BNotQDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KappaTop

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open Hyp111 CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

@[expose] def IsAGLBlockDatum (M H B L : Subgroup G) : Prop :=
  (∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) ∨
    ∃ J₀ N₀ : Subgroup G, J₀ ≤ L ∧ N₀ ≤ L ∧ IsPGroup 2 N₀ ∧
      H ⊓ M ≤ Subgroup.normalizer (J₀ : Set G) ∧ H ⊓ M ≤ Subgroup.normalizer (N₀ : Set G) ∧
      J₀ ≤ Subgroup.normalizer (N₀ : Set G) ∧
      (∀ b ∈ B, ∀ x ∈ J₀, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 J₀) ∧ ¬ 2 ∣ (J₀ ⊔ N₀).relIndex L

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} {z : H}
  {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} {E : Subgroup G}

variable (G) in
@[expose] def InnerNotQBlockJ : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) (z : H)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G),
    InnerNotQConfig p P M H R Rbar z L E →
    ∃ E' : Subgroup G, IsFieldOmegaA p M H R L E' ∧ rankThreeGamma 1 p E' ≤ M ∧
      ∃ Lm : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) Lm ∧ (Lm.subgroupOf M).Normal ∧
        IsAGLBlockDatum M H (innerNotQBaseA p H R L E') Lm

section OneSmall

variable {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

variable (G) in
@[expose] def D1SmallCentralBaseXJ : Prop :=
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
        IsAGLBlockDatum M H (d1LiftX p H R K) L

end OneSmall

end CFSG.LocalAnalysis.RankThreeTheoremC
