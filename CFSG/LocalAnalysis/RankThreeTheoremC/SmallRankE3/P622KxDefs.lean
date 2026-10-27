module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

@[expose] def P622L613 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
    ∀ (p : ℕ), p ≠ 3 → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        ¬ CFSG.ABGLocalTools.IsPConstrained p ↥M →
        ∀ (H K : Subgroup G), H ≤ M ⊓ centralizer ({x} : Set G) → S622IsSimpleSection H K →
          p ∣ K.relIndex H → ∀ f : ℕ, f.Prime → f ≠ 2 → f ≠ p → f ∣ K.relIndex H →
            CFSG.Open.GLBStronglyEmbedded f M

structure P622KxCfg {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G)
    (x z : G) (T S L : Subgroup G) : Prop where
  setting : Setting G
  d1 : TheoremD1 G
  d2 : TheoremD2 G
  u0 : FullCoreLocal G
  conf : P622Conf p P M x z T S
  simple : S622IsSimpleSection L ⊥
  le_C : L ≤ centralizer ({x} : Set G)
  z_mem : z ∈ L
  rank : CFSG.Open.pRank p L ≤ 1
  not_le : ¬ L ≤ M
  normC : centralizer ({x} : Set G) ≤ normalizer (L : Set G)

namespace P622KxCfg

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S L : Subgroup G}

theorem norm (c : P622KxCfg p P M x z T S L) :
    M ⊓ centralizer ({x} : Set G) ≤ normalizer (L : Set G) :=
  inf_le_right.trans c.normC

end P622KxCfg

@[expose] def P622KxThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
    ∀ (P : Sylow 3 G) (M : Subgroup G) (x z : G) (T S : Subgroup G),
      Prop627Failure G 3 P M x z T → P622Prop614At M x z →
      IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G)) S →
      smallRankS x T ≤ S → rankThreePrimeCore 3 (centralizer ({x} : Set G)) = ⊥ →
      ∀ L : Subgroup G, S622IsSimpleSection L ⊥ → L ≤ centralizer ({x} : Set G) → z ∈ L →
        CFSG.Open.pRank 3 L ≤ 1 → ¬ L ≤ M →
        centralizer ({x} : Set G) ≤ normalizer (L : Set G) → False

@[expose] def P622KxLarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
    ∀ (p : ℕ), p ≠ 3 → ∀ (P : Sylow p G) (M : Subgroup G) (x z : G) (T S : Subgroup G),
      Prop627Failure G p P M x z T → P622Prop614At M x z →
      IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G)) S →
      smallRankS x T ≤ S → rankThreePrimeCore p (centralizer ({x} : Set G)) = ⊥ →
      ∀ L : Subgroup G, S622IsSimpleSection L ⊥ → L ≤ centralizer ({x} : Set G) → z ∈ L →
        CFSG.Open.pRank p L ≤ 1 → ¬ L ≤ M →
        centralizer ({x} : Set G) ≤ normalizer (L : Set G) → False

theorem p622Kx_of_three_large (h3 : P622KxThree) (hL : P622KxLarge) : P622Kx := by
  intro G _ _ hS hD1 hD2 hU0 p P M x z T S hf h614 hmax hle hbot L hL1 hLC hzL hrk hLM hN
  by_cases hp3 : p = 3
  · subst hp3
    exact h3 G hS hD1 hD2 hU0 P M x z T S hf h614 hmax hle hbot L hL1 hLC hzL hrk hLM hN
  · exact hL G hS hD1 hD2 hU0 p hp3 P M x z T S hf h614 hmax hle hbot L hL1 hLC hzL hrk hLM hN

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
