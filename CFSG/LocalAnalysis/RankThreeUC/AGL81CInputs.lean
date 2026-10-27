module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15

abbrev NineSevenTwoInputConclusion (G : Type) [Group G] [Finite G]
    (M Q H E : Subgroup G) : Prop :=
  pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H →
  ∃ L : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H), CFSG.IsComponent L ∧ ¬ L ≤ barInf 3 M H ∧
    (IsL34Type ↥L ∨ IsA11Type ↥L)

@[expose] def NineSevenTwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G),
    NineSetting G M 3 Q H E 2 → H ∈ H2Fam M Q → 3 ∉ sigmaM G M →
    NineSevenTwoInputConclusion G M Q H E

@[expose] def NineSevenTwoInputGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G),
    NineSettingGen G M 3 Q H E 2 → H ∈ H2Fam M Q → 3 ∉ sigmaM G M →
    NineSevenTwoInputConclusion G M Q H E

abbrev NineSixInputConclusion (G : Type) [Group G] [Finite G]
    (M Q H E : Subgroup G) : Prop :=
  (∃ L : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H), CFSG.IsComponent L ∧ ¬ L ≤ barInf 3 M H ∧
    (IsL34Type ↥L ∨ IsA11Type ↥L)) →
  {C : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H) |
      CFSG.IsComponent C ∧ ¬ C ≤ barInf 3 M H}.ncard ≤ 2 ∧
    ∀ C₁ C₂ : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H), CFSG.IsComponent C₁ → ¬ C₁ ≤ barInf 3 M H →
      CFSG.IsComponent C₂ → ¬ C₂ ≤ barInf 3 M H → C₁ ≠ C₂ →
        (IsL34Type ↥C₁ ∨ IsA6Type ↥C₁) ∧ (IsL34Type ↥C₂ ∨ IsA6Type ↥C₂)

@[expose] def NineSixInputGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G),
    NineSettingGen G M 3 Q H E 2 → H ∈ H2Fam M Q → 3 ∉ sigmaM G M →
    NineSixInputConclusion G M Q H E

abbrev ThreeFiveA11InputConclusion (G : Type) [Group G] [Finite G]
    (M Q H E : Subgroup G) : Prop :=
  (∃ L : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H), CFSG.IsComponent L ∧ ¬ L ≤ barInf 3 M H ∧
    IsA11Type ↥L) → 5 ∣ Nat.card (barInf 3 M H)

@[expose] def ThreeFiveA11InputGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G),
    NineSettingGen G M 3 Q H E 2 → H ∈ H2Fam M Q → 3 ∉ sigmaM G M →
    ThreeFiveA11InputConclusion G M Q H E

@[expose] def KFactAutL34 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, (∃ Q : TauCeti.PrimePower, Q.card = 4 ∧ d.1 = .A 2 Q) →
    Nat.card (MulAut (TauCeti.CFSGIndex.lie d).Group) ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7

@[expose] def KFactCardL34 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, (∃ Q : TauCeti.PrimePower, Q.card = 4 ∧ d.1 = .A 2 Q) →
    Nat.card (TauCeti.CFSGIndex.lie d).Group = 20160

@[expose] def KFactAutA11 : Prop :=
  Nat.card (MulAut (alternatingGroup (Fin 11))) ∣ Nat.factorial 11

@[expose] def KFactAutA6 : Prop :=
  Nat.card (MulAut (alternatingGroup (Fin 6))) ∣ 1440

@[expose] def KFactThreeRankL34 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → IsL34Type L →
    2 ≤ pRank 3 (⊤ : Subgroup L)

@[expose] def KFactThreeRankA11 : Prop :=
  2 ≤ pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 11)))

@[expose] def KFactOmegaNotCentral : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ C : Subgroup X, CFSG.IsComponent C →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card C →
      ∃ e ∈ C, orderOf e = p ∧ ∃ c ∈ C, e * c ≠ c * e

@[expose] def KFactNormalComplement : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ J : Subgroup X, CFSG.IsComponent J →
    J.Normal → ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card J →
      ∃ (N : Subgroup X) (_ : N.Normal), J ⊔ Subgroup.centralizer (J : Set X) ≤ N ∧
        ¬ q ∣ (J ⊔ Subgroup.centralizer (J : Set X)).relIndex N ∧ IsPGroup q (X ⧸ N)

structure ZKFacts : Prop where
  autL34 : KFactAutL34
  cardL34 : KFactCardL34
  autA11 : KFactAutA11
  autA6 : KFactAutA6
  rankL34 : KFactThreeRankL34
  rankA11 : KFactThreeRankA11
  omegaNotCentral : KFactOmegaNotCentral
  normalComplement : KFactNormalComplement

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
