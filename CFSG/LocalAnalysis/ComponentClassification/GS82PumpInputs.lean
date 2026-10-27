module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def ChevOddPumpLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.Catalog S → ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    ∀ r : ℕ, r.Prime → r ≠ 2 →
    HarrisLit.IsSimpleChevalleyOver r (↥P ⧸ Open.fusionZStar ↥P) →
    ¬ GH74.GLS.InChev2 (↥P ⧸ Open.fusionZStar ↥P) →
      (HarrisLit.IsSimpleChevalleyOver r S ∧ ¬ GH74.GLS.InChev2 S) ∨
        (Blueprint.NativeSporadic.IsSporadic S .J3 ∧
          Blueprint.LieModel (↥P ⧸ Open.fusionZStar ↥P) .PSL 2 17 1)

@[expose] def ChevOddCentralPumpInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      HarrisLit.IsSimpleChevalleyOver r (↥T ⧸ Open.fusionZStar ↥T) →
      ¬ GH74.GLS.InChev2 (↥T ⧸ Open.fusionZStar ↥T) →
    ∀ w : H, orderOf w = 2 → w ∈ T → w ∈ (Open.fusionZStar ↥M).map M.subtype →
      HarrisLit.IsSimpleChevalleyOver r (↥M ⧸ Open.fusionZStar ↥M) ∧
        ¬ GH74.GLS.InChev2 (↥M ⧸ Open.fusionZStar ↥M)

@[expose] def KGSLTwoInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ B : Subgroup H, IsPGroup 2 B → B ≤ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M ⊓ centralizer (B : Set H) →
      IsPComponent 2 (T.subgroupOf (M ⊓ centralizer (B : Set H))) →
    ∀ r e : ℕ, r.Prime → r ≠ 2 → 1 ≤ e → r ^ e ∉ ({3, 5, 7, 9} : Finset ℕ) →
      HarrisLit.IsSLTwoOver (r ^ e) (↥T ⧸ pPrimeCore 2 ↥T) →
        HarrisLit.IsSimpleChevalleyOver r (↥M ⧸ Open.fusionZStar ↥M) ∧
          ¬ GH74.GLS.InChev2 (↥M ⧸ Open.fusionZStar ↥M)

@[expose] def MTypeOfSLTwoSection : Prop :=
  ∀ (J : Type) [Group J] [Finite J], HarrisLit.IsTwoQuasisimple J →
    ∀ p : ℕ, p.Prime → p ≠ 2 → HarrisLit.IsSimpleChevalleyOver p (J ⧸ Open.fusionZStar J) →
    ∀ (N : Subgroup J) (q₀ : ℕ), Odd q₀ → 5 ≤ q₀ →
      HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N) →
    ∀ c : J, orderOf c = 2 → c ∈ N → c ∈ Open.fusionZStar J →
      HarrisLit.IsMTypeSchur p J

@[expose] def AltCentralPumpInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
    ∀ n : ℕ, 7 ≤ n → GH74.GLS.IsDoubleCoverOfAlt (↥T ⧸ pPrimeCore 2 ↥T) n →
    ∀ w : H, orderOf w = 2 → w ∈ T → w ∈ (Open.fusionZStar ↥M).map M.subtype →
      ∃ m : ℕ, n ≤ m ∧ GH74.GLS.IsDoubleCoverOfAlt (↥M ⧸ pPrimeCore 2 ↥M) m

@[expose] def SLTwoCentralPumpInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
    ∀ q₀ q₁ : ℕ, Odd q₀ → 5 ≤ q₀ → Odd q₁ → q₀ ≤ q₁ →
      HarrisLit.IsSLTwoOver q₁ (↥T ⧸ pPrimeCore 2 ↥T) →
    ∀ w : H, orderOf w = 2 → w ∈ T → w ∈ (Open.fusionZStar ↥M).map M.subtype →
      (∃ q₂ : ℕ, Odd q₂ ∧ q₀ ≤ q₂ ∧ HarrisLit.IsSLTwoOver q₂ (↥M ⧸ pPrimeCore 2 ↥M)) ∨
        Blueprint.OddLieType (↥M ⧸ Open.fusionZStar ↥M) ∨
        (∃ n : ℕ, 7 ≤ n ∧ GH74.GLS.IsDoubleCoverOfAlt (↥M ⧸ pPrimeCore 2 ↥M) n) ∨
        (GH74.GLS.IsL34Quotient (↥M ⧸ pPrimeCore 2 ↥M) ∧
          Monoid.exponent ↥(center (↥M ⧸ pPrimeCore 2 ↥M)) = 4)

@[expose] def SpFourThreeCentralPumpInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
      Blueprint.LieModel (↥T ⧸ Open.fusionZStar ↥T) .PSp 2 3 1 →
    ∀ w : H, orderOf w = 2 → w ∈ T → w ∈ (Open.fusionZStar ↥M).map M.subtype →
      HarrisLit.IsSimpleChevalleyOver 3 (↥M ⧸ Open.fusionZStar ↥M)

@[expose] def L34ExpFourPumpInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
      GH74.GLS.IsL34Quotient (↥T ⧸ pPrimeCore 2 ↥T) →
      ¬ IsElementaryAbelian 2 ↥(center (↥T ⧸ pPrimeCore 2 ↥T)) →
        Blueprint.LieModel (↥M ⧸ Open.fusionZStar ↥M) .PSL 3 2 2 ∨
          (Blueprint.NativeSporadic.IsSporadic (↥M ⧸ Open.fusionZStar ↥M) .ONan ∧
            IsCyclic ↥(center (↥T ⧸ pPrimeCore 2 ↥T)) ∧
            Nat.card ↥(center (↥T ⧸ pPrimeCore 2 ↥T)) = 4)

@[expose] def KGSLTwoSmallInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ B : Subgroup H, IsPGroup 2 B → B ≤ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M ⊓ centralizer (B : Set H) →
      IsPComponent 2 (T.subgroupOf (M ⊓ centralizer (B : Set H))) →
    ∀ q₀ : ℕ, q₀ ∈ ({5, 7, 9} : Finset ℕ) →
      HarrisLit.IsSLTwoOver q₀ (↥T ⧸ pPrimeCore 2 ↥T) →
    ∀ w : H, orderOf w = 2 → w ∈ T → w ∈ (Open.fusionZStar ↥M).map M.subtype →
      (∃ q₂ : ℕ, Odd q₂ ∧ q₀ ≤ q₂ ∧ HarrisLit.IsSLTwoOver q₂ (↥M ⧸ pPrimeCore 2 ↥M)) ∨
        Blueprint.OddLieType (↥M ⧸ Open.fusionZStar ↥M) ∨
        (∃ n : ℕ, 7 ≤ n ∧ GH74.GLS.IsDoubleCoverOfAlt (↥M ⧸ pPrimeCore 2 ↥M) n) ∨
        (GH74.GLS.IsL34Quotient (↥M ⧸ pPrimeCore 2 ↥M) ∧
          Monoid.exponent ↥(center (↥M ⧸ pPrimeCore 2 ↥M)) = 4)

@[expose] def L34CentralSLTwoFact : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsQuasisimple H → IsPGroup 2 ↥(center H) →
    Blueprint.LieModel (H ⧸ center H) .PSL 3 2 2 →
    ∀ σ : MulAut H, (∀ y, σ (σ y) = y) → σ ≠ 1 →
    ∀ N : Subgroup H, N ≤ fixedSubgroup σ →
    ∀ q₀ : ℕ, q₀ ∈ ({5, 7, 9} : Finset ℕ) → HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N) →
    ∀ c : H, orderOf c = 2 → c ∈ N → c ∈ center H →
      q₀ = 7 ∧ Nat.card ↥(center H) = 16

end CFSG.ComponentClassification.GS82PumpInputs
