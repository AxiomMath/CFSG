module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall CatSLmEvenInner catSLmEvenInner)

@[expose] def CatSL2Bound (n : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → (∃ a b : J, a * b ≠ b * a) → Catalog J →
    ∀ τ : MulAut J, orderOf τ = 2 → ∀ D : Subgroup (fixedSubgroup τ), IsComponent D →
      LieModel (D ⧸ center D) .PSL 2 2 n → FixedCentralizerTwoSmall τ D →
      ∀ P : Subgroup (MulAut J), IsPGroup 2 P → Nat.card P < 2 * (2 ^ n) ^ 4

@[expose] def CatSL2Hyp (J : Type) [Group J] (τ : MulAut J) (n : ℕ) : Prop :=
  orderOf τ = 2 ∧ ∃ D : Subgroup (fixedSubgroup τ), IsComponent D ∧
    LieModel (D ⧸ center D) .PSL 2 2 n ∧ FixedCentralizerTwoSmall τ D

@[expose] def AutTwoBound (J : Type) [Group J] (n : ℕ) : Prop :=
  ∀ P : Subgroup (MulAut J), IsPGroup 2 P → Nat.card P < 2 * (2 ^ n) ^ 4

@[expose] def CatSL2AlternatingBound (n : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → (∃ a b : J, a * b ≠ b * a) →
    (∃ m : ℕ, 5 ≤ m ∧ Nonempty (J ≃* alternatingGroup (Fin m))) →
    ∀ τ : MulAut J, CatSL2Hyp J τ n → AutTwoBound J n

@[expose] def CatSL2EvenOuterBound (n : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → (∃ a b : J, a * b ≠ b * a) →
    EvenLieType J → ∀ τ : MulAut J, τ ∉ (MulAut.conj : J →* MulAut J).range →
      CatSL2Hyp J τ n → AutTwoBound J n

@[expose] def CatSL2EvenOuterList (n : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → (∃ a b : J, a * b ≠ b * a) →
    EvenLieType J → ∀ τ : MulAut J, τ ∉ (MulAut.conj : J →* MulAut J).range →
      CatSL2Hyp J τ n →
        LieModel J .PSL 2 2 (2 * n) ∨ LieModel J .PSU 3 2 n ∨ LieModel J .PSL 3 2 n

@[expose] def CatSL2OddLieBound (n : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → (∃ a b : J, a * b ≠ b * a) →
    OddLieType J → ∀ τ : MulAut J, CatSL2Hyp J τ n → AutTwoBound J n

@[expose] def CatSL2SporadicBound (n : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → (∃ a b : J, a * b ≠ b * a) →
    NativeSporadic.SporadicRep J → ∀ τ : MulAut J, CatSL2Hyp J τ n → AutTwoBound J n

theorem catSL2Bound_of_clauses
    {n : ℕ}
    (hA : CatSL2AlternatingBound n) (hEO : CatSL2EvenOuterBound n) (hO : CatSL2OddLieBound n)
    (hS : CatSL2SporadicBound n) : CatSL2Bound n := by
  intro J _ _ hJ hna hcat τ hτ D hD hDL h2 P hP
  have hyp : CatSL2Hyp J τ n := ⟨hτ, D, hD, hDL, h2⟩
  rcases (Milestones.ct_catalog_nonabelian_type_partition J hna).mp hcat with
    hAlt | hOdd | hEven | hSpor
  · exact hA J hJ hna hAlt τ hyp P hP
  · exact hO J hJ hna hOdd τ hyp P hP
  · by_cases hin : τ ∈ (MulAut.conj : J →* MulAut J).range
    · exact (catSLmEvenInner J hJ hna hEven τ hτ hin 2 n D hD hDL).elim
    · exact hEO J hJ hna hEven τ hin hyp P hP
  · exact hS J hJ hna hSpor τ hyp P hP

@[expose] def StarPrimeStatement (f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    LieModel L .PSU 3 2 f →
    (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    ∀ t : G, orderOf t = 2 → t ∈ centralizer (L : Set G) →
    ∀ w : G, orderOf w = 2 → w * t = t * w → w ∈ normalizer (L : Set G) →
      (¬ ∃ l ∈ L, ∀ x ∈ L, w * x * w⁻¹ = l * x * l⁻¹) →
      (∀ g ∈ centralizer ({w} : Set G), g * t * g⁻¹ ≠ t * w) →
      ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({w} : Set G) →
        Nat.card P < 4 * (2 ^ f) ^ 4

end CFSG.SeitzReduction.RankOne
