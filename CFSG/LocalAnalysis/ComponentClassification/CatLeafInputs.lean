module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def GLS3OddLieAutComponentsInput : Prop :=
  ∀ (J : Type) [Group J] (τ : StatedLieTag) (n p f : ℕ), p.Prime → p ≠ 2 →
    StatedLieAdmissible τ n p f → Blueprint.LieModel J τ n p f →
    ∀ α : MulAut J, orderOf α = 2 → ∀ K : Subgroup (fixedSubgroup α), IsComponent K →
      (∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' p f' ∧
          Blueprint.LieModel (K ⧸ center K) τ' n' p f') ∨
        (p = 3 ∧ Blueprint.LieModel J .G2 0 3 1 ∧ α ∉ (MulAut.conj : J →* MulAut J).range ∧
          Blueprint.LieModel K .PSL 2 2 3)

@[expose] def lieOrderNumerator : StatedLieTag → ℕ → ℕ → ℕ
  | .PSL, n, q => q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1)
  | .PSU, n, q => q ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1)
  | .PSp, n, q => q ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)
  | .POmegaOdd, n, q => q ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)
  | .POmegaPlus, n, q => q ^ (n * (n - 1)) * (q ^ n - 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)
  | .POmegaMinus, n, q => q ^ (n * (n - 1)) * (q ^ n + 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)
  | .G2, _, q => q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)
  | .F4, _, q => q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
  | .E6, _, q => q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1)
  | .E7, _, q => q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
  | .E8, _, q => q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) *
      (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)
  | .twistedE6, _, q => q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1)
  | .trialityD4, _, q => q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
  | .twistedB2, _, q => q ^ 2 * (q ^ 2 + 1) * (q - 1)
  | .twistedG2, _, q => q ^ 3 * (q ^ 3 + 1) * (q - 1)
  | .twistedF4, _, q => q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)
  | .Tits, _, _ => 17971200

@[expose] def lieOrderDivisor : StatedLieTag → ℕ → ℕ → ℕ
  | .PSL, n, q => Nat.gcd n (q - 1)
  | .PSU, n, q => Nat.gcd n (q + 1)
  | .PSp, _, q => Nat.gcd 2 (q - 1)
  | .POmegaOdd, _, _ => 2
  | .POmegaPlus, n, q => Nat.gcd 4 (q ^ n - 1)
  | .POmegaMinus, n, q => Nat.gcd 4 (q ^ n + 1)
  | .E6, _, q => Nat.gcd 3 (q - 1)
  | .E7, _, q => Nat.gcd 2 (q - 1)
  | .twistedE6, _, q => Nat.gcd 3 (q + 1)
  | _, _, _ => 1

@[expose] def lieSylowExponent : StatedLieTag → ℕ → ℕ
  | .PSL, n => n * (n - 1) / 2
  | .PSU, n => n * (n - 1) / 2
  | .PSp, n => n ^ 2
  | .POmegaOdd, n => n ^ 2
  | .POmegaPlus, n => n * (n - 1)
  | .POmegaMinus, n => n * (n - 1)
  | .G2, _ => 6
  | .F4, _ => 24
  | .E6, _ => 36
  | .E7, _ => 63
  | .E8, _ => 120
  | .twistedE6, _ => 36
  | .trialityD4, _ => 12
  | .twistedB2, _ => 2
  | .twistedG2, _ => 3
  | .twistedF4, _ => 12
  | .Tits, _ => 11

@[expose] def LieOrderFormulasInput : Prop :=
  ∀ (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ), StatedLieAdmissible t n p f →
    Blueprint.LieModel X t n p f →
      Finite X ∧ Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) ∧
        (Nat.card X).factorization p = lieSylowExponent t n * f

@[expose] def EvenLieOuterTwoComponentsInput : Prop :=
  ∀ (K : Type) [Group K] (τ : StatedLieTag) (n f : ℕ), StatedLieAdmissible τ n 2 f →
    Blueprint.LieModel K τ n 2 f → ∀ α : MulAut K, orderOf α = 2 →
    α ∉ (MulAut.conj : K →* MulAut K).range →
    ∀ P : Subgroup (fixedSubgroup α), IsPComponent 2 P →
      (∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' 2 f' ∧
          Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f') ∨
        Nonempty (P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 6)) ∨
        Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSU 3 3 1

@[expose] def MonsterInnerInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    Nonempty (S ≃* Blueprint.NativeSporadic.M) → ∀ α : MulAut S, α ∈ OuterAutomorphisms.inner S

@[expose] def MonsterLocalComponentsInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    Nonempty (S ≃* Blueprint.NativeSporadic.M) → ∀ t : S, orderOf t = 2 →
    ∀ B : Subgroup (centralizer ({t} : Set S)), IsComponent B →
      2 ^ 41 ∣ Nat.card (B ⧸ center B) ∧ ¬ 2 ^ 42 ∣ Nat.card (B ⧸ center B)

end CFSG.ComponentClassification.CatLeaf
