module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcChev
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangChev
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTriD4Conj
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangSz
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangReeF4
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Model

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.YS09Field
open CFSG.LocalAnalysis.GLTheoremA

abbrev FixGapG2 : Prop :=
  ∀ (n p : ℕ) (K : Type) [Field K] [Finite K], 2 ≤ n → Nat.card K = 2 ^ n → p.Prime → p ≠ 2 →
    ∀ f ∈ LargeEvenChevFieldImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K false),
      orderOf f = p → p ∣ n ∧ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨.G2, 0, n / p⟩ ∧ GGHasLabel lab'' R₀ ∧ Nonempty (ggFixDer f ≃* R₀)

abbrev FixGapE6 : Prop :=
  ∀ (n p : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ n → Nat.card K = 2 ^ n → p.Prime → p ≠ 2 →
    ¬ (p ≠ 3 ∧ p ∣ 2 ^ n - 1) →
    ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K (LargeEvenChevH (LargeEvenCartanE 6) K false),
      orderOf f = p → p ∣ n ∧ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨.E6, 0, n / p⟩ ∧ GGHasLabel lab'' R₀ ∧ Nonempty (ggFixDer f ≃* R₀)

abbrev FixGapTwE6 : Prop :=
  ∀ (n p : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime → p ≠ 2 →
    ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K
        (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n),
      orderOf f = p → p ∣ n ∧ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨.twE6, 0, n / p⟩ ∧ GGHasLabel lab'' R₀ ∧ Nonempty (ggFixDer f ≃* R₀)

abbrev FixGapTriD4 : Prop :=
  ∀ (n p : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ n → Nat.card K = (2 ^ n) ^ 3 → p.Prime → p ≠ 2 →
    p ≠ 3 → ∀ f ∈ LargeEvenChevFieldImage LargeEvenCartanD4 K
        (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n),
      orderOf f = p → p ∣ n ∧ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨.triD4, 0, n / p⟩ ∧ GGHasLabel lab'' R₀ ∧ Nonempty (ggFixDer f ≃* R₀)

abbrev FixGapTwB2 : Prop :=
  ∀ (a p : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) → p.Prime →
    p ≠ 2 → ∀ f ∈ LargeEvenMatFieldImage (LargeEvenCenterMk (LargeEvenSzGroup a K)),
      orderOf f = p → p ∣ 2 * a + 1 ∧
        (Group.IsSolvable ↥(ggFixSub f) ∨ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
          IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
          canonLabel lab'' = ⟨.twB2, 0, (2 * a + 1) / p⟩ ∧ GGHasLabel lab'' R₀ ∧
          Nonempty (ggFixDer f ≃* R₀))

abbrev FixGapTwF4 : Prop :=
  ∀ (a p : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) → p.Prime →
    p ≠ 2 → ∀ f ∈ LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K),
      orderOf f = p → p ∣ 2 * a + 1 ∧ ∃ (R₀ : Type) (_ : Group R₀) (lab'' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab'' ∧
        canonLabel lab'' = ⟨.twF4, 0, (2 * a + 1) / p⟩ ∧ GGHasLabel lab'' R₀ ∧
        Nonempty (ggFixDer f ≃* R₀)

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
