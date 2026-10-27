module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.LocalAnalysis.GLTheoremB Subgroup

@[expose] def KGTransvCent : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (V : Type) [CommGroup V] [Finite V], IsElemAbelianTwo V →
    ∀ (ρ : A →* MulAut V) (N : Subgroup A) (a z : A) (q : ℕ),
      IsSimpleGroup ↥N → (∃ x y : ↥N, x * y ≠ y * x) →
      (∀ n : ℕ, 7 ≤ n → ¬ Nonempty (↥N ≃* alternatingGroup (Fin n))) →
      a ∈ normalizer (N : Set A) → a ≠ 1 → a ^ 2 = 1 → a ∉ N →
      (∀ x ∈ N ⊔ zpowers a, (∀ n ∈ N, x * n = n * x) → x = 1) →
      (∀ x ∈ N ⊔ zpowers a, ρ x = 1 → x = 1) → IsTransvection (ρ a) →
      z ∈ N → orderOf z = q → q.Prime → 5 ≤ q → a * z = z * a →
      ∃ (ε : Bool) (n : ℕ), 3 ≤ n ∧ IsOmegaTwo ε n ↥N ∧
        ∃ Y : Subgroup A, Y ≤ N ⊓ centralizer ({a} : Set A) ∧ z ∈ Y ∧ IsSimpleGroup ↥Y ∧
          (∃ x y : ↥Y, x * y ≠ y * x) ∧ 3 ∣ Nat.card ↥Y

@[expose] def KFact2401ThreeOmega : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L E : Subgroup A) (ε : Bool) (n : ℕ), 3 ≤ n →
    IsOmegaTwo ε n ↥L → CFSG.ABGLocalTools.IsSylowOf 3 E L →
    ∀ J : Subgroup A, (∀ S₀ : Subgroup A, S₀ ≤ E → S₀ ≠ ⊥ →
      normalizer (S₀ : Set A) ⊓ L ≤ J) → L ≤ J

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
