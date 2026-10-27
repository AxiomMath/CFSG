module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace X10Rec

@[expose] def Conf (G : Type) [Group G] (N : Subgroup G) (p f : ℕ) : Prop :=
  N.Normal ∧ centralizer (N : Set G) = ⊥ ∧ IsSimpleGroup ↥N ∧
    ∃ (a b : G) (J K P₀ : Subgroup G), orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧
      J ≤ N ∧ J ≤ centralizer ({a} : Set G) ∧
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) ∧
      Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p (2 * f) ∧ b ∈ coreActionKernel J ∧
      P₀ ≤ centralizer ({a} : Set G) ⊓ coreActionKernel J ∧
      (∃ R : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ coreActionKernel J),
        (R : Subgroup _) = P₀.subgroupOf (centralizer ({a} : Set G) ⊓ coreActionKernel J)) ∧
      (∃ y ∈ P₀, Nat.card P₀ = 2 * orderOf y) ∧
      K ≤ N ∧ K ≠ N ∧ K ≤ centralizer ({b} : Set G) ∧
      IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set G))) ∧
      Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSp 2 p f

end X10Rec

@[expose] def CF81X10RowExc : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (τ : StatedLieTag) (p f' f : ℕ), p.Prime → p ≠ 2 →
    (τ ∈ Blueprint.chevalleyExceptionalTags ∨ τ = .twistedG2) →
    StatedLieAdmissible τ 0 p f' → Blueprint.LieModel N τ 0 p f' → 1 ≤ f → 5 ≤ p ^ f →
    ∀ α : MulAut N, α * α = 1 → α ≠ 1 → ∀ L : Subgroup ↥(fixedSubgroup α), IsPComponent 2 L →
      ¬ Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p f

@[expose] def CF81X10RowLin : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (τ : StatedLieTag) (n p f' f : ℕ), p.Prime → p ≠ 2 →
    (τ = .PSL ∨ τ = .PSU) → StatedLieAdmissible τ n p f' → Blueprint.LieModel N τ n p f' →
    1 ≤ f → 5 ≤ p ^ f →
    ∀ α : MulAut N, α * α = 1 → α ≠ 1 → ∀ L : Subgroup ↥(fixedSubgroup α), IsPComponent 2 L →
      (Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p f → (n = 4 ∧ f' = f) ∨ n = 5) ∧
      (n = 5 → ¬ Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSL 2 p (2 * f))

@[expose] def CF81X10RowSpHigh : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (n p f' f : ℕ), p.Prime → p ≠ 2 → 3 ≤ n →
    StatedLieAdmissible .PSp n p f' → Blueprint.LieModel N .PSp n p f' → 1 ≤ f → 5 ≤ p ^ f →
    ∀ α : MulAut N, α * α = 1 → α ≠ 1 → ∀ L : Subgroup ↥(fixedSubgroup α), IsPComponent 2 L →
      (Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p f → n = 4) ∧
      (n = 4 → ¬ Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSL 2 p (2 * f))

@[expose] def CF81X10RowOrth : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) (τ : StatedLieTag) (n p f' f : ℕ),
    p.Prime → p ≠ 2 → 1 ≤ f → 3 < p ^ f → X10Rec.Conf G N p f →
    (τ = .POmegaOdd ∨ τ = .POmegaPlus ∨ τ = .POmegaMinus) → StatedLieAdmissible τ n p f' →
    ¬ Blueprint.LieModel ↥N τ n p f'

end CFSG.ComponentClassification.GSThmB
