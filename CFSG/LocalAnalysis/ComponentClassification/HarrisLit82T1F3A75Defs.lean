module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def Harris82OutQuatThree : Prop :=
  ∀ (S : Type) [Group S],
    ((IsSimpleChevalleyOver 3 S ∧ (∀ f : ℕ, ¬ Blueprint.LieModel S .PSL 2 3 f) ∧
        ∀ f : ℕ, ¬ Blueprint.LieModel S .POmegaPlus 4 3 f) ∨
      Nonempty (S ≃* ↥Blueprint.NativeSporadic.M11)) →
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nonempty (X ⧸ center X ≃* S) →
    ∀ (R : Subgroup (MulAut X)) (φ : ↥R →* PSL(2, ZMod 3)), Function.Surjective φ →
      ∃ r : ↥R, (r : MulAut X) ∈ (MulAut.conj : X →* MulAut X).range ∧ φ r ≠ 1

namespace F3FG

@[expose] def FourGroupResidualStepD4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ z₁ z₂ : G, orderOf z₁ = 2 → orderOf z₂ = 2 → z₁ ≠ z₂ → z₁ * z₂ = z₂ * z₁ →
    ∀ L₁ K : Subgroup G, IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}) →
    z₁ ∈ L₁ → Nonempty (↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)) →
    IsTwoComponentIn K (centralizer {z₁}) →
    centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) →
    ⁅K, GH74.GLS.oPrimeResidualOf 3 L₁⁆ = K →
    (∃ hz₂K : z₂ ∈ K, (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
      center (↥K ⧸ pPrimeCore 2 ↥K)) →
    ((IsSimpleChevalleyOver 3 (↥K ⧸ Open.fusionZStar ↥K) ∧
        ∀ f : ℕ, ¬ Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL 2 3 f) ∨
      Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃* ↥Blueprint.NativeSporadic.M11)) →
    (∃ f : ℕ, Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .POmegaPlus 4 3 f) →
      GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K

end F3FG

end CFSG.ComponentClassification.HarrisLit.T1
