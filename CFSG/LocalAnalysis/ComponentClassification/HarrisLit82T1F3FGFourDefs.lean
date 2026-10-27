module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def FourGroupResidualStep : Prop :=
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
      GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
