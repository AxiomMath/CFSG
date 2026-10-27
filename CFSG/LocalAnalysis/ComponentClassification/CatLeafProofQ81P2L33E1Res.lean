module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.E1

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def ChevOddInnerInput :
    Prop :=
  (∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
    ∀ α : MulAut (adjointGroup .E7 K), α ^ 2 = 1 → α ≠ 1 →
      (∃ (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ), ∀ h : adjointGroup .E7 K,
        (α h : ModGL .E7 K) = (g : ModGL .E7 K) * rootDiagUnit .E7 a * h *
          (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹) →
      ∃ X : Subgroup (adjointGroup .E7 K), X ≤ fixedSubgroup α ∧ ⁅X, X⁆ = X ∧
        2 ∣ Nat.card X) ∧
  ∀ (t : TwistTag) (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ t.order →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
        ∀ x : graphFixedRootGroup t K σ.toRingHom, x ^ 2 = 1 → x ≠ 1 →
          ∃ X : Subgroup (graphFixedRootGroup t K σ.toRingHom),
            X ≤ fixedSubgroup (MulAut.conj x) ∧ ⁅X, X⁆ = X ∧ 2 ∣ Nat.card X

end CFSG.ComponentClassification.HarrisLit.L33.E1
