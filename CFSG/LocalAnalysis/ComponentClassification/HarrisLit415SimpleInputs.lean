module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def Harris415SmallTypesIndexFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (Nonempty (Y ≃* Blueprint.NativeSporadic.J2) ∨ Nonempty (Y ≃* Blueprint.NativeSporadic.J3) ∨
      Blueprint.LieModel Y .PSL 3 2 2) →
    ∀ τ : MulAut Y, orderOf τ = 2 →
    ∀ K : Subgroup Y, IsTwoComponentIn K (fixedPoints τ) →
    ∀ p m : ℕ, p.Prime → p ≠ 2 → 1 ≤ m → 16 ∣ p ^ (2 * m) - 1 →
      Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 p m →
      4 * twoPart (fixedPoints τ) ≤ twoPart (⊤ : Subgroup Y)

end CFSG.ComponentClassification.HarrisLit
