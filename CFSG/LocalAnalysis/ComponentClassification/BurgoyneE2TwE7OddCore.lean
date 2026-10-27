module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7CoreRows
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Twisted

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Input


@[expose] def BurgoyneE2TwistedE7OddCoreInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 →
    ∀ (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ),
      orderOf (MulAut.conj g * rootDiagAut .E7 K a) = 2 →
      (∀ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) → ∀ ψ : MulAut (adjointGroup .E7 K),
        ψ * (MulAut.conj g * rootDiagAut .E7 K a) * ψ⁻¹ ≠
          rootDiagAut .E7 K (signMaskTuple .E7 K m)) →
      pPrimeCore 2 (fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a)) ≠ ⊥ →
      BurgTorusFor (MulAut.conj g * rootDiagAut .E7 K a)

end Input


theorem burgoyneE2TwistedE7Input_of_oddCore (h : BurgoyneE2TwistedE7OddCoreInput) :
    BurgoyneE2TwistedE7Input := by
  intro K _ _ hK2 g a hα hns
  by_cases hcore : pPrimeCore 2 (fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a)) = ⊥
  · have : Fintype K := Fintype.ofFinite K
    have : CharP K (ringChar K) := ringChar.charP K
    obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
    have : Fact (ringChar K).Prime := ⟨hp⟩
    exact Or.inl (TwE7.burgCoreFor_twisted_of_core (f := n) hK2 n.pos
      (by rw [Nat.card_eq_fintype_card, hcard]) hα hns hcore)
  · exact Or.inr (h K hK2 g a hα hns hcore)

end CFSG.ComponentClassification.Burgoyne.E2
