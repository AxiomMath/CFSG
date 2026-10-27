module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowFixed

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def OuterFixedOrderBoundAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n ℓ f : ℕ),
    StatedLieAdmissible t n ℓ f → CFSG.Blueprint.LieModel K t n ℓ f → t ≠ .Tits →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ lieOrderDivisor t n (ℓ ^ f) →
      ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3) →
    ∀ α : MulAut K, α ^ p = 1 → α ∉ inner K →
      (∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator t n (ℓ ^ f₀)) ∨
      (t = .trialityD4 ∧ p = 3 ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .G2 0 (ℓ ^ f))

theorem outerFixedOrderBound_of_forall (h : ∀ t, OuterFixedOrderBoundAt t) :
    CFSG.AGLEmbedding.OuterSylow.OuterFixedOrderBound :=
  fun K _ _ t n ℓ f hadm hm ht p hp hp2 hd hD4 α hα hin =>
    h t K n ℓ f hadm hm ht p hp hp2 hd hD4 α hα hin

end CFSG.HardMathSupport.Lang.Coordinator
