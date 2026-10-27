module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Adjoint

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.RankThree.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank SteinbergBT
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem outerFixedOrder_adjointE
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (t : StatedLieTag)
    (hfix : ∀ {M : Type} [Field M] [Finite M] (σ : M ≃+* M) {q₀ : ℕ},
      Nat.card (fixSubfield σ) = q₀ →
        Nat.card (entrywiseFixedGroup τ σ) ∣ lieOrderNumerator t 0 q₀)
    {ℓ f p : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ¬ p ∣ τ.cartan.det.natAbs)
    (α : MulAut (adjointGroup τ K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup τ K)) :
    ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator t 0 (ℓ ^ f₀) := by
  obtain ⟨d, T, r, j, ψ, hd, -, hcard, hαβ, hψ⟩ :=
    exists_conj_entrywise_of_outer_E τ hτ hf K hK hp hp2 hdet α hαp hα
  refine ⟨d, hd, ?_⟩
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  rw [fixedSubgroup_pow_eq hαβ, ← card_fixedSubgroup_conj ψ (α ^ r), hψ,
    card_fixedSubgroup_entrywiseAdjointAut]
  exact hfix T hcard

end CFSG.HardMathSupport.Lang.E6Descent
