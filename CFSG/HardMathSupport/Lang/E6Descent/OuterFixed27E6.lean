module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27Arith
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcFieldCore

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.RankThree.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank SteinbergBT
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Malle.E27Lie

section

theorem twentySeven_dvd_fixedSubgroup_adjointE_of_diag
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h27 : ∀ (F : Type) [Field F] [Finite F], 27 ∣ Nat.card (adjointGroup τ F))
    {ℓ f p : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (adjointGroup τ K)) (hαp : α ^ p = 1)
    (_hα : α ∉ inner (adjointGroup τ K))
    (hdiag : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      α = MulAut.conj g * rootDiagAut τ K a → 27 ∣ Nat.card (fixedSubgroup α)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  by_cases hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      α ≠ MulAut.conj g * rootDiagAut τ K a
  · have : Finite K :=
      Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
    obtain ⟨-, T, r, j, ψ, -, -, -, -, -, hαβ, hψ⟩ :=
      exists_conj_entrywise_of_not_innerDiag τ hτ hf K hK hp hp2 α hαp hnd
    rw [fixedSubgroup_pow_eq hαβ]
    exact dvd_card_fixedSubgroup_of_conj h27 (α ^ r) ψ T hψ
  · push Not at hnd
    obtain ⟨g, a, hga⟩ := hnd
    exact hdiag g a hga

theorem twentySeven_dvd_card_adjointGroup_E6 (F : Type) [Field F] [Finite F] :
    27 ∣ Nat.card (adjointGroup Tag.E6 F) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6]
  exact twentySeven_dvd_ordE6 _ Nat.card_pos

end

end CFSG.HardMathSupport.Lang.E6Descent
