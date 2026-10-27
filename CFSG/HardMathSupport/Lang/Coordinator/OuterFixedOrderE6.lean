module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Adjoint

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.SteinbergBT CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section

theorem E6_adjoint_outer_fixed_order {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : ¬ p ∣ Nat.gcd 3 (ℓ ^ f - 1)) (α' : MulAut (adjointGroup Tag.E6 K))
    (hα'pow : α' ^ p = 1) (hα : α' ∉ inner (adjointGroup Tag.E6 K)) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      Nat.card (fixedSubgroup α') ∣ lieOrderNumerator .E6 0 (ℓ ^ f₀) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  exact CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrder_adjointE6 hf K hK hp hp2 hdiv α'
    hα'pow hα

theorem outerFixedOrderBoundAt_E6 : OuterFixedOrderBoundAt .E6 := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 hdiv _ α hαp hαin
  left
  rcases hmodel with ⟨ht, -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hE
    have hdiv' : ¬ p ∣ Nat.gcd 3 (ℓ ^ f - 1) := hdiv
    let θ : K ≃* adjointGroup Tag.E6 F := e.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    have hβp : MulAut.congr θ α ^ p = 1 := by rw [← map_pow, hαp, map_one]
    have hβout : MulAut.congr θ α ∉ inner (adjointGroup Tag.E6 F) :=
      fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
    rw [← card_fixedSubgroup_congr θ α]
    exact E6_adjoint_outer_fixed_order hadm.1 hadm.2.1 F hFcard hp hp2 hdiv' _ hβp hβout
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end

end CFSG.HardMathSupport.Lang.Coordinator
