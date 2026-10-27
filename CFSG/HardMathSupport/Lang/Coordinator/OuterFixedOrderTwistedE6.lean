module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

set_option linter.unusedSectionVars false

theorem outerFixedOrderBoundAt_twistedE6 : OuterFixedOrderBoundAt .twistedE6 := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 hdiv _ α hαp hαin
  left
  obtain ⟨hℓ, hf, hn⟩ := hadm
  have hchev : ChevalleyExceptionalModel K .twistedE6 ℓ f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hdiv' : ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1) := hdiv
  obtain ⟨K', _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
  set β : MulAut (twistedE6RootGroup K' σ) := MulAut.congr e α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ twistedE6Inn K' σ := fun hin => hαin ((congr_mem_inner_iff e α).mp hin)
  rw [← card_fixedSubgroup_congr e α]
  change ∃ f₀ : ℕ, f = p * f₀ ∧
    Nat.card (fixedSubgroup β) ∣ lieOrderNumerator .twistedE6 0 (ℓ ^ f₀)
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K' hcard σ hσ
  have hη1 : Θ β ≠ 1 := by
    intro h1
    have hmem : β ∈ twistedE6Inn K' σ ⊔ twistedE6Diag K' σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hβout (mem_inner_of_mem_inn_sup_diag hp hcard hσ hdiv' hcube hβp hmem)
  have hK2 : Nat.card K' = ℓ ^ (2 * f) := by rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨d, hd, hd0, r, ε, hε, ψ, hψ⟩ :=
    twisted_E6_field_descent_of_prime_order hℓ hf K' hK2 σ hσ Θ hΘ hp hp2 β hβp hη1
  refine ⟨d, hd, ?_⟩
  have hle : fixedSubgroup β ≤ fixedSubgroup (β ^ r) := by
    intro x hx
    have hx' : β x = x := hx
    show (β ^ r) x = x
    clear hψ
    induction r with
    | zero => rfl
    | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, hx']
  have hconj : Nat.card (fixedSubgroup (β ^ r)) =
      Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)) :=
    card_fixedSubgroup_eq_of_intertwine (ψ : twistedE6RootGroup K' σ ≃* twistedE6RootGroup K' σ)
      (β ^ r) _ fun x => by
        have h := congrArg (fun g : MulAut (twistedE6RootGroup K' σ) => g (ψ x)) hψ
        simpa [MulAut.mul_apply] using h.symm
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hσ, hd, mul_comm]
  have hdvd := card_fixedSubgroup_fieldActor_dvd hℓ hd0 hp.pos K'
    (by rw [hK2, hd, show 2 * (p * d) = 2 * (d * p) by ring]) σ ε hσ' hε
  exact (Subgroup.card_dvd_of_le hle).trans (hconj ▸ hdvd)

end CFSG.HardMathSupport.Lang.Coordinator
