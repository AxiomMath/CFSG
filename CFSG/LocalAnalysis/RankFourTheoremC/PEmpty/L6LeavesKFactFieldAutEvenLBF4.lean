module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenDefs
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedF4
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Fixed27

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.RankThree.Chevalley
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.LocalRank SteinbergBT
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.E6Descent (card_fixedSubgroup_conj even_F4_odd_prime_field_descent)
open CFSG.HardMathSupport.Lang.Coordinator (card_fixedSubgroup_congr congr_mem_inner_iff)

theorem fixedLower_adjointF4
    {ℓ f f₀ p : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (hf₀ : f = p * f₀) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (adjointGroup Tag.F4 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.F4 K)) :
    CFSG.Open.ordF4 (ℓ ^ f₀) ∣ Nat.card (fixedSubgroup α) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner (adjointGroup Tag.F4 K)).one_mem)
  have hαin :
      α ∉ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range := hα
  obtain ⟨σ, ψ, hσp, hψ⟩ : ∃ (σ : K ≃+* K) (ψ : MulAut (adjointGroup Tag.F4 K)),
      orderOf σ = p ∧ ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.F4 σ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact even_F4_odd_prime_field_descent hf K hK hp hp2 α hαord hαin
    · obtain ⟨-, σ, δ, hσp, -, hδ, -⟩ :=
        odd_F4_prime_field_coset_descent hℓ hℓ2 hf K hK hp α hαord hαin
      exact ⟨σ, δ, hσp, hδ⟩
  obtain ⟨-, hcard⟩ := card_fixSubfield hℓ hf hK σ
  rw [hσp, show f / p = f₀ by rw [hf₀, Nat.mul_div_cancel_left f₀ hp.pos]] at hcard
  rw [← card_fixedSubgroup_conj ψ α, hψ]
  have h := CFSG.HardMathSupport.Malle.E27Lie.card_adjointGroup_dvd_card_fixedSubgroup
    (τ := Tag.F4) σ
  rwa [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hcard] at h

theorem fixedLowerBoundAt_F4
    : FixedLowerBoundAt .F4 := by
  intro K _ _ n ℓ f f₀ p hadm hmodel _ hp hp5 _ _ hf α hαp hαin
  have : Fact ℓ.Prime := ⟨hadm.1⟩
  have hf1 : 1 ≤ f := hadm.2.1
  rcases hmodel with ⟨ht, -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hE
    let θ : K ≃* adjointGroup Tag.F4 F := e.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    have hβp : MulAut.congr θ α ^ p = 1 := by rw [← map_pow, hαp, map_one]
    have hβout : MulAut.congr θ α ∉ inner (adjointGroup Tag.F4 F) := fun hin =>
      hαin ((congr_mem_inner_iff θ α).mp hin)
    rw [← card_fixedSubgroup_congr θ α]
    have h := fixedLower_adjointF4 hf1 hf F hFcard hp (by omega) _ hβp hβout
    have h1 : lieOrderDivisor .F4 0 (ℓ ^ f₀) = 1 := rfl
    have h2 : lieOrderNumerator .F4 0 (ℓ ^ f₀) = CFSG.Open.ordF4 (ℓ ^ f₀) := rfl
    rw [h1, h2, one_mul]
    exact h
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
