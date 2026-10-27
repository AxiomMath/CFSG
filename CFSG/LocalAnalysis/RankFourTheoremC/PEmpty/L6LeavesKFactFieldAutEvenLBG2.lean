module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenDefs
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Fixed27

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GroupTheory
  CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.E6Descent
  (card_fixedSubgroup_conj G2_form_odd G2_form_even G2_form_three
    exists_conj_eq_entrywiseAdjointAut_of_form)
open CFSG.HardMathSupport.Lang.Coordinator (card_fixedSubgroup_congr congr_mem_inner_iff)

theorem fixedLower_adjointG2
    {ℓ f f₀ p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hf₀ : f = p * f₀) (h3 : 3 ≤ ℓ ^ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (adjointGroup Tag.G2 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.G2 K)) :
    CFSG.Open.ordG2 (ℓ ^ f₀) ∣ Nat.card (fixedSubgroup α) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner (adjointGroup Tag.G2 K)).one_mem)
  have hform : ∃ (x : adjointGroup Tag.G2 K) (σ : K ≃+* K),
      orderOf σ = p ∧ α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have hf2 : 2 ≤ f := by
        by_contra h
        have : f = 1 := by omega
        subst this
        omega
      exact G2_form_even hf2 K hK hp α hαord hα
    by_cases hℓ3 : ℓ = 3
    · subst hℓ3
      have : CharP K 3 := finite_field_prime_power_characteristic hℓ hf hK
      exact G2_form_three hf K hK hp hp2 α hαord hα
    · exact G2_form_odd hℓ hℓ2 hℓ3 hf K hK hp α hαord hα
  obtain ⟨x, σ, hσp, hασ⟩ := hform
  obtain ⟨δ, hδ⟩ :=
    exists_conj_eq_entrywiseAdjointAut_of_form Tag.G2 hℓ hf K hK hp α hαord x σ hσp hασ
  obtain ⟨-, hcard⟩ := card_fixSubfield hℓ hf hK σ
  rw [hσp, show f / p = f₀ by rw [hf₀, Nat.mul_div_cancel_left f₀ hp.pos]] at hcard
  rw [← card_fixedSubgroup_conj δ α, hδ]
  have h := CFSG.HardMathSupport.Malle.E27Lie.card_adjointGroup_dvd_card_fixedSubgroup
    (τ := Tag.G2) σ
  rwa [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hcard] at h

theorem fixedLowerBoundAt_G2
    : FixedLowerBoundAt .G2 := by
  intro K _ _ n ℓ f f₀ p hadm hmodel _ hp hp5 _ _ hf α hαp hαin
  have hℓ : ℓ.Prime := hadm.1
  have hf1 : 1 ≤ f := hadm.2.1
  have h3 : 3 ≤ ℓ ^ f := hadm.2.2.2
  rcases hmodel with ⟨ht, -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hE
    let θ : K ≃* adjointGroup Tag.G2 F := e.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    have hβp : MulAut.congr θ α ^ p = 1 := by rw [← map_pow, hαp, map_one]
    have hβout : MulAut.congr θ α ∉ inner (adjointGroup Tag.G2 F) := fun hin =>
      hαin ((congr_mem_inner_iff θ α).mp hin)
    rw [← card_fixedSubgroup_congr θ α]
    have h := fixedLower_adjointG2 hℓ hf1 hf h3 F hFcard hp (by omega) _ hβp hβout
    have h1 : lieOrderDivisor .G2 0 (ℓ ^ f₀) = 1 := rfl
    have h2 : lieOrderNumerator .G2 0 (ℓ ^ f₀) = CFSG.Open.ordG2 (ℓ ^ f₀) := rfl
    rw [h1, h2, one_mul]
    exact h
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
