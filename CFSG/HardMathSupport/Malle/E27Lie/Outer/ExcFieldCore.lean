module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Fixed27
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Arith27
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedF4

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Lang.E6Descent

section


theorem dvd_card_fixedSubgroup_of_conj {τ : Tag} {K : Type} [Field K] [Finite K]
    (h27 : ∀ (F : Type) [Field F] [Finite F], 27 ∣ Nat.card (adjointGroup τ F))
    (α : MulAut (adjointGroup τ K)) (ψ : MulAut (adjointGroup τ K)) (σ : K ≃+* K)
    (hψ : ψ * α * ψ⁻¹ = entrywiseAdjointAut τ σ) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  rw [← card_fixedSubgroup_conj ψ α, hψ]
  exact (h27 (fixSubfield σ)).trans (card_adjointGroup_dvd_card_fixedSubgroup σ)

theorem twentySeven_dvd_card_adjointGroup_G2 (F : Type) [Field F] [Finite F] :
    27 ∣ Nat.card (adjointGroup Tag.G2 F) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
  exact twentySeven_dvd_ordG2 _ Nat.card_pos

theorem twentySeven_dvd_card_adjointGroup_F4 (F : Type) [Field F] [Finite F] :
    27 ∣ Nat.card (adjointGroup Tag.F4 F) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
  exact twentySeven_dvd_ordF4 _ Nat.card_pos

theorem twentySeven_dvd_fixedSubgroup_G2 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (h3 : 3 ≤ ℓ ^ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup Tag.G2 K))
    (hα3 : α ^ 3 = 1) (hα : α ∉ inner (adjointGroup Tag.G2 K)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hαord : orderOf α = 3 :=
    orderOf_eq_prime hα3 fun h1 => hα (h1 ▸ (inner (adjointGroup Tag.G2 K)).one_mem)
  have hform : ∃ (x : adjointGroup Tag.G2 K) (σ : K ≃+* K),
      orderOf σ = 3 ∧ α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
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
  obtain ⟨δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut_of_form Tag.G2 hℓ hf K hK hp α hαord x σ
    hσp hασ
  exact dvd_card_fixedSubgroup_of_conj twentySeven_dvd_card_adjointGroup_G2 α δ σ hδ

theorem twentySeven_dvd_fixedSubgroup_F4 {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.F4 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (adjointGroup Tag.F4 K)) : 27 ∣ Nat.card (fixedSubgroup α) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hαord : orderOf α = 3 :=
    orderOf_eq_prime hα3 fun h1 => hα (h1 ▸ (inner (adjointGroup Tag.F4 K)).one_mem)
  have hαin : α ∉ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range :=
    hα
  obtain ⟨σ, ψ, -, hψ⟩ : ∃ (σ : K ≃+* K) (ψ : MulAut (adjointGroup Tag.F4 K)),
      orderOf σ = 3 ∧ ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.F4 σ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact even_F4_odd_prime_field_descent hf K hK hp hp2 α hαord hαin
    · obtain ⟨-, σ, δ, hσp, -, hδ, -⟩ :=
        odd_F4_prime_field_coset_descent hℓ hℓ2 hf K hK hp α hαord hαin
      exact ⟨σ, δ, hσp, hδ⟩
  exact dvd_card_fixedSubgroup_of_conj twentySeven_dvd_card_adjointGroup_F4 α ψ σ hψ

end

end CFSG.HardMathSupport.Malle.E27Lie
