module

public import CFSG.HardMathSupport.Lang.E6Descent.OutRankTwE6
public import CFSG.HardMathSupport.Lang.E6Descent.FixedTwE6
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6Noninner

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.Chevalley


@[expose] def SubfieldPairTwistedE6 : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 2 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (ℓ ^ f)) → ∀ (p : ℕ), p.Prime → 5 ≤ p → p ≠ ℓ →
    ∀ η : K ≃+* K, orderOf η = p → ∀ ψ : MulAut (twistedE6RootGroup K σ),
      (fixedSubgroup (fieldActor (t := TwistTag.E6) σ η)).map ψ.toMonoidHom ≠
        fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) →
      Subgroup.closure ((fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) :
          Set (twistedE6RootGroup K σ)) ∪
        ((fixedSubgroup (fieldActor (t := TwistTag.E6) σ η)).map ψ.toMonoidHom :
          Set (twistedE6RootGroup K σ))) = ⊤ ∨
        ¬ p ∣ Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ η))

section Main

theorem exists_conj_fieldActor_twE6 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp3 : 3 < p)
    (α : MulAut (twistedE6RootGroup K σ)) (hα : IsOuterOfOrder p α) :
    ∃ (ψ : MulAut (twistedE6RootGroup K σ)) (η : K ≃+* K), orderOf η = p ∧
      ψ * α * ψ⁻¹ = fieldActor σ η := by
  classical
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hord, hout⟩ := hα
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  let α' : (⊤ : Subgroup (MulAut (twistedE6RootGroup K σ))) := ⟨α, Subgroup.mem_top _⟩
  have hα' : (α' : MulAut (twistedE6RootGroup K σ)) ∉
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range :=
    fun ⟨g, hg⟩ => hout g hg.symm
  have hαp : orderOf α' = p := by rw [Subgroup.orderOf_mk]; exact hord
  obtain ⟨hηo, -, ⟨ψ, hψ⟩, -⟩ :=
    twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK' σ hσ Θ hΘ hp
      hp3 ⊤ le_top α' hα' hαp
  exact ⟨ψ, Θ α', hηo, hψ⟩

theorem fieldAutData_twE6 (hpair : SubfieldPairTwistedE6) {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) :
    FieldAutData (twistedE6RootGroup K σ) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hp5 : 5 ≤ p := by
    rcases (show p = 4 ∨ 5 ≤ p by omega) with h | h
    · subst h
      exact absurd hp (by norm_num)
    · exact h
  refine fieldAutData_of_standard ⊤
    {g | ∃ η : K ≃+* K, orderOf η = p ∧ g = fieldActor σ η} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_inner_mem_of_plane_twE6 hℓ hf hK σ hσ hp hp3 E hEc
  · intro α hα
    obtain ⟨ψ, η, hη, h⟩ := exists_conj_fieldActor_twE6 hℓ hf hK σ hσ hp hp3 α hα
    refine ⟨ψ⁻¹, Subgroup.mem_top _, fieldActor σ η, ⟨η, hη, rfl⟩, ?_⟩
    rw [← h]
    group
  · rintro _ ⟨η, hη, rfl⟩ _ ⟨η', hη', rfl⟩
    have := fixedSubgroup_eq_of_zpowers_eq (fieldActorHom (t := TwistTag.E6) σ)
      (zpowers_ringEquiv_eq_of_orderOf hℓ (by omega : 1 ≤ 2 * f) hK' hη hη')
    simpa only [fieldActorHom_apply] using this
  · rintro _ ⟨η, hη, rfl⟩ _ x hx hc
    exact eq_one_of_central_fixed_twE6 hℓ hf hK σ hσ hp hp3 hη hx hc
  · rintro _ ⟨η, hη, rfl⟩ d _ hne
    exact hpair ℓ f hℓ hf K hK σ hσ p hp hp5 hpℓ η hη d hne

end Main

end CFSG.HardMathSupport.Lang.E6Descent
