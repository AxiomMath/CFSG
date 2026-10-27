module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineOddPairBinary
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineOddPairOdd

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair

variable {Y Ω : Type*} [Group Y] [Finite Y] [Finite Ω] [MulAction Y Ω]

omit [Finite Y] [Finite Ω] [MulAction Y Ω] in
theorem no_four_group_iff_no_binary_product_subgroup :
    (∀ V : Subgroup Y, ¬ IsKleinFour V) ↔
      ∀ V : Subgroup Y, ¬ Nonempty (V ≃* Multiplicative (ZMod 2 × ZMod 2)) := by
  constructor
  · intro h V ⟨e⟩
    apply h V
    exact ⟨(Nat.card_congr e.toEquiv).trans IsKleinFour.card_four,
      (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two⟩
  · intro h V hV
    let := hV
    exact h V IsKleinFour.nonempty_mulEquiv

omit [Finite Y] [Finite Ω] in
theorem original_fixed_set_eq_native_fixed_points (A : Subgroup Y) :
    OriginalFixedSet (Ω := Ω) A = MulAction.fixedPoints A Ω := by
  ext γ
  constructor
  · intro h
    exact fun a => h a a.property
  · intro h a ha
    exact h ⟨a, ha⟩

theorem affine_odd_pair_subgroup_full
    (hno : ∀ V : Subgroup Y, ¬ IsKleinFour V) (hdegree : 3 ≤ Nat.card Ω)
    (Q : Subgroup ((MulAction.toPermHom Y Ω).range)) [Q.Normal] [Nontrivial Q]
    (ℓ : ℕ) (hℓ : ℓ.Prime) [IsElementaryAbelian ℓ Q]
    (hreg : RegularOnEntire (MulAction.toPermHom Y Ω).range Q)
    (A : Subgroup Y) (hodd : Odd (Nat.card A)) (α β : Ω) (hne : α ≠ β)
    (hα : ∀ a ∈ A, a • α = α) (hβ : ∀ a ∈ A, a • β = β) :
    3 ≤ Nat.card (OriginalFixedSet (Ω := Ω) A) ∧
      (IsPGroup 2 Q → Nat.card Ω = 4 ∧ ∀ a ∈ A, ∀ γ : Ω, a • γ = γ) := by
  have hbinary : IsPGroup 2 Q →
      Nat.card Ω = 4 ∧ ∀ a ∈ A, ∀ γ : Ω, a • γ = γ := by
    intro htwo
    have hprime := elementary_prime_eq_two_of_two_group ℓ hℓ htwo
    subst ℓ
    exact binary_regular_odd_pair_fixes_every_point hno hdegree Q hreg A hodd α β hne hα hβ
  refine ⟨?_, hbinary⟩
  rcases hℓ.eq_two_or_odd' with htwo | hoddPrime
  · subst ℓ
    obtain ⟨hfour, hfix⟩ := hbinary (IsElementaryAbelian.isPGroup 2 Q)
    have hset : OriginalFixedSet (Ω := Ω) A = Set.univ := by
      ext γ
      exact ⟨fun _ => Set.mem_univ γ, fun _ a ha => hfix a ha γ⟩
    rw [hset, Nat.card_univ, hfour]
    norm_num
  · exact odd_prime_regular_pair_fixed_count_ge_three ℓ hℓ hoddPrime Q hreg A α β hne hα hβ

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair

namespace CFSG.ProperTwoGeneratedCore

open LocalCriterionAffineOddPair

variable {Y Ω : Type*} [Group Y] [Finite Y] [Finite Ω] [MulAction Y Ω]

theorem rank_one_cover_affine_odd_pair_subgroups_fix_three_points
    (hno : ∀ V : Subgroup Y, ¬ Nonempty (V ≃* Multiplicative (ZMod 2 × ZMod 2)))
    (hdegree : 3 ≤ Nat.card Ω)
    (Q : Subgroup ((MulAction.toPermHom Y Ω).range)) [Q.Normal] [Nontrivial Q]
    (helementary : ∃ ℓ : ℕ, ℓ.Prime ∧ IsElementaryAbelian ℓ Q)
    (hreg : RegularOnEntire (MulAction.toPermHom Y Ω).range Q) :
    (∀ (A : Subgroup Y), Odd (Nat.card A) →
      ∀ (α β : Ω), α ≠ β →
        (∀ a ∈ A, a • α = α) → (∀ a ∈ A, a • β = β) →
          3 ≤ Nat.card (MulAction.fixedPoints A Ω)) ∧
      (IsPGroup 2 Q → Nat.card Ω = 4 ∧
        ∀ (A : Subgroup Y), Odd (Nat.card A) →
          ∀ (α β : Ω), α ≠ β →
            (∀ a ∈ A, a • α = α) → (∀ a ∈ A, a • β = β) →
              ∀ a ∈ A, ∀ γ : Ω, a • γ = γ) := by
  obtain ⟨ℓ, hℓ, hQelem⟩ := helementary
  let := hQelem
  have hnoFour := no_four_group_iff_no_binary_product_subgroup.mpr hno
  constructor
  · intro A hodd α β hne hα hβ
    rw [← original_fixed_set_eq_native_fixed_points]
    exact (affine_odd_pair_subgroup_full hnoFour hdegree Q ℓ hℓ hreg A hodd α β hne hα hβ).1
  · intro htwo
    have hprime := elementary_prime_eq_two_of_two_group ℓ hℓ htwo
    subst ℓ
    refine ⟨binary_regular_normal_image_degree_four hnoFour hdegree Q hreg, ?_⟩
    intro A hodd α β hne hα hβ
    exact (binary_regular_odd_pair_fixes_every_point hnoFour hdegree Q hreg
      A hodd α β hne hα hβ).2

end CFSG.ProperTwoGeneratedCore
