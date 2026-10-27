module

public import CFSG.CharacterTheory.Semidihedral.Principal.TensorGapBound
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralQuotientRegular
public import CFSG.CharacterTheory.Wreathed.WeightedCentralInvolutionSum

public noncomputable section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

universe u w

@[expose] def regularClassFunction (U : Type u) [Group U] [Fintype U] : U → ℂ :=
  fun u => if u = 1 then (Nat.card U : ℂ) else 0

theorem characterPairing_regularClassFunction {U : Type u} [Group U] [Fintype U] (g : U → ℂ) :
    characterPairing (regularClassFunction U) g = g 1 := by
  unfold characterPairing regularClassFunction
  rw [Finset.sum_eq_single (1 : U)]
  · simp only [ite_true, inv_one]
    have h0 : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp
  · intro u _ hu
    simp [hu]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_basis_label_ne_one {U : Type u} [Group U] [Fintype U] (hU : 1 < Nat.card U)
    (basis : FiniteIrreducibleCharacterBasis U) :
    ∃ ψ : basis.index, (basis.representation ψ).character ≠ 1 := by
  by_contra! hall
  have hzero : regularClassFunction U - 1 = 0 := by
    apply basis.separates
    · intro x c
      simp only [Pi.sub_apply, Pi.one_apply, regularClassFunction]
      congr 1
      by_cases hx : x = 1
      · simp [hx]
      · have : c * x * c⁻¹ ≠ 1 := by
          intro h
          apply hx
          have := congrArg (fun y => c⁻¹ * y * c) h
          simpa [mul_assoc] using this
        simp [hx, this]
    · intro ψ
      rw [hall ψ, characterPairing_sub_left, characterPairing_regularClassFunction]
      simp [characterPairing, Nat.card_eq_fintype_card]
  have h1 := congrFun hzero 1
  simp only [Pi.sub_apply, Pi.one_apply, regularClassFunction, ite_true, Pi.zero_apply,
    sub_eq_zero] at h1
  have : Nat.card U = 1 := by exact_mod_cast h1
  omega

theorem characterPairing_const_add_regular {U : Type u} [Group U] [Fintype U] (a b : ℂ)
    (g : U → ℂ) :
    characterPairing (a • (1 : U → ℂ) + b • regularClassFunction U) g =
      a * characterPairing (1 : U → ℂ) g + b * g 1 := by
  rw [← characterPairing_regularClassFunction g]
  unfold characterPairing
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_add]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

theorem isMulCommutative_of_forall_commute {H : Type u} [Group H] (U : Subgroup H)
    (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) : IsMulCommutative U :=
  ⟨⟨fun a b => Subtype.ext (hU a a.2 b b.2)⟩⟩

theorem regular_coefficients_natural {H : Type u} [Group H] [Fintype H] (U : Subgroup H)
    (hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU : 1 < Nat.card U) (Φ : H → ℂ)
    (hΦ1 : Φ 1 = Nat.card U) (hΦ : ∀ u ∈ U, u ≠ 1 → Φ u = 0)
    (χ : FiniteComplexRepresentation.{u, w} H) (a b : ℂ)
    (hχ : ∀ y ∈ U, χ.character y = a + b * Φ y) :
    (∃ n : ℕ, b = n) ∧ ∃ n : ℕ, a + b = n := by
  let basis : FiniteIrreducibleCharacterBasis U := (finiteIrreducibleCharacterBasis_exists).some
  obtain ⟨p₀, hp₀, -⟩ := complete_character_basis_contains_irreducible basis
    (principalFiniteComplexRepresentation U) (principalFiniteComplexRepresentation_isIrreducible U)
  rw [principalFiniteComplexRepresentation_character] at hp₀
  obtain ⟨ψ, hψ⟩ := exists_basis_label_ne_one hU basis
  have : IsMulCommutative U := isMulCommutative_of_forall_commute U hUcomm
  have hψdeg : (basis.representation ψ).character 1 = 1 := by
    have : (basis.representation ψ).representation.IsIrreducible := basis.irreducible ψ
    rw [FiniteComplexRepresentation.character, Representation.char_one,
      Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
        (basis.representation ψ).representation, Nat.cast_one]
  let ρ := inflatedFiniteComplexRepresentation U.subtype χ
  have hρ : ρ.character = a • (1 : U → ℂ) + b • regularClassFunction U := by
    funext u
    rw [inflatedFiniteComplexRepresentation_character]
    simp only [Function.comp_apply, Subgroup.coe_subtype, Pi.add_apply, Pi.smul_apply,
      Pi.one_apply, smul_eq_mul, mul_one, regularClassFunction]
    rw [hχ u u.2]
    by_cases hu : u = 1
    · subst hu
      simp [hΦ1]
    · have hu' : (u : H) ≠ 1 := fun h => hu (Subtype.ext h)
      simp [hu, hΦ u u.2 hu']
  have hp₀ψ : characterPairing (1 : U → ℂ) (basis.representation ψ).character = 0 := by
    rw [← hp₀, characterPairing_irreducible _ _ (basis.irreducible p₀) (basis.irreducible ψ),
      ite_eq_right]
    intro h
    exact hψ (h ▸ hp₀)
  have hp₀p₀ : characterPairing (1 : U → ℂ) (1 : U → ℂ) = 1 := by
    rw [← hp₀, characterPairing_irreducible _ _ (basis.irreducible p₀) (basis.irreducible p₀),
      ite_eq_left rfl]
  obtain ⟨m₁, hm₁⟩ := characterPairing_basis_natural basis ρ ψ
  obtain ⟨m₀, hm₀⟩ := characterPairing_basis_natural basis ρ p₀
  rw [hρ, characterPairing_const_add_regular, hp₀ψ, hψdeg] at hm₁
  rw [hρ, characterPairing_const_add_regular, hp₀, hp₀p₀] at hm₀
  refine ⟨⟨m₁, ?_⟩, ⟨m₀, ?_⟩⟩
  · rw [← hm₁]
    ring
  · rw [← hm₀]
    simp

theorem odd_abelian_lift_coefficients_natural {H Γ : Type u} [Group H] [Fintype H] [Group Γ]
    (π : H →* Γ) (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center H)
    (hZ2 : IsPGroup 2 π.ker) (U : Subgroup Γ) (hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hUodd : Odd (Nat.card U)) (hU : 1 < Nat.card U) (φ : Γ → ℂ) (hφ1 : φ 1 = Nat.card U)
    (hφ : ∀ u ∈ U, u ≠ 1 → φ u = 0) (χ : FiniteComplexRepresentation.{u, w} H) (a b : ℂ)
    (hχ : ∀ y : H, Odd (orderOf y) → χ.character y = a + b * φ (π y)) :
    (∃ n : ℕ, b = n) ∧ ∃ n : ℕ, a + b = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hlift⟩ :=
    central_p_quotient_prime_regular_elements_of_surjective π hπ hZ hZ2
  obtain ⟨Ũ, e, hŨ, hŨcomm, he⟩ := hlift U hUcomm hUodd.not_two_dvd_nat
  have hcard : Nat.card Ũ = Nat.card U := Nat.card_congr e.toEquiv
  refine regular_coefficients_natural Ũ hŨcomm (hcard ▸ hU) (fun y => φ (π y)) ?_ ?_ χ a b ?_
  · rw [map_one, hφ1, hcard]
  · intro u hu hu1
    have hmem : π u ∈ U := by
      have : u ∈ (Ũ : Set H) := hu
      rw [hŨ] at this
      exact this.2
    refine hφ _ hmem fun h1 => hu1 ?_
    have h := he ⟨u, hu⟩
    rw [h1] at h
    have : e ⟨u, hu⟩ = 1 := Subtype.ext h
    exact congrArg Subtype.val (e.injective (this.trans e.map_one.symm))
  · intro y hy
    have : y ∈ (Ũ : Set H) := hy
    rw [hŨ] at this
    exact hχ y (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp this.1))

end CFSG.Wreathed
