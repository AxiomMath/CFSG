module

public import CFSG.CharacterTheory.Wreathed.GeneralCentralTwoCoverRegularBasis

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Wreathed

theorem two_smul_projective_regular_gram {k : ℕ} (hk : 2 ≤ k) :
    (2 : ℤ) • !![4, -2; -2, ((2 ^ (k - 2) + 1 : ℕ) : ℤ)] =
      !![8, -4; -4, ((2 ^ (k - 1) + 2 : ℕ) : ℤ)] := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
  · simp
  · simp
    ring

theorem projective_central_double_cover_principal_regular_integral_basis {p f : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f) (F : Type) [Field F] [Fintype F]
    (hcard : Nat.card F = p ^ f) (Γ : Subgroup (Equiv.Perm (Omega F)))
    (hDΓ : coordinateD F ≤ Γ) (hΓE : Γ ≤ coordinateE F) {k : ℕ} (hk : 2 ≤ k)
    (hS : ∃ S : Sylow 2 Γ, Nonempty ((S : Subgroup Γ) ≃* DihedralGroup (2 ^ (k - 1))))
    (hG : ∃ T : Sylow 2 (coordinateG F), ¬ IsCyclic (T : Subgroup (coordinateG F)))
    {H : Type} [Group H] [Fintype H] (π : H →* Γ) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center H) (hZcard : Nat.card π.ker = 2)
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    let Φ : H → ℂ := fun h =>
      (Nat.card {x : Omega F // ((π h : Γ) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1
    let e : ℤ := if Nat.card F % 4 = 1 then 1 else -1
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    3 ≤ k ∧
    (∃ lΦ ∈ B, (basis.representation lΦ).character = Φ) ∧
    (∀ χ ∈ B, ∃ a b : ℤ, (∀ y : H, Odd (orderOf y) →
        (basis.representation χ).character y = a + b * Φ y) ∧ 0 ≤ b ∧ 0 ≤ a + b ∧
      ∀ a' b' : ℤ, (∀ y : H, Odd (orderOf y) →
        (basis.representation χ).character y = a' + b' * Φ y) → a' = a ∧ b' = b) ∧
    LinearIndependent ℤ ![oddRestriction (1 : H → ℂ), oddRestriction (1 + (e : ℂ) • Φ)] ∧
    Submodule.span ℤ {oddRestriction (1 : H → ℂ), oddRestriction (1 + (e : ℂ) • Φ)} =
      oddRestrictionLattice basis B ∧
    (∃ A : Matrix B (Fin 2) ℤ, ∀ χ : B,
      oddRestriction (basis.representation χ).character =
        A χ 0 • oddRestriction (1 : H → ℂ) + A χ 1 • oddRestriction (1 + (e : ℂ) • Φ)) ∧
    ∀ A : Matrix B (Fin 2) ℤ, (∀ χ : B,
      oddRestriction (basis.representation χ).character =
        A χ 0 • oddRestriction (1 : H → ℂ) + A χ 1 • oddRestriction (1 + (e : ℂ) • Φ)) →
      A.transpose * A = !![8, -4; -4, ((2 ^ (k - 1) + 2 : ℕ) : ℤ)] := by
  intro Φ e B
  have hZ2 : IsPGroup 2 π.ker := IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
  obtain ⟨hk3, hΦ, hcoeff, hind, hspan, hA, hgram⟩ :=
    general_central_two_cover_principal_regular_integral_basis hp hodd hf F hcard Γ hDΓ hΓE hk hS
      hG π hπ hZ hZ2 basis ideal principal hprincipal
  refine ⟨hk3, hΦ, hcoeff, hind, hspan, hA, fun A hrows => ?_⟩
  rw [hgram A hrows, hZcard, Nat.cast_ofNat, two_smul_projective_regular_gram hk]

end CFSG.Semidihedral.Principal
