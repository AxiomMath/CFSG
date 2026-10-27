module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeInversionFamily

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem cyclic_five_sylow_inversion_normalizer_principal_block_four_character_family
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 5] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow 5 G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) (hP : Nat.card P = 5)
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 2) :
    ∃ (δ : ℤ) (χ ψ₁ ψ₂ : basis.index),
      (δ = 1 ∨ δ = -1) ∧ χ ≠ principal ∧ ψ₁ ≠ principal ∧ ψ₂ ≠ principal ∧ χ ≠ ψ₁ ∧ χ ≠ ψ₂ ∧
      ψ₁ ≠ ψ₂ ∧
      coefficientBlock basis (localizedComplexIntegerRing ideal) principal =
        {principal, χ, ψ₁, ψ₂} ∧
      (∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal, ∀ g : G,
        starRingEnd ℂ ((basis.representation θ).character g) =
          (basis.representation θ).character g) ∧
      (basis.representation ψ₁).character 1 = (basis.representation χ).character 1 + δ ∧
      (basis.representation ψ₂).character 1 = (basis.representation χ).character 1 + δ ∧
      0 < (Module.finrank ℂ (basis.representation χ).vector : ℤ) + δ ∧
      (∀ x : G, ¬ 5 ∣ orderOf x →
        (basis.representation ψ₁).character x = (basis.representation χ).character x + δ ∧
        (basis.representation ψ₂).character x = (basis.representation χ).character x + δ) ∧
      (∀ j ∈ Finset.Icc 1 4, ∀ y ∈ Subgroup.centralizer ({u} : Set G), ¬ 5 ∣ orderOf y →
        (basis.representation χ).character (u ^ j * y) = δ ∧
        (basis.representation ψ₁).character (u ^ j * y) =
          δ * (Complex.exp (2 * Real.pi * Complex.I / 5) ^ ((1 * j : ℕ) : ℤ) +
            Complex.exp (2 * Real.pi * Complex.I / 5) ^ (-((1 * j : ℕ) : ℤ))) ∧
        (basis.representation ψ₂).character (u ^ j * y) =
          δ * (Complex.exp (2 * Real.pi * Complex.I / 5) ^ ((2 * j : ℕ) : ℤ) +
            Complex.exp (2 * Real.pi * Complex.I / 5) ^ (-((2 * j : ℕ) : ℤ)))) ∧
      (∀ z : G, 5 ∣ orderOf z → ∃ j ∈ Finset.Icc 1 4,
        ∃ y ∈ Subgroup.centralizer ({u} : Set G), ¬ 5 ∣ orderOf y ∧ IsConj z (u ^ j * y)) ∧
      ∀ x₁ x₂ z : G, ¬ 5 ∣ orderOf x₁ → ¬ 5 ∣ orderOf x₂ → 5 ∣ orderOf z →
        ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation θ).character x₁ * (basis.representation θ).character x₂ *
            (basis.representation θ).character z / (basis.representation θ).character 1 =
          ((basis.representation χ).character 1 - (basis.representation χ).character x₁) *
            ((basis.representation χ).character 1 - (basis.representation χ).character x₂) /
              ((basis.representation χ).character 1 *
                ((basis.representation χ).character 1 + δ)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨δ, χ, ψ, hδ, hχ, hψ, hinj, hB, hreal, hpos, hdeg, hreg, hval, hconj, hsum⟩ :=
    prime_order_sylow_inversion_normalizer_exact_principal_block_family basis ideal 5 le_rfl
      principal hprincipal P u hPu hP hindex
  have hIcc : Finset.Icc 1 ((5 - 1) / 2) = {1, 2} := by decide
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 ((5 - 1) / 2) := by rw [hIcc]; simp
  have h2 : (2 : ℕ) ∈ Finset.Icc 1 ((5 - 1) / 2) := by rw [hIcc]; simp
  have hPset : (P : Set G) = (Subgroup.zpowers u : Set G) := by rw [← hPu]; rfl
  have hcent : ∀ y : G, y ∈ Subgroup.centralizer ({u} : Set G) ↔
      y ∈ Subgroup.centralizer (P : Set G) := by
    intro y
    rw [hPset, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact CFSG.LyonsUnitaryFour.mem_centralizer_zpowers_of_commute h.symm
    · intro h
      exact (CFSG.LyonsUnitaryFour.commute_of_mem_centralizer_zpowers u ⟨y, h⟩).eq.symm
  refine ⟨δ, χ, ψ 1, ψ 2, hδ, hχ, (hψ 1 h1).1, (hψ 2 h2).1, fun h => (hψ 1 h1).2 h.symm,
    fun h => (hψ 2 h2).2 h.symm, fun h => absurd (hinj h1 h2 h) (by norm_num), ?_, hreal,
    hdeg 1 h1, hdeg 2 h2, hpos, fun x hx => ⟨hreg 1 h1 x hx, hreg 2 h2 x hx⟩,
    fun j hj y hy hyreg => ?_, fun z hz => ?_, hsum⟩
  · rw [hB, hIcc]
    simp [Finset.image_insert, Finset.image_singleton]
  · have hj' : j ∈ Finset.Icc 1 (5 - 1) := hj
    have hy' := (hcent y).mp hy
    obtain ⟨hχv, hψv⟩ := hval j hj' y hy' hyreg
    exact ⟨hχv, hψv 1 h1, hψv 2 h2⟩
  · obtain ⟨j, hj, y, hy, hyreg, hc⟩ := hconj z hz
    exact ⟨j, hj, y, (hcent y).mpr hy, hyreg, hc⟩

end CFSG.Semidihedral.Principal
