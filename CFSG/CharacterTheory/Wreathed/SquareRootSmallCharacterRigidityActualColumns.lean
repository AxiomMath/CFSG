module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityCentralizers
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityPrincipalColumns
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigiditySections

public noncomputable section

namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity

open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem zpowers_odd_power_eq {G : Type*} [Group G] {y : G} {a : ℕ}
    (hy : orderOf y = 2 ^ a) {h : ℤ} (hh : Odd h) :
    Subgroup.zpowers (y ^ h) = Subgroup.zpowers y := by
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers y h)
  · exact Subgroup.zpowers_le.mpr (CFSG.Wreathed.mem_zpowers_zpow_of_odd
      (by rw [← hy]; exact pow_orderOf_eq_one y) hh)

theorem orderOf_odd_power {G : Type*} [Group G] {y : G} {a : ℕ}
    (hy : orderOf y = 2 ^ a) {h : ℤ} (hh : Odd h) : orderOf (y ^ h) = 2 ^ a := by
  apply Nat.dvd_antisymm
  · rw [← hy]
    exact orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers y h)
  · rw [← hy]
    exact orderOf_dvd_of_mem_zpowers (CFSG.Wreathed.mem_zpowers_zpow_of_odd
      (by rw [← hy]; exact pow_orderOf_eq_one y) hh)

theorem original_principal_odd_power_column_off_section {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2 * 2 ^ n)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {h : ℤ} (hh : Odd h) (g : G) (hg : g ∉ squareRootSection y) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character (y ^ h) *
        starRingEnd ℂ ((basis.representation χ).character g) = 0 := by
  have hy2 : orderOf y = 2 ^ (n + 1) := by rw [hy, pow_succ, Nat.mul_comm]
  have hyh := orderOf_odd_power hy2 hh
  let C : Subgroup G := Subgroup.centralizer (Subgroup.zpowers (y ^ h) : Set G)
  have hC : C = Subgroup.centralizer ({y ^ h} : Set G) := by
    dsimp only [C]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hdata := maximal_root_centralizer_odd_complement n hn S e (y ^ h) (by
    rw [hyh, pow_succ, Nat.mul_comm])
  dsimp only at hdata
  have hneeded : ∃ (N : Subgroup (Subgroup.centralizer ({y ^ h} : Set G)))
      (_ : N.Normal), Odd (Nat.card N) ∧
      IsPGroup 2 ((Subgroup.centralizer ({y ^ h} : Set G)) ⧸ N) ∧
      IsCyclic ((Subgroup.centralizer ({y ^ h} : Set G)) ⧸ N) := by
    obtain ⟨N, hnormal, hN, _, _, _, _, hquot, hcyc, _⟩ := hdata
    exact ⟨N, hnormal, hN, hquot, hcyc⟩
  rw [← hC] at hneeded
  obtain ⟨N, hnormal, hN, hquot, hcyc⟩ := hneeded
  let : N.Normal := hnormal
  let : IsCyclic (C ⧸ N) := hcyc
  let localBasis : FiniteIrreducibleCharacterBasis C :=
    Classical.choice finiteIrreducibleCharacterBasis_exists
  obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
    finiteIrreducibleCharacterBasis_contains_irreducible localBasis
      (principalFiniteComplexRepresentation C)
      (principalFiniteComplexRepresentation_isIrreducible C)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  apply principal_value_column_off_section basis ideal principal hprincipal (by omega) hyh
    localBasis localPrincipal hlocalPrincipal N hN hquot g
  intro a c hproduct hcomm ⟨k, hk⟩ hc
  exact not_isConj_odd_power_of_not_mem_section hy2 hg hcomm hproduct
    (by rw [hk])
    (Nat.coprime_two_left.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hc)) hh

theorem original_integral_average_supported {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2 * 2 ^ n)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {κ : Type*} (K : Finset κ) (h : κ → ℤ) (hh : ∀ k ∈ K, Odd (h k))
    (c : basis.index → ℤ) (scale : ℂ) (T : G → ℂ)
    (hT : ∀ g, T g = ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (c χ : ℂ) * (basis.representation χ).character g)
    (hc : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (c χ : ℂ) = scale * ∑ k ∈ K, (basis.representation χ).character (y ^ h k)) :
    ∀ g ∉ squareRootSection y, T g = 0 := by
  exact integral_average_columns_support
    (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) K
    (fun χ => (basis.representation χ).character) (fun k => y ^ h k) c scale T hT hc
    (squareRootSection y) (fun g hg k hk =>
      original_principal_odd_power_column_off_section n hn S e y hy basis ideal
        principal hprincipal (hh k hk) g hg)

theorem original_fourier_average_supported {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (c : basis.index → ℤ) (T : G → ℂ)
    (hT : ∀ g, T g = ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (c χ : ℂ) * (basis.representation χ).character g)
    (hc : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (c χ : ℂ) = ((2 ^ n / 2 : ℕ) : ℂ)⁻¹ *
        ∑ k : Fin (2 ^ n / 2),
          (basis.representation χ).character (actualRoot S e ^ (2 * (k : ℤ) + 1))) :
    ∀ g ∉ squareRootSection (actualRoot S e), T g = 0 := by
  exact original_integral_average_supported n hn S e (actualRoot S e)
    (actualRoot_orderOf n hn S e) basis ideal principal hprincipal
    (Finset.univ : Finset (Fin (2 ^ n / 2))) (fun k => 2 * (k : ℤ) + 1)
    (fun k _ => ⟨(k : ℤ), rfl⟩) c (((2 ^ n / 2 : ℕ) : ℂ)⁻¹) T hT hc

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
