module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerCharacteristicValuation
public import CFSG.CharacterTheory.Semidihedral.SameParameterSections

public noncomputable section

namespace CFSG.Semidihedral.PerfectLayerNormalization

section ActualFourier

universe u v w z

open CFSG.Semidihedral.Principal
open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
open scoped BigOperators Classical

theorem original_actual_principal_fourier_theta_of_family {G : Type} [Group G] [Fintype G]
    (hindex : ∀ U : Subgroup G, U.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {t : G}
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq3 : 3 ≤ q) (hqodd : Odd q) (e : ℤ) (he : e = 1 ∨ e = -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index)
    (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    {S : Sylow 2 G} (presentation : SemidihedralGroup n ≃* (S : Subgroup G))
    (hcent : (presentation (r n) : G) ^ (modulus n / 2) = t) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : G := presentation (r n)
    let M := modulus n
    let Θ := principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x)
    Θ = 1 + (δ₁ : ℂ) • (basis.representation χ₁).character +
      (δ₂ : ℂ) • (basis.representation χ₂).character +
      (δ₃ : ℂ) • (basis.representation χ₃).character := by
  intro B ρ M Θ
  obtain ⟨hφ, hδ₁, hδ₂, hδ₃, -, hnd, -, -, -, -, -, hB, -, hodd, hsec, hrel⟩ := hfam
  obtain ⟨hφ1, y, hy, hyq⟩ :=
    family_character_nonconstant hnonab localBasis ideal localPrincipal q φ hφ
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    change c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hχ₁B := hmem χ₁ (by simp)
  have hχ₂B := hmem χ₂ (by simp)
  have hχ₃B := hmem χ₃ (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h01, h02, h03, -⟩, ⟨h12, h13, -⟩, ⟨h23, -⟩, -, -⟩ := hnd
  have hoddF : ∀ c ∈ B, (∃ d : ℕ, Odd d ∧ (basis.representation c).character 1 = d) ↔
      c = principal ∨ c = χ₁ ∨ c = χ₂ ∨ c = χ₃ := by
    intro c hc
    rw [← hodd c hc, (basis_character_one basis c).1]
    exact ⟨fun ⟨d, hd, hcd⟩ => Nat.cast_injective hcd ▸ hd, fun h => ⟨_, h, rfl⟩⟩
  let Φ : G → ℂ := fun g => if h : g ∈ C t then φ ⟨g, h⟩ else 0
  have hΦC : ∀ (g : G) (hg : g ∈ C t), Φ g = φ ⟨g, hg⟩ := fun g hg => by
    simp only [Φ, hg, dite_true]
  have hΦ : ∃ y₁ ∈ Subgroup.centralizer {ρ ^ (M / 2)},
      ∃ y₂ ∈ Subgroup.centralizer {ρ ^ (M / 2)},
        Odd (orderOf y₁) ∧ Odd (orderOf y₂) ∧ Φ y₁ ≠ Φ y₂ := by
    change ∃ y₁ ∈ Subgroup.centralizer {(presentation (r n) : G) ^ (modulus n / 2)},
      ∃ y₂ ∈ Subgroup.centralizer {(presentation (r n) : G) ^ (modulus n / 2)}, _
    rw [hcent]
    refine ⟨1, one_mem _, y, y.property, by simp, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact hy
    · rw [hΦC 1 (one_mem _), show (⟨1, (one_mem (C t))⟩ : C t) = 1 from rfl,
        hφ1, hΦC y y.property]
      exact Ne.symm hyq
  have hΦ1 : Φ 1 = q := (hΦC 1 (one_mem _)).trans hφ1
  have hχ₁t : ∀ g ∈ Subgroup.centralizer {ρ ^ (M / 2)}, Odd (orderOf g) →
      (basis.representation χ₁).character (ρ ^ (M / 2) * g) = δ₁ * e * Φ g := by
    change ∀ g ∈ Subgroup.centralizer {(presentation (r n) : G) ^ (modulus n / 2)}, _
    rw [hcent]
    intro g hg hgo
    rw [hΦC g hg]
    exact (hsec ⟨g, hg⟩ (by rw [Subgroup.orderOf_mk]; exact hgo)).1
  have hχ₂t : ∀ g ∈ Subgroup.centralizer {ρ ^ (M / 2)}, Odd (orderOf g) →
      (basis.representation χ₂).character (ρ ^ (M / 2) * g) = -δ₂ * e * Φ g := by
    change ∀ g ∈ Subgroup.centralizer {(presentation (r n) : G) ^ (modulus n / 2)}, _
    rw [hcent]
    intro g hg hgo
    rw [hΦC g hg, (hsec ⟨g, hg⟩ (by rw [Subgroup.orderOf_mk]; exact hgo)).2.1]
    ring
  have hχ₃t : ∀ g ∈ Subgroup.centralizer {ρ ^ (M / 2)}, Odd (orderOf g) →
      (basis.representation χ₃).character (ρ ^ (M / 2) * g) = -δ₃ := by
    change ∀ g ∈ Subgroup.centralizer {(presentation (r n) : G) ^ (modulus n / 2)}, _
    rw [hcent]
    intro g hg hgo
    exact (hsec ⟨g, hg⟩ (by rw [Subgroup.orderOf_mk]; exact hgo)).2.2.1
  obtain ⟨-, -, hrel1, -⟩ := hrel 1 (by simp)
  have hdeg : 1 + δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) +
      δ₂ * Module.finrank ℂ (basis.representation χ₂).vector +
      δ₃ * Module.finrank ℂ (basis.representation χ₃).vector = 0 := by
    rw [(basis_character_one basis χ₁).1, (basis_character_one basis χ₂).1,
      (basis_character_one basis χ₃).1] at hrel1
    exact_mod_cast hrel1
  exact (nonsimple_principal_Fourier_odd_degree_product hindex hn presentation basis ideal
    principal hprincipal χ₁ χ₂ χ₃ hχ₁B hχ₂B hχ₃B h01 h02 h03 h12 h13 h23 hoddF _ _ _
      (basis_character_one basis χ₁).1 (basis_character_one basis χ₂).1
      (basis_character_one basis χ₃).1 q hq3 hqodd e δ₁ δ₂ δ₃ he hδ₁ hδ₂ hδ₃ Φ hΦ hΦ1
      hχ₁t hχ₂t hχ₃t hdeg).2.1

theorem original_regular_principal_fourier_theta {G : Type} [Group G] [Fintype G]
    (hindex : ∀ U : Subgroup G, U.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {t : G}
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq3 : 3 ≤ q) (hqodd : Odd q) (e : ℤ) (he : e = 1 ∨ e = -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index)
    (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    {S : Sylow 2 G} (presentation : SemidihedralGroup n ≃* (S : Subgroup G))
    (hcent : (presentation (r n) : G) ^ (modulus n / 2) = t) (p : ℕ)
    (hvalues : ActualPrincipalCharacteristicValues basis t (presentation (s n) : G) p q
      (2 ^ (n - 3)) e δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : G := presentation (r n)
    let M := modulus n
    let Θ := principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x)
    Θ = 1 + (e : ℂ) • (basis.representation χ₁).character -
      (basis.representation χ₂).character - (e : ℂ) • (basis.representation χ₃).character := by
  have hΘ := original_actual_principal_fourier_theta_of_family hindex hn hnonab basis ideal
    principal hprincipal localBasis localPrincipal q hq3 hqodd e he φ δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν hfam presentation hcent
  rw [hvalues.1, hvalues.2.1, hvalues.2.2.1] at hΘ
  simpa only [Int.cast_neg, Int.cast_one, neg_smul, one_smul, sub_eq_add_neg] using hΘ

theorem original_regular_even_fourier_family {G : Type} [Group G] [Fintype G]
    (hindex : ∀ U : Subgroup G, U.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {t : G}
    (ht : orderOf t = 2) [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq3 : 3 ≤ q) (hqodd : Odd q) (e : ℤ) (he : e = 1 ∨ e = -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index)
    (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    {S : Sylow 2 G} (presentation : SemidihedralGroup n ≃* (S : Subgroup G))
    (hcent : (presentation (r n) : G) ^ (modulus n / 2) = t) (p : ℕ)
    (hvalues : ActualPrincipalCharacteristicValues basis t (presentation (s n) : G) p q
      (2 ^ (n - 3)) e δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : G := presentation (r n)
    let M := modulus n
    let K := Finset.Icc 1 (2 ^ (n - 3) - 1)
    let E := fun l : ℕ => principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
    ∃ σ : {l // l ∈ K} ≃ {j // j ∈ K}, ∀ l : {l // l ∈ K},
      E l = 1 + (e : ℂ) • (basis.representation χ₁).character -
        (e : ℂ) • (basis.representation (ψ (σ l))).character := by
  intro B ρ M K E
  have hΘ := original_actual_principal_fourier_theta_of_family hindex hn hnonab basis ideal
    principal hprincipal localBasis localPrincipal q hq3 hqodd e he φ δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν hfam presentation hcent
  obtain ⟨hlφ, hδ₁, hδ₂, hδ₃, -, hnd, -, -, -, -, -, hB, -, hodd, hsec, -⟩ := hfam
  obtain ⟨hφ1, -⟩ := family_character_nonconstant hnonab localBasis ideal localPrincipal q φ hlφ
  let χ : basis.index → G → ℂ := fun c => (basis.representation c).character
  have hpB : principal ∈ B := coefficientBlock_self_mem _ _ _
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    change c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hχ₁B : χ₁ ∈ B := hmem χ₁ (by simp)
  have hχ₂B : χ₂ ∈ B := hmem χ₂ (by simp)
  have hχ₃B : χ₃ ∈ B := hmem χ₃ (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h01, h02, h03, -⟩, ⟨h12, h13, -⟩, ⟨h23, -⟩, -, -⟩ := hnd
  have hδ₄' : δ₄ = -δ₂ := by rw [hvalues.2.2.2.1, hvalues.2.1]; norm_num
  obtain ⟨-, -, hΘapply, -, -, hE1, -, -, -, -, -, -, -, -, -, -,
    c₁', c₂', c₃', δ₁', δ₂', δ₃', εe, ψ', hc₁', -, -, h12', h13', -, hc₁p', -, -,
    hδ₁', -, -, -, hψinj', hψmem', -, hEeq, hθcoef, hηcoef, -, -, hne0, -, hεsign⟩ :=
    even_cyclic_principal_Fourier_family hn presentation basis ideal principal hprincipal
  beta_reduce at hΘapply hEeq hθcoef hηcoef hE1 hne0 hεsign
  set L := multiplicityColumn basis (presentation (r n) : G) (modulus n)
  obtain ⟨hM4, hkeven, hk2, hhalf⟩ := modulus_eq_four_mul hn
  have hθours : ∀ c ∈ B, L 0 c - L ((modulus n / 2 : ℕ) : ℤ) c =
      (if c = principal then 1 else 0) + δ₁ * (if c = χ₁ then 1 else 0) +
        δ₂ * (if c = χ₂ then 1 else 0) + δ₃ * (if c = χ₃ then 1 else 0) := by
    intro c hc
    have h := coefficient_eq_of_combination_eq basis
      (fun d => ((L 0 d - L ((modulus n / 2 : ℕ) : ℤ) d : ℤ) : ℂ))
      (fun d => (((if d = principal then 1 else 0) + δ₁ * (if d = χ₁ then 1 else 0) +
        δ₂ * (if d = χ₂ then 1 else 0) + δ₃ * (if d = χ₃ then 1 else 0) : ℤ) : ℂ)) (by
          funext g
          rw [← hΘapply g, hΘ]
          simp [Finset.sum_add_distrib, add_mul, Finset.sum_ite_eq', hpB, hχ₁B, hχ₂B, hχ₃B,
            hprincipal]) hc
    exact_mod_cast h
  have hεe' : εe = -δ₁' := by
    rw [(basis_character_one basis c₁').1] at hεsign hne0
    rw [hεsign]
    exact neg_sign_one_add_mul_eq hδ₁' (basis_character_one basis c₁').2 hne0
  have hc₁'match : (c₁' = χ₁ ∧ δ₁' = δ₁) ∨ (c₁' = χ₂ ∧ δ₁' = δ₂) ∨ (c₁' = χ₃ ∧ δ₁' = δ₃) := by
    have h1 : δ₁' = (if c₁' = principal then 1 else 0) + δ₁ * (if c₁' = χ₁ then 1 else 0) +
        δ₂ * (if c₁' = χ₂ then 1 else 0) + δ₃ * (if c₁' = χ₃ then 1 else 0) := by
      rw [← hθours c₁' hc₁', hθcoef c₁' hc₁']
      simp [hc₁p', h12', h13']
    exact eq_of_coefficient_ne_zero (by rcases hδ₁' with h | h <;> omega) hc₁p' h12 h13 h23 h1
  have hsec1 := hsec 1 (by simp)
  simp only [OneMemClass.coe_one, mul_one, hφ1] at hsec1
  obtain ⟨hχ₁tv, hχ₂tv, hχ₃tv, hχ₄tv, hψtv, hνtv⟩ := hsec1
  obtain ⟨-, hvodd, hvinv⟩ :=
    cyclic_principal_Fourier_projection_values hn presentation basis ideal principal hprincipal
  beta_reduce at hvodd hvinv
  have hk1 : 1 ≤ modulus n / 4 - 1 := by omega
  have hψ'deg : ∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 →
      ¬ Odd (Module.finrank ℂ (basis.representation (ψ' l)).vector) := by
    intro l hl1 hl2 hodd'
    have h := hE1 l hl1 hl2
    rw [hEeq l hl1 hl2, hεe'] at h
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at h
    rw [(basis_character_one basis c₁').1, (basis_character_one basis (ψ' l)).1] at h
    have hc₁'odd : Odd (Module.finrank ℂ (basis.representation c₁').vector) := by
      rw [hodd c₁' hc₁']
      rcases hc₁'match with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> simp [h']
    have hZ : (1 : ℤ) + δ₁' * (Module.finrank ℂ (basis.representation c₁').vector : ℤ) -
        δ₁' * (Module.finrank ℂ (basis.representation (ψ' l)).vector : ℤ) = 0 := by
      have h' : ((1 + δ₁' * (Module.finrank ℂ (basis.representation c₁').vector : ℤ) -
          δ₁' * (Module.finrank ℂ (basis.representation (ψ' l)).vector : ℤ) : ℤ) : ℂ) = 0 := by
        push_cast at h ⊢
        linear_combination h
      exact_mod_cast h'
    obtain ⟨a, ha⟩ := hc₁'odd
    obtain ⟨b, hb⟩ := hodd'
    rcases hδ₁' with h1 | h1 <;> rw [h1] at hZ <;> omega
  have hzt : (presentation (z n) : G) = t := by
    rw [← hcent]
    show ((presentation (r n ^ half n) : (S : Subgroup G)) : G) = _
    rw [map_pow, SubmonoidClass.coe_pow]
    congr 1
    show 2 ^ (n - 2) = modulus n / 2
    omega
  have htS : t ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← hzt]
    have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn))
      (presentation.symm ⟨x, hx⟩)
    have h' := congrArg (fun w => ((presentation w : (S : Subgroup G)) : G)) h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnv : ∀ c ∈ B, χ c t ≠ 0 := fun c hc =>
    CFSG.LyonsUnitaryFour.principal_block_character_ne_zero_of_centralizes_sylow basis ideal 2
      principal hprincipal c hc S t htS
  have hψ'1B : ψ' 1 ∈ B := (hψmem' 1 le_rfl hk1).1
  have hψ'1 : ψ' 1 ≠ principal ∧ ψ' 1 ≠ χ₁ ∧ ψ' 1 ≠ χ₂ ∧ ψ' 1 ≠ χ₃ := by
    have h := hψ'deg 1 le_rfl hk1
    rw [hodd _ hψ'1B] at h
    push Not at h
    exact h
  have hEt := (hvinv t t 1 (mul_one t) (Commute.one_right t) ht
    (by rw [orderOf_one]; exact odd_one)).2.1 1 le_rfl hk1
  rw [hEeq 1 le_rfl hk1, hεe'] at hEt
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at hEt
  have heq0 : (e : ℂ) * q ≠ 1 := by
    intro h
    have h' : e * (q : ℤ) = 1 := by exact_mod_cast h
    rcases he with rfl | rfl <;> omega
  have hc₁'χ₁ : c₁' = χ₁ ∧ δ₁' = δ₁ := by
    rcases hc₁'match with h | ⟨hc, hδ⟩ | ⟨hc, hδ⟩
    · exact h
    ·
      exfalso
      rw [hc, hδ] at hEt
      have hsq : (δ₂ : ℂ) * δ₂ = 1 := by rcases hδ₂ with h | h <;> rw [h] <;> norm_num
      have hval : (basis.representation (ψ' 1)).character t = δ₂ * (1 - e * q) := by
        have h := hEt
        rw [hχ₂tv] at h
        push_cast at h
        linear_combination (-(δ₂ : ℂ)) * h - ((basis.representation (ψ' 1)).character t +
          δ₂ * e * q) * hsq
      have hψ'list : ψ' 1 ∈ ({principal, χ₁, χ₂, χ₃, χ₄} ∪
          (Finset.Icc 1 (2 ^ (n - 3) - 1)).image ψ ∪ (Finset.range (2 ^ (n - 3))).image ν :
            Finset basis.index) := hB ▸ hψ'1B
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_image] at hψ'list
      obtain ⟨hp', h1', h2', h3'⟩ := hψ'1
      have hint : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
          ((a * (1 + e * q) : ℤ) : ℂ) ≠ ((b * (1 - e * q) : ℤ) : ℂ) := by
        intro a b ha hb h
        have h' : a * (1 + e * (q : ℤ)) = b * (1 - e * q) := by exact_mod_cast h
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases he with rfl | rfl <;>
          omega
      rcases hψ'list with ((h | h | h | h | h) | ⟨j, hj, hjeq⟩) | ⟨i, hi, hieq⟩
      · exact hp' h
      · exact h1' h
      · exact h2' h
      · exact h3' h
      · rw [h, hχ₄tv, hδ₄'] at hval
        have hZ : ((-δ₂ * (1 - e * q) : ℤ) : ℂ) = ((δ₂ * (1 - e * q) : ℤ) : ℂ) := by
          push_cast at hval ⊢
          exact hval
        have hZ' : -δ₂ * (1 - e * (q : ℤ)) = δ₂ * (1 - e * q) := by exact_mod_cast hZ
        rcases hδ₂ with rfl | rfl <;> rcases he with rfl | rfl <;> omega
      · rw [← hjeq, hψtv j hj] at hval
        exact hint δ₁ δ₂ hδ₁ hδ₂ (by push_cast; exact hval)
      · rw [← hieq, hνtv i hi] at hval
        exact hint (-δ₁) δ₂ (by rcases hδ₁ with h | h <;> rw [h] <;> norm_num) hδ₂
          (by push_cast; linear_combination hval)
    ·
      exfalso
      apply hnv (ψ' 1) hψ'1B
      rw [hc, hδ] at hEt
      have hsq : (δ₃ : ℂ) * δ₃ = 1 := by rcases hδ₃ with h | h <;> rw [h] <;> norm_num
      have h := hEt
      rw [hχ₃tv] at h
      push_cast at h
      show (basis.representation (ψ' 1)).character t = 0
      linear_combination (-(δ₃ : ℂ)) * h - ((basis.representation (ψ' 1)).character t + δ₃) * hsq
  obtain ⟨hc₁'eq, hδ₁'eq⟩ := hc₁'χ₁
  have hψ'avoid : ∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 →
      ψ' l ≠ principal ∧ ψ' l ≠ χ₁ ∧ ψ' l ≠ χ₂ ∧ ψ' l ≠ χ₃ := by
    intro l hl1 hl2
    have h := hψ'deg l hl1 hl2
    rw [hodd _ (hψmem' l hl1 hl2).1] at h
    push Not at h
    exact h
  have hψ'match : ∀ l : ℕ, l ∈ K → ∃ j ∈ K, ψ' l = ψ j := by
    intro l hl
    obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
    have hl2' : l ≤ modulus n / 4 - 1 := by omega
    obtain ⟨hp', h1', h2', h3'⟩ := hψ'avoid l hl1 hl2'
    have hEt := (hvinv t t 1 (mul_one t) (Commute.one_right t) ht
      (by rw [orderOf_one]; exact odd_one)).2.1 l hl1 hl2'
    rw [hEeq l hl1 hl2', hεe', hc₁'eq, hδ₁'eq] at hEt
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at hEt
    have hsq : (δ₁ : ℂ) * δ₁ = 1 := by rcases hδ₁ with h | h <;> rw [h] <;> norm_num
    have hval : (basis.representation (ψ' l)).character t = δ₁ * (1 + e * q) := by
      rw [hχ₁tv] at hEt
      push_cast at hEt
      linear_combination (-(δ₁ : ℂ)) * hEt -
        ((basis.representation (ψ' l)).character t - δ₁ * e * q) * hsq
    have hlist : ψ' l ∈ ({principal, χ₁, χ₂, χ₃, χ₄} ∪
        (Finset.Icc 1 (2 ^ (n - 3) - 1)).image ψ ∪
          (Finset.range (2 ^ (n - 3))).image ν : Finset basis.index) :=
      hB ▸ (hψmem' l hl1 hl2').1
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image] at hlist
    rcases hlist with ((h | h | h | h | h) | ⟨j, hj, hjeq⟩) | ⟨i, hi, hieq⟩
    · exact (hp' h).elim
    · exact (h1' h).elim
    · exact (h2' h).elim
    · exact (h3' h).elim
    · exfalso
      rw [h, hχ₄tv, hvalues.1, hvalues.2.2.2.1] at hval
      simp only [Int.cast_one, one_mul] at hval
      have hZ : 1 - e * (q : ℤ) = e * (1 + e * q) := by exact_mod_cast hval
      rcases he with rfl | rfl <;> omega
    · exact ⟨j, hj, hjeq.symm⟩
    · exfalso
      rw [← hieq, hνtv i hi, hvalues.1] at hval
      have hZ : -(e * (1 + e * (q : ℤ))) = e * (1 + e * q) := by exact_mod_cast hval
      rcases he with rfl | rfl <;> omega
  let f : {l // l ∈ K} → {j // j ∈ K} := fun l =>
    ⟨Classical.choose (hψ'match l l.property), (Classical.choose_spec
      (hψ'match l l.property)).1⟩
  have hf : ∀ l : {l // l ∈ K}, ψ' l = ψ (f l) := fun l =>
    (Classical.choose_spec (hψ'match l l.property)).2
  have hfinj : Function.Injective f := by
    intro l k hlk
    apply Subtype.ext
    apply hψinj' l k (Finset.mem_Icc.mp l.property).1 (by
      have := (Finset.mem_Icc.mp l.property).2
      omega) (Finset.mem_Icc.mp k.property).1 (by
      have := (Finset.mem_Icc.mp k.property).2
      omega)
    rw [hf l, hf k, hlk]
  let σ := Equiv.ofBijective f ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  refine ⟨σ, fun l => ?_⟩
  change E l = 1 + (e : ℂ) • (basis.representation χ₁).character -
    (e : ℂ) • (basis.representation (ψ (f l))).character
  have hl := Finset.mem_Icc.mp l.property
  have hl2 : (l : ℕ) ≤ modulus n / 4 - 1 := by omega
  have h := hEeq l hl.1 hl2
  rw [hεe', hc₁'eq, hδ₁'eq, hvalues.1, hf l] at h
  simpa only [Int.cast_neg, neg_smul, sub_eq_add_neg, E, B, ρ, M] using h

theorem original_regular_odd_fourier_family {G : Type} [Group G] [Fintype G]
    (hindex : ∀ U : Subgroup G, U.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {t : G}
    (ht : orderOf t = 2) [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq3 : 3 ≤ q) (hqodd : Odd q) (e : ℤ) (he : e = 1 ∨ e = -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index)
    (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    {S : Sylow 2 G} (presentation : SemidihedralGroup n ≃* (S : Subgroup G))
    (hcent : (presentation (r n) : G) ^ (modulus n / 2) = t) (p : ℕ)
    (hvalues : ActualPrincipalCharacteristicValues basis t (presentation (s n) : G) p q
      (2 ^ (n - 3)) e δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (I : Finset (ZMod (modulus n)))
    (hI : IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : G := presentation (r n)
    let M := modulus n
    let F := fun j : ZMod M => principalCyclicProjection basis B ρ
      (fun x => cyclicLinearCharacter ρ M j.val x - cyclicLinearCharacter ρ M 1 x)
    ∃ (ε : ℤ) (σ : {j // j ∈ I} ≃ {i // i ∈ Finset.range (2 ^ (n - 3))}),
      (ε = 1 ∨ ε = -1) ∧ ∀ j : {j // j ∈ I},
        F j = (ε : ℂ) • ((basis.representation (ν (σ j))).character -
          (basis.representation (ν (σ ⟨1, hI.one_mem⟩))).character) := by
  intro B ρ M F
  obtain ⟨σe, hEe⟩ := original_regular_even_fourier_family hindex hn ht hnonab basis ideal
    principal hprincipal localBasis localPrincipal q hq3 hqodd e he φ δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν hfam presentation hcent p hvalues
  have hΘ := original_actual_principal_fourier_theta_of_family hindex hn hnonab basis ideal
    principal hprincipal localBasis localPrincipal q hq3 hqodd e he φ δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν hfam presentation hcent
  obtain ⟨hφ, hδ₁, hδ₂, hδ₃, -, hnd, hψinj, -, hψavoid, -, -, hB, -, -, hsec, -⟩ := hfam
  let K := Finset.Icc 1 (2 ^ (n - 3) - 1)
  let ψe : ℕ → basis.index := fun l => if h : l ∈ K then ψ (σe ⟨l, h⟩) else principal
  have hψe : ∀ l (hl : l ∈ K), ψe l = ψ (σe ⟨l, hl⟩) := fun l hl => dite_eq_left hl
  obtain ⟨hM4, -, hk2, -⟩ := modulus_eq_four_mul hn
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    change c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hχ₁B : χ₁ ∈ B := hmem χ₁ (by simp)
  have hχ₂B : χ₂ ∈ B := hmem χ₂ (by simp)
  have hχ₃B : χ₃ ∈ B := hmem χ₃ (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h01, h02, h03, -⟩, ⟨h12, h13, -⟩, ⟨h23, -⟩, -, -⟩ := hnd
  have hψeinj : ∀ j l : ℕ, 1 ≤ j → j ≤ modulus n / 4 - 1 → 1 ≤ l →
      l ≤ modulus n / 4 - 1 → ψe j = ψe l → j = l := by
    intro j l hj1 hj2 hl1 hl2 h
    have hj : j ∈ K := Finset.mem_Icc.mpr ⟨hj1, by omega⟩
    have hl : l ∈ K := Finset.mem_Icc.mpr ⟨hl1, by omega⟩
    rw [hψe j hj, hψe l hl] at h
    have hσ : σe ⟨j, hj⟩ = σe ⟨l, hl⟩ :=
      Subtype.ext (hψinj (σe ⟨j, hj⟩).property (σe ⟨l, hl⟩).property h)
    exact congrArg Subtype.val (σe.injective hσ)
  have hψemem : ∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 →
      ψe l ∈ B ∧ ψe l ≠ principal ∧ ψe l ≠ χ₁ ∧ ψe l ≠ χ₂ ∧ ψe l ≠ χ₃ := by
    intro l hl1 hl2
    have hl : l ∈ K := Finset.mem_Icc.mpr ⟨hl1, by omega⟩
    rw [hψe l hl]
    have hσ := (σe ⟨l, hl⟩).property
    refine ⟨?_, (hψavoid _ hσ).1, (hψavoid _ hσ).2.1,
      (hψavoid _ hσ).2.2.1, (hψavoid _ hσ).2.2.2.1⟩
    change ψ (σe ⟨l, hl⟩) ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨_, hσ, rfl⟩))
  have hEeq : ∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 →
      principalCyclicProjection basis B ρ
        (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x) =
          1 + (δ₁ : ℂ) • (basis.representation χ₁).character +
            ((-e : ℤ) : ℂ) • (basis.representation (ψe l)).character := by
    intro l hl1 hl2
    have hl : l ∈ K := Finset.mem_Icc.mpr ⟨hl1, by omega⟩
    rw [hvalues.1, hψe l hl]
    simpa only [Int.cast_neg, neg_smul, sub_eq_add_neg] using hEe ⟨l, hl⟩
  obtain ⟨hIcard, -, -, -, -, -, -, -, -, -, -, εo, ν', dν, hεo, -, hνinj', hνmem',
    hfeq, -, havoid⟩ := odd_cyclic_principal_Fourier_family hn presentation basis ideal
      principal hprincipal I hI
  beta_reduce at hνmem' hfeq havoid
  obtain ⟨havoid1, havoid5, havoid4⟩ := havoid χ₁ χ₂ χ₃ δ₁ δ₂ δ₃ (-e) ψe
    hχ₁B hχ₂B hχ₃B h12 h13 h23 (Ne.symm h01) (Ne.symm h02) (Ne.symm h03)
      hδ₁ hδ₂ hδ₃ (by rcases he with h | h <;> rw [h] <;> norm_num)
        hψeinj hψemem hΘ hEeq
  have havoid23 : ∀ j ∈ I, ν' j ≠ χ₂ ∧ ν' j ≠ χ₃ := by
    by_cases hn5 : 5 ≤ n
    · exact (havoid5 hn5).1
    have hn4 : n = 4 := by omega
    rcases havoid4 hn4 with h | ⟨himage, -, -⟩
    · exact h
    exfalso
    have h2 : χ₂ ∈ I.image ν' := by rw [himage]; simp
    have h3 : χ₃ ∈ I.image ν' := by rw [himage]; simp
    obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp h2
    obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.mp h3
    have hdeg : (basis.representation χ₂).character 1 =
        (basis.representation χ₃).character 1 := by
      rw [← hjeq, ← hkeq, (hνmem' j hj).2.2, (hνmem' k hk).2.2]
    rw [(basis_character_one basis χ₂).1, (basis_character_one basis χ₃).1] at hdeg
    have hval2 := hvalues.2.2.2.2.2.1
    have hval3 := hvalues.2.2.2.2.2.2.1
    have hdegZ : (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) =
        Module.finrank ℂ (basis.representation χ₃).vector := by exact_mod_cast hdeg
    rw [hval2, hval3] at hdegZ
    have hqZ : (3 : ℤ) ≤ q := by exact_mod_cast hq3
    rcases he with rfl | rfl <;> nlinarith [sq_nonneg ((q : ℤ) - 1)]
  have hν'match : ∀ j ∈ I, ∃ i ∈ Finset.range (2 ^ (n - 3)), ν' j = ν i := by
    intro j hj
    have hp' := (hνmem' j hj).2.1
    have h1' := (havoid1 j hj).1
    obtain ⟨h2', h3'⟩ := havoid23 j hj
    have hlist : ν' j ∈ ({principal, χ₁, χ₂, χ₃, χ₄} ∪ K.image ψ ∪
        (Finset.range (2 ^ (n - 3))).image ν : Finset basis.index) :=
      hB ▸ (hνmem' j hj).1
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image] at hlist
    rcases hlist with ((h | h | h | h | h) | ⟨l, hl, hleq⟩) | ⟨i, hi, hieq⟩
    · exact (hp' h).elim
    · exact (h1' h).elim
    · exact (h2' h).elim
    · exact (h3' h).elim
    · exfalso
      have hν't : ∀ k ∈ I, (basis.representation (ν' k)).character t =
          (basis.representation χ₄).character t := by
        intro k hk
        have hodd : Odd ((k.val : ℕ) : ℤ) := by exact_mod_cast hI.odd k hk
        have hf := (cyclic_principal_Fourier_projection_values hn presentation basis ideal
          principal hprincipal).2.2 t t 1 (mul_one t) (Commute.one_right t) ht
            (by rw [orderOf_one]; exact odd_one)
        have hh := hf.2.2 _ hodd
        beta_reduce at hh
        rw [hfeq k hk] at hh
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hh
        have hε0 : (εo : ℂ) ≠ 0 := by rcases hεo with h | h <;> rw [h] <;> norm_num
        have hv := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hε0)
        have hbase := (cyclic_principal_Fourier_projection_values hn presentation basis ideal
          principal hprincipal).2.2 t t 1 (mul_one t) (Commute.one_right t) ht
            (by rw [orderOf_one]; exact odd_one)
        have hjodd : Odd ((j.val : ℕ) : ℤ) := by exact_mod_cast hI.odd j hj
        have hhb := hbase.2.2 _ hjodd
        beta_reduce at hhb
        rw [hfeq j hj] at hhb
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hhb
        have hvb := sub_eq_zero.mp ((mul_eq_zero.mp hhb).resolve_left hε0)
        exact hv.trans (hvb.symm.trans (congrArg (fun c => (basis.representation c).character t) h))
      have hcard : 1 < I.card := by rw [hIcard]; omega
      obtain ⟨k, hk, hkj⟩ := Finset.exists_mem_ne hcard j
      have hne : ν' k ≠ χ₄ := fun heq => hkj (hνinj' k hk j hj (heq.trans h.symm))
      have hlistk : ν' k ∈ ({principal, χ₁, χ₂, χ₃, χ₄} ∪ K.image ψ ∪
          (Finset.range (2 ^ (n - 3))).image ν : Finset basis.index) :=
        hB ▸ (hνmem' k hk).1
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_image] at hlistk
      have hlψ : ∀ l ∈ K, ν' k ≠ ψ l := by
        intro l hl heq
        let a := σe.symm ⟨l, hl⟩
        have ha := a.property
        have hae : ψe a = ψ l := by
          rw [hψe a ha]
          exact congrArg (fun z => ψ z.val) (σe.apply_symm_apply ⟨l, hl⟩)
        exact ((havoid1 k hk).2 a (Finset.mem_Icc.mp ha).1 (by
          have := (Finset.mem_Icc.mp ha).2
          omega)) (heq.trans hae.symm)
      rcases hlistk with ((hk0 | hk1 | hk2 | hk3 | hk4) | ⟨l, hl, heq⟩) |
        ⟨i, hi, heq⟩
      · exact (hνmem' k hk).2.1 hk0
      · exact (havoid1 k hk).1 hk1
      · exact (havoid23 k hk).1 hk2
      · exact (havoid23 k hk).2 hk3
      · exact hne hk4
      · exact hlψ l hl heq.symm
      · have hv := hν't k hk
        obtain ⟨hφ1, -⟩ := family_character_nonconstant hnonab localBasis ideal localPrincipal
          q φ hφ
        have hrow := hsec 1 (by simp)
        simp only [OneMemClass.coe_one, mul_one, hφ1] at hrow
        rw [← heq, hrow.2.2.2.2.2 i hi, hrow.2.2.2.1, hvalues.1,
          hvalues.2.2.2.1] at hv
        simp only [Int.cast_one, one_mul] at hv
        have hvZ : -(e * (1 + e * (q : ℤ))) = 1 - e * q := by exact_mod_cast hv
        rcases he with rfl | rfl <;> omega
    · exfalso
      let a := σe.symm ⟨l, hl⟩
      have ha := a.property
      have hae : ψe a = ψ l := by
        rw [hψe a ha]
        exact congrArg (fun z => ψ z.val) (σe.apply_symm_apply ⟨l, hl⟩)
      exact ((havoid1 j hj).2 a (Finset.mem_Icc.mp ha).1 (by
        have := (Finset.mem_Icc.mp ha).2
        omega)) (hleq.symm.trans hae.symm)
    · exact ⟨i, hi, hieq.symm⟩
  let f : {j // j ∈ I} → {i // i ∈ Finset.range (2 ^ (n - 3))} := fun j =>
    ⟨Classical.choose (hν'match j j.property), (Classical.choose_spec
      (hν'match j j.property)).1⟩
  have hf : ∀ j : {j // j ∈ I}, ν' j = ν (f j) := fun j =>
    (Classical.choose_spec (hν'match j j.property)).2
  have hfinj : Function.Injective f := by
    intro j k heq
    apply Subtype.ext
    apply hνinj' j j.property k k.property
    rw [hf j, hf k, heq]
  let : Fintype {i : ℕ // i ∈ Finset.range (2 ^ (n - 3))} := Fintype.ofFinite _
  have hcard : Fintype.card {j : ZMod (modulus n) // j ∈ I} =
      Fintype.card {i : ℕ // i ∈ Finset.range (2 ^ (n - 3))} := by
    rw [Fintype.card_coe, Fintype.card_coe, Finset.card_range, hIcard]
    omega
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hfinj, hcard⟩
  let σ := Equiv.ofBijective f hbij
  refine ⟨εo, σ, hεo, fun j => ?_⟩
  change F j = (εo : ℂ) • ((basis.representation (ν (f j))).character -
    (basis.representation (ν (f ⟨1, hI.one_mem⟩))).character)
  have h := hfeq j j.property
  rw [hf j, hf ⟨1, hI.one_mem⟩] at h
  exact h

theorem original_cyclic_projection_rotation_section_support {G : Type u}
    [Group G] [Fintype G] {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (presentation : SemidihedralGroup n ≃* (S : Subgroup G))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (f : Subgroup.zpowers (presentation (r n) : G) → ℂ) (h1 : f 1 = 0)
    (ht : f ⟨(presentation (r n) : G) ^ (modulus n / 2),
      Subgroup.npow_mem_zpowers _ _⟩ = 0) :
    ∀ x ∉ SameParameterSections.rotationSections presentation,
      principalCyclicProjection basis (coefficientBlock basis
        (localizedComplexIntegerRing ideal) principal) (presentation (r n) : G) f x = 0 := by
  intro x hx
  refine principalCyclicProjection_eq_zero_of_inv_columns hn presentation basis _ h1 ht
    fun w hw0 hw1 => ?_
  refine (noncentral_rotation_principal_section_columns hn presentation basis ideal
    principal hprincipal).2.2.1 w hw0 hw1 x⁻¹ fun a c hac hacomm ha hc hconj => ?_
  apply hx
  have hnw := noncentral_neg hn hw0 hw1
  refine ⟨-w, hnw.1, hnw.2, a⁻¹, c⁻¹, ?_⟩
  obtain ⟨k, hk⟩ := ha
  refine ⟨k, ?_, hacomm.inv_inv, by rw [orderOf_inv]; exact hk,
    by rw [orderOf_inv]; exact hc, ?_⟩
  · rw [← mul_inv_rev, ← hacomm.eq, hac, inv_inv]
  · obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    refine isConj_iff.mpr ⟨g, ?_⟩
    rw [zpow_neg, ← hg]
    group

theorem original_fourier_rotation_sections {G : Type u} [Group G] [Fintype G]
    {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (presentation : SemidihedralGroup n ≃* (S : Subgroup G))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : G := presentation (r n)
    let M := modulus n
    let a : ℤ := ((M / 2 : ℕ) : ℤ) - 1
    let ζ : ℂ := cyclicRoot M
    let Θ := principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x)
    let E := fun l : ℕ => principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
    let F := fun j : ℤ => principalCyclicProjection basis B ρ
      (fun x => cyclicLinearCharacter ρ M j x - cyclicLinearCharacter ρ M 1 x)
    (∀ x ∉ SameParameterSections.rotationSections presentation,
      Θ x = 0 ∧ (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → E l x = 0) ∧
        ∀ j : ℤ, Odd j → F j x = 0) ∧
    (∀ v : ℤ, ¬ v ≡ 0 [ZMOD M] → ¬ v ≡ (M / 2 : ℕ) [ZMOD M] →
      ∀ x ∈ SameParameterSections.twoSection (ρ ^ v),
        Θ x = 2 - 2 * (-1 : ℂ) ^ v ∧
        (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 →
          E l x = 2 - ζ ^ (2 * (l : ℤ) * v) - ζ ^ (-(2 * (l : ℤ) * v))) ∧
        ∀ j : ℤ, Odd j → F j x = ζ ^ (j * v) + ζ ^ (a * j * v) - ζ ^ v - ζ ^ (a * v)) := by
  intro B ρ M a ζ Θ E F
  have hord : orderOf ρ = M := suppliedRotation_orderOf (by omega) presentation
  have hlam1 : ∀ j : ℤ, cyclicLinearCharacter ρ M j 1 = 1 := fun j =>
    cyclicLinearCharacter_one hord j
  have hlamt : ∀ j : ℤ, cyclicLinearCharacter ρ M j
      ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = (-1 : ℂ) ^ j := by
    intro j
    have h := cyclicLinearCharacter_zpow hord j ((M / 2 : ℕ) : ℤ)
    rw [show (⟨ρ ^ (((M / 2 : ℕ) : ℤ)), Subgroup.zpow_mem_zpowers _ _⟩ :
        Subgroup.zpowers ρ) = ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ from
        Subtype.ext (zpow_natCast _ _)] at h
    rw [h, mul_comm, zpow_mul, cyclicRoot_zpow_half hn]
  have hM4 := (modulus_eq_four_mul hn).1
  have hΘ1 : (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x)
      (1 : Subgroup.zpowers ρ) = 0 := by simp only [hlam1, sub_self]
  have hΘt : (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x)
      ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 := by
    simp only [hlamt]
    rw [show (((M / 2 : ℕ) : ℤ)) = 2 * ((M / 4 : ℕ) : ℤ) by omega, zpow_mul]
    norm_num
  have hE1 : ∀ l : ℕ, (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
      (1 : Subgroup.zpowers ρ) = 0 := fun l => by simp only [hlam1, sub_self]
  have hEt : ∀ l : ℕ, (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
      ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 := fun l => by
    simp only [hlamt]
    rw [zpow_mul]
    norm_num
  have hF1 : ∀ j : ℤ, (fun x => cyclicLinearCharacter ρ M j x -
      cyclicLinearCharacter ρ M 1 x) (1 : Subgroup.zpowers ρ) = 0 := fun j => by
    simp only [hlam1, sub_self]
  have hFt : ∀ j : ℤ, Odd j → (fun x => cyclicLinearCharacter ρ M j x -
      cyclicLinearCharacter ρ M 1 x) ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 := by
    intro j hj
    simp only [hlamt]
    rw [hj.neg_one_zpow]
    norm_num
  have hval := (cyclic_principal_Fourier_projection_values hn presentation basis ideal
    principal hprincipal).1
  beta_reduce at hval
  refine ⟨fun x hx => ⟨?_, fun l _ _ => ?_, fun j hj => ?_⟩, ?_⟩
  · exact original_cyclic_projection_rotation_section_support hn presentation basis ideal
      principal hprincipal _ hΘ1 hΘt x hx
  · exact original_cyclic_projection_rotation_section_support hn presentation basis ideal
      principal hprincipal _ (hE1 l) (hEt l) x hx
  · exact original_cyclic_projection_rotation_section_support hn presentation basis ideal
      principal hprincipal _ (hF1 j) (hFt j hj) x hx
  · intro v hv0 hv1 x hx
    obtain ⟨g, y, hy, hxy⟩ := SameParameterSections.twoSection_normal_form hx
    have hconst : ∀ h : Subgroup.zpowers ρ → ℂ,
        principalCyclicProjection basis B ρ h x =
          principalCyclicProjection basis B ρ h (ρ ^ v * (y : G)) := by
      intro h
      unfold principalCyclicProjection
      apply Finset.sum_congr rfl
      intro c hc
      rw [← hxy]
      exact congrArg (fun z => characterPairing (fun a : Subgroup.zpowers ρ =>
        (basis.representation c).character a) h * z)
          (Representation.char_conj (basis.representation c).representation x g).symm
    have h := hval v hv0 hv1 y y.property (by rw [Subgroup.orderOf_coe]; exact hy)
    rw [← hconst _] at h
    refine ⟨h.1, fun l hl1 hl2 => ?_, fun j hj => ?_⟩
    · have he := h.2.1 l hl1 hl2
      rwa [← hconst _] at he
    · have hf := h.2.2 j hj
      rwa [← hconst _] at hf

theorem original_regular_actual_family_rotation_support {G : Type} [Group G] [Fintype G]
    (hindex : ∀ U : Subgroup G, U.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {t : G}
    (ht : orderOf t = 2) [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq3 : 3 ≤ q) (hqodd : Odd q) (e : ℤ) (he : e = 1 ∨ e = -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index)
    (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    {S : Sylow 2 G} (presentation : SemidihedralGroup n ≃* (S : Subgroup G))
    (hcent : (presentation (r n) : G) ^ (modulus n / 2) = t) (p : ℕ)
    (hvalues : ActualPrincipalCharacteristicValues basis t (presentation (s n) : G) p q
      (2 ^ (n - 3)) e δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :
    let χ := fun c : basis.index => (basis.representation c).character
    ∀ x ∉ SameParameterSections.rotationSections presentation,
      (1 + (e : ℂ) • χ χ₁ - χ χ₂ - (e : ℂ) • χ χ₃) x = 0 ∧
      (∀ j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1),
        (1 + (e : ℂ) • χ χ₁ - (e : ℂ) • χ (ψ j)) x = 0) ∧
      ∀ i ∈ Finset.range (2 ^ (n - 3)), ∀ j ∈ Finset.range (2 ^ (n - 3)),
        (χ (ν i) - χ (ν j)) x = 0 := by
  intro χ x hx
  have hsupport := (original_fourier_rotation_sections hn presentation basis ideal
    principal hprincipal).1 x hx
  have hΘ := original_regular_principal_fourier_theta hindex hn hnonab basis ideal
    principal hprincipal localBasis localPrincipal q hq3 hqodd e he φ δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν hfam presentation hcent p hvalues
  obtain ⟨σe, hEe⟩ := original_regular_even_fourier_family hindex hn ht hnonab basis ideal
    principal hprincipal localBasis localPrincipal q hq3 hqodd e he φ δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν hfam presentation hcent p hvalues
  obtain ⟨I, hI⟩ := exists_isOddResidueTransversal hn
  obtain ⟨ε, σo, hε, hFo⟩ := original_regular_odd_fourier_family hindex hn ht hnonab basis ideal
    principal hprincipal localBasis localPrincipal q hq3 hqodd e he φ δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν hfam presentation hcent p hvalues I hI
  have hM4 := (modulus_eq_four_mul hn).1
  refine ⟨?_, ?_, ?_⟩
  · rw [← hΘ]
    exact hsupport.1
  · intro j hj
    let l := σe.symm ⟨j, hj⟩
    have hl := Finset.mem_Icc.mp l.property
    have hl2 : (l : ℕ) ≤ modulus n / 4 - 1 := by omega
    have hσ : σe l = ⟨j, hj⟩ := σe.apply_symm_apply _
    have heq := congrFun (hEe l) x
    rw [hσ] at heq
    exact heq.symm.trans (hsupport.2.1 l hl.1 hl2)
  · have hε0 : (ε : ℂ) ≠ 0 := by
      rcases hε with h | h <;> rw [h] <;> norm_num
    have hν : ∀ i ∈ Finset.range (2 ^ (n - 3)),
        χ (ν i) x = χ (ν (σo ⟨1, hI.one_mem⟩)) x := by
      intro i hi
      let j := σo.symm ⟨i, hi⟩
      have hjodd : Odd ((j : ZMod (modulus n)).val : ℤ) := by
        exact_mod_cast hI.odd j j.property
      have hσ : σo j = ⟨i, hi⟩ := σo.apply_symm_apply _
      have heq := congrFun (hFo j) x
      rw [hσ] at heq
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at heq
      have hzero := heq.symm.trans (hsupport.2.2 _ hjodd)
      exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hε0)
    intro i hi j hj
    exact sub_eq_zero.mpr ((hν i hi).trans (hν j hj).symm)

theorem original_fourier_ordinary_pairings {G : Type u} [Group G] [Fintype G]
    {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (presentation : SemidihedralGroup n ≃* (S : Subgroup G))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (I : Finset (ZMod (modulus n)))
    (hI : IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : G := presentation (r n)
    let M := modulus n
    let Θ := principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x)
    let E := fun l : ℕ => principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
    let F := fun j : ZMod M => principalCyclicProjection basis B ρ
      (fun x => cyclicLinearCharacter ρ M j.val x - cyclicLinearCharacter ρ M 1 x)
    characterPairing Θ 1 = 1 ∧ characterPairing Θ Θ = 4 ∧
      (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 →
        E l 1 = 0 ∧ characterPairing (E l) 1 = 1 ∧ characterPairing Θ (E l) = 2) ∧
      (∀ j l : ℕ, 1 ≤ j → j ≤ M / 4 - 1 → 1 ≤ l → l ≤ M / 4 - 1 →
        characterPairing (E j) (E l) = 2 + if j = l then 1 else 0) ∧
      F 1 = 0 ∧
      (∀ j ∈ I, F j 1 = 0 ∧ characterPairing (F j) 1 = 0 ∧
        characterPairing (F j) Θ = 0 ∧
        ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → characterPairing (F j) (E l) = 0) ∧
      (∀ j ∈ I, ∀ k ∈ I, j ≠ 1 → k ≠ 1 →
        characterPairing (F j) (F k) = 1 + if j = k then 1 else 0) := by
  intro B ρ M Θ E F
  obtain ⟨-, -, -, -, -, hE1, -, -, hΘone, hEone, -, -, -, hΘΘ, hΘE, hEE, -⟩ :=
    even_cyclic_principal_Fourier_family hn presentation basis ideal principal hprincipal
  obtain ⟨-, -, -, hFone, hF1, -, hFprincipal, -, hFF, hFΘ, hFE, -⟩ :=
    odd_cyclic_principal_Fourier_family hn presentation basis ideal principal hprincipal I hI
  exact ⟨hΘone, hΘΘ, fun l hl1 hl2 => ⟨hE1 l hl1 hl2, hEone l hl1 hl2,
    hΘE l hl1 hl2⟩, hEE, hFone, fun j hj => ⟨hF1 j hj, hFprincipal j hj,
      (hFΘ j hj).2, fun l hl1 hl2 => (hFE j hj l hl1 hl2).2⟩, hFF⟩

theorem original_regular_rotation_pairings_of_character_restrictions
    {G : Type} [Group G] [Fintype G]
    (hindex : ∀ U : Subgroup G, U.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {t : G}
    (ht : orderOf t = 2) [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq3 : 3 ≤ q) (hqodd : Odd q) (e : ℤ) (he : e = 1 ∨ e = -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index)
    (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    {S : Sylow 2 G} (presentation : SemidihedralGroup n ≃* (S : Subgroup G))
    (hcent : (presentation (r n) : G) ^ (modulus n / 2) = t) (p : ℕ)
    (hvalues : ActualPrincipalCharacteristicValues basis t (presentation (s n) : G) p q
      (2 ^ (n - 3)) e δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (θ₁ : FiniteComplexRepresentation.{0, v} G)
    (θ₂ : FiniteComplexRepresentation.{0, w} G)
    (θ₃ : FiniteComplexRepresentation.{0, z} G) (d₁ d₂ d₃ : ℤ)
    (hrow : ∀ x ∈ SameParameterSections.rotationSections presentation,
      θ₁.character x = (d₁ * e : ℤ) * (basis.representation χ₁).character x ∧
      θ₂.character x = (-d₂ : ℤ) * (basis.representation χ₂).character x ∧
      θ₃.character x = (-d₃ * e : ℤ) * (basis.representation χ₃).character x) :
    let χ := fun c : basis.index => (basis.representation c).character
    let T := 1 + (e : ℂ) • χ χ₁ - χ χ₂ - (e : ℂ) • χ χ₃
    let E := fun j : ℕ => 1 + (e : ℂ) • χ χ₁ - (e : ℂ) • χ (ψ j)
    characterPairing θ₁.character T = d₁ ∧ characterPairing θ₂.character T = d₂ ∧
      characterPairing θ₃.character T = d₃ ∧
      (∀ j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1), characterPairing θ₁.character (E j) = d₁) ∧
      ∀ i ∈ Finset.range (2 ^ (n - 3)), ∀ j ∈ Finset.range (2 ^ (n - 3)),
        characterPairing θ₁.character (χ (ν i) - χ (ν j)) = 0 := by
  intro χ T E
  have hs := original_regular_actual_family_rotation_support hindex hn ht hnonab basis ideal
    principal hprincipal localBasis localPrincipal q hq3 hqodd e he φ δ₁ δ₂ δ₃ δ₄
      χ₁ χ₂ χ₃ χ₄ ψ ν hfam presentation hcent p hvalues
  obtain ⟨-, -, -, -, -, hnd, -, -, hψavoid, hνavoid, -, -, -, -, -, -⟩ := hfam
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h01, h02, h03, -⟩, ⟨h12, h13, -⟩, ⟨h23, -⟩, -, -⟩ := hnd
  have hlin : ∀ (c : basis.index) (a : basis.index → ℂ),
      characterPairing (χ c) (fun x => ∑ d, a d * χ d x) = a c := by
    intro c a
    rw [characterPairing_comm]
    exact basis_combination_coefficient basis (Finset.mem_univ c) a
  have hTsum : T = fun x => ∑ c,
      ((if c = principal then 1 else 0) + (e : ℂ) * (if c = χ₁ then 1 else 0) -
        (if c = χ₂ then 1 else 0) - (e : ℂ) * (if c = χ₃ then 1 else 0)) * χ c x := by
    funext x
    simp [T, χ, Finset.sum_add_distrib, Finset.sum_sub_distrib, add_mul, sub_mul,
      mul_ite, Finset.sum_ite_eq', hprincipal]
  have hEsum : ∀ j, E j = fun x => ∑ c,
      ((if c = principal then 1 else 0) + (e : ℂ) * (if c = χ₁ then 1 else 0) -
        (e : ℂ) * (if c = ψ j then 1 else 0)) * χ c x := by
    intro j
    funext x
    simp [E, χ, Finset.sum_add_distrib, Finset.sum_sub_distrib, add_mul, sub_mul,
      mul_ite, Finset.sum_ite_eq', hprincipal]
  have hT₁ : characterPairing (χ χ₁) T = e := by
    rw [hTsum, hlin]
    simp [Ne.symm h01, h12, h13]
  have hT₂ : characterPairing (χ χ₂) T = -1 := by
    rw [hTsum, hlin]
    simp [Ne.symm h02, Ne.symm h12, h23]
  have hT₃ : characterPairing (χ χ₃) T = -(e : ℂ) := by
    rw [hTsum, hlin]
    simp [Ne.symm h03, Ne.symm h13, Ne.symm h23]
  have hE : ∀ j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1), characterPairing (χ χ₁) (E j) = e := by
    intro j hj
    rw [hEsum j, hlin]
    simp [Ne.symm h01, Ne.symm (hψavoid j hj).2.1]
  have hF : ∀ i ∈ Finset.range (2 ^ (n - 3)), ∀ j ∈ Finset.range (2 ^ (n - 3)),
      characterPairing (χ χ₁) (χ (ν i) - χ (ν j)) = 0 := by
    intro i hi j hj
    change characterPairing (χ χ₁) (fun x => χ (ν i) x - χ (ν j) x) = 0
    rw [characterPairing_sub_right']
    change characterPairing (basis.representation χ₁).character
      (basis.representation (ν i)).character - characterPairing
        (basis.representation χ₁).character (basis.representation (ν j)).character = 0
    rw [characterPairing_basis, characterPairing_basis]
    simp [Ne.symm (hνavoid i hi).2.1, Ne.symm (hνavoid j hj).2.1]
  have he2 : (e : ℂ) * e = 1 := by rcases he with h | h <;> rw [h] <;> norm_num
  have hpair := SameParameterSections.pairing_of_rotation_sections hn presentation
  have h1 := hpair θ₁.character (χ χ₁) T ((d₁ * e : ℤ) : ℂ)
    (fun x hx => (hrow x hx).1) (fun x hx => (hs x hx).1)
  have h2 := hpair θ₂.character (χ χ₂) T ((-d₂ : ℤ) : ℂ)
    (fun x hx => (hrow x hx).2.1) (fun x hx => (hs x hx).1)
  have h3 := hpair θ₃.character (χ χ₃) T ((-d₃ * e : ℤ) : ℂ)
    (fun x hx => (hrow x hx).2.2) (fun x hx => (hs x hx).1)
  rw [hT₁, Int.cast_mul, mul_assoc, he2, mul_one] at h1
  rw [hT₂, Int.cast_neg, mul_neg_one, neg_neg] at h2
  rw [hT₃, Int.cast_mul, Int.cast_neg] at h3
  have h3' : characterPairing θ₃.character T = d₃ := by
    calc
      characterPairing θ₃.character T = -(d₃ : ℂ) * e * -(e : ℂ) := h3
      _ = (d₃ : ℂ) * ((e : ℂ) * e) := by ring
      _ = d₃ := by rw [he2, mul_one]
  refine ⟨h1, h2, h3', ?_, ?_⟩
  · intro j hj
    have h := hpair θ₁.character (χ χ₁) (E j) ((d₁ * e : ℤ) : ℂ)
      (fun x hx => (hrow x hx).1) (fun x hx => (hs x hx).2.1 j hj)
    rwa [hE j hj, Int.cast_mul, mul_assoc, he2, mul_one] at h
  · intro i hi j hj
    have h := hpair θ₁.character (χ χ₁) (χ (ν i) - χ (ν j)) ((d₁ * e : ℤ) : ℂ)
      (fun x hx => (hrow x hx).1) (fun x hx => (hs x hx).2.2 i hi j hj)
    rwa [hF i hi j hj, mul_zero] at h

end ActualFourier

end CFSG.Semidihedral.PerfectLayerNormalization
