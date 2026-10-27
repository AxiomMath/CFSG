module

public import CFSG.CharacterTheory.Semidihedral.Principal.EvenFourierFamily
public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.NonrealSectionVanishing

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Open

variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}

omit [Fintype G] in
theorem character_involution_eigen (data : FiniteComplexRepresentation G) {g : G}
    (hg : g ^ 2 = 1) :
    ∃ a b : ℕ, data.character 1 = a + b ∧ data.character g = a - b := by
  obtain ⟨a, ha⟩ := cyclicMultiplicity_natural data g (by norm_num : 0 < 2) hg 0
  obtain ⟨b, hb⟩ := cyclicMultiplicity_natural data g (by norm_num : 0 < 2) hg 1
  have hζ : cyclicRoot 2 = -1 := by
    have h := cyclicRoot_pow_half (M := 2) (by norm_num) (by decide)
    simpa using h
  have h0 := cyclicMultiplicity_inversion data.character g (M := 2) (by norm_num) (w := 0)
    (by norm_num)
  have h1 := cyclicMultiplicity_inversion data.character g (M := 2) (by norm_num) (w := 1)
    (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    mul_zero, zpow_zero, mul_one, pow_zero, pow_one, ha, hb, hζ] at h0 h1
  refine ⟨a, b, h0, ?_⟩
  rw [h1]
  simp
  ring

omit [Fintype G] in
theorem character_involution_parity (data : FiniteComplexRepresentation G) {g : G}
    (hg : g ^ 2 = 1) : ∃ k : ℤ, data.character g = k ∧
      ∀ d : ℕ, data.character 1 = d → (k - d) % 2 = 0 := by
  obtain ⟨a, b, h1, hg'⟩ := character_involution_eigen data hg
  refine ⟨a - b, by rw [hg']; push_cast; ring, fun d hd => ?_⟩
  have : (d : ℂ) = ((a + b : ℕ) : ℂ) := by rw [← hd, h1]; push_cast; ring
  have hd' : d = a + b := by exact_mod_cast this
  subst hd'
  push_cast
  omega

theorem odd_rotation_not_isConj_inv (hn : 4 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G))
    {v : ℤ} (hv : Odd v) : ¬ IsConj ((e (r n) : G) ^ v) ((e (r n) : G) ^ v)⁻¹ := by
  obtain ⟨hM4, -, hK2, -⟩ := modulus_eq_four_mul hn
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = ((2 ^ (n - 3) : ℕ) : ℤ) := ⟨_, rfl⟩
  have hMK : (modulus n : ℤ) = 4 * K := by rw [hK, hM4]; push_cast; ring
  have hhalf : ((modulus n / 2 : ℕ) : ℤ) = 2 * K := by rw [hK]; omega
  have hnc : ∀ w : ℤ, Odd w → ¬ w ≡ 0 [ZMOD modulus n] ∧
      ¬ w ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] := by
    intro w hw
    obtain ⟨k, rfl⟩ := hw
    constructor
    · intro h
      obtain ⟨c, hc⟩ := Int.modEq_zero_iff_dvd.mp h
      obtain ⟨P, hP⟩ : ∃ P : ℤ, P = K * c := ⟨_, rfl⟩
      have : 2 * k + 1 = 4 * P := by rw [hP, hc, hMK]; ring
      omega
    · intro h
      obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp h
      obtain ⟨P, hP⟩ : ∃ P : ℤ, P = K * c := ⟨_, rfl⟩
      have : 2 * K - (2 * k + 1) = 4 * P := by rw [hP, ← hhalf, hc, hMK]; ring
      omega
  obtain ⟨hv0, hv1⟩ := hnc (-v) hv.neg
  rw [← zpow_neg, noncentralRotation_isConj_iff hn e v (-v) hv0 hv1]
  obtain ⟨k, rfl⟩ := hv
  rintro (h | h)
  · obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp h
    obtain ⟨P, hP⟩ : ∃ P : ℤ, P = K * c := ⟨_, rfl⟩
    have : 2 * k + 1 - -(2 * k + 1) = 4 * P := by rw [hP, hc, hMK]; ring
    omega
  · obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp h
    have hc' : (2 * K - 1) * (2 * k + 1) - -(2 * k + 1) = 4 * K * c := by
      rw [← hhalf, hc, hMK]
    have h2 : (2 * K) * (2 * k + 1) = (2 * K) * (2 * c) := by linarith
    have hK0 : (2 * K) ≠ 0 := by omega
    have h3 := mul_left_cancel₀ hK0 h2
    omega

theorem principal_Fourier_involution_square_sum (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      characterPairing
        (fun x : Subgroup.zpowers (e (r n) : G) => (basis.representation χ).character x)
        (fun x => 1 - cyclicLinearCharacter (e (r n) : G) (modulus n)
          ((modulus n / 2 : ℕ) : ℤ) x) *
      ((basis.representation χ).character ((e (r n) : G) ^ (modulus n / 2)) *
        (basis.representation χ).character ((e (r n) : G) ^ (modulus n / 2)) /
          (basis.representation χ).character 1) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord := suppliedRotation_orderOf (by omega) e
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set t := (e (r n) : G) ^ (modulus n / 2) with ht
  set w : basis.index → ℂ := fun χ => (basis.representation χ).character t *
    (basis.representation χ).character t / (basis.representation χ).character 1 with hw
  have ht2 : orderOf t = 2 := suppliedRotation_half_orderOf hn e
  have hterm : ∀ v : ℕ, (∑ χ ∈ B, w χ *
      (basis.representation χ).character ((e (r n) : G) ^ (v : ℤ))) *
        (1 - cyclicLinearCharacter (e (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ)
          ⟨(e (r n) : G) ^ (-(v : ℤ)), Subgroup.zpow_mem_zpowers _ _⟩) = 0 := by
    intro v
    rcases Nat.even_or_odd v with hv | hv
    · rw [cyclicLinearCharacter_zpow hord, zpow_mul, cyclicRoot_zpow_half hn]
      obtain ⟨k, rfl⟩ := hv
      rw [show -((k + k : ℕ) : ℤ) = 2 * (-(k : ℤ)) by push_cast; ring, zpow_mul]
      norm_num
    · have hu : ∃ m : ℕ, orderOf ((e (r n) : G) ^ (v : ℤ)) = 2 ^ m := by
        obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
          (suppliedRotation_zpow_orderOf_dvd (by omega) e (v : ℤ))
        exact ⟨m, hm⟩
      have h0 := (nonreal_primary_section_block_involution_product_vanishing basis ideal 2
        principal ht2 ht2 hu (odd_rotation_not_isConj_inv hn e (by exact_mod_cast hv)) 1
        (Subgroup.one_mem _) (by rw [orderOf_one]; exact Nat.coprime_one_right 2)).1
      rw [mul_one] at h0
      have hsum : ∑ χ ∈ B, w χ * (basis.representation χ).character ((e (r n) : G) ^ (v : ℤ)) =
          ∑ χ ∈ B, (basis.representation χ).character t * (basis.representation χ).character t *
            (basis.representation χ).character ((e (r n) : G) ^ (v : ℤ)) /
              (basis.representation χ).character 1 :=
        Finset.sum_congr rfl fun χ _ => by rw [hw]; ring
      rw [hsum, h0, zero_mul]
  have hlin : ∑ χ ∈ B, characterPairing
      (fun x : Subgroup.zpowers (e (r n) : G) => (basis.representation χ).character x)
      (fun x => 1 - cyclicLinearCharacter (e (r n) : G) (modulus n)
        ((modulus n / 2 : ℕ) : ℤ) x) * w χ =
      characterPairing (fun x : Subgroup.zpowers (e (r n) : G) =>
        ∑ χ ∈ B, w χ * (basis.representation χ).character x)
        (fun x => 1 - cyclicLinearCharacter (e (r n) : G) (modulus n)
          ((modulus n / 2 : ℕ) : ℤ) x) := by
    rw [characterPairing_finset_expansion_left]
    exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
  rw [hlin, characterPairing_zpowers_eq_sum_range hord]
  exact mul_eq_zero_of_right _ (Finset.sum_eq_zero fun v _ => hterm v)

theorem sum_four_labels {ι : Type*} [DecidableEq ι] {B : Finset ι} {p y s u : ι} (hp : p ∈ B)
    (hy : y ∈ B) (hs : s ∈ B) (hu : u ∈ B) (b c d : ℤ) (w : ι → ℂ) :
    ∑ x ∈ B, ((((if x = p then 1 else 0) + b * (if x = y then 1 else 0) +
        c * (if x = s then 1 else 0) + d * (if x = u then 1 else 0) : ℤ)) : ℂ) * w x =
      w p + b * w y + c * w s + d * w u := by
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    one_mul, Finset.sum_ite_eq', hp, hy, hs, hu, ite_true]

theorem principal_Fourier_theta_parity (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (c : basis.index) :
    ((multiplicityColumn basis (e (r n) : G) (modulus n) 0 c -
      multiplicityColumn basis (e (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) c) -
        (Module.finrank ℂ (basis.representation c).vector : ℤ)) % 2 = 0 := by
  obtain ⟨hM4, -, hK2, -⟩ := modulus_eq_four_mul hn
  obtain ⟨I, hI⟩ := exists_isOddResidueTransversal hn
  have hcent := supplied_central_column_identity hn e basis hI c
  have ht2 : ((e (r n) : G) ^ (modulus n / 2)) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one ((e (r n) : G) ^ (modulus n / 2))
    rwa [suppliedRotation_half_orderOf hn e] at h
  obtain ⟨k, hk, hkd⟩ := character_involution_parity (basis.representation c) ht2
  have hd := hkd (Module.finrank ℂ (basis.representation c).vector)
    (basis_character_one basis c).1
  set L := multiplicityColumn basis (e (r n) : G) (modulus n) with hL
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = ∑ l ∈ Finset.Icc 1 (modulus n / 4 - 1), (L 0 c - L (2 * l) c) :=
    ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A' : ℤ, A' = ∑ j ∈ I, (L j.val c - L 1 c) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = ((2 ^ (n - 3) : ℕ) : ℤ) * (L 0 c - L 1 c) := ⟨_, rfl⟩
  have hhalf : ((modulus n / 2 : ℕ) : ℤ) = 2 * ((2 ^ (n - 3) : ℕ) : ℤ) := by omega
  rw [← hA, ← hA'] at hcent
  have hkX : k = 2 * P - (L 0 c - L (modulus n / 2 : ℕ) c) - 2 * A - 2 * A' := by
    have h := hk.symm.trans hcent
    have h' : k = ((modulus n / 2 : ℕ) : ℤ) * (L 0 c - L 1 c) -
        (L 0 c - L (modulus n / 2 : ℕ) c) - 2 * A - 2 * A' := by exact_mod_cast h
    rw [h', hhalf, hP]
    ring
  omega

theorem odd_degree_sign_alignment {f₁ f₂ f₃ : ℕ} {τ₁ τ₂ τ₃ δ₁ δ₂ δ₃ : ℤ}
    (hτ₁ : τ₁ = 1 ∨ τ₁ = -1) (hτ₂ : τ₂ = 1 ∨ τ₂ = -1) (hτ₃ : τ₃ = 1 ∨ τ₃ = -1)
    (hδ₁ : δ₁ = 1 ∨ δ₁ = -1) (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (hδ₃ : δ₃ = 1 ∨ δ₃ = -1) (hf₃ : 1 < f₃)
    (hκ : τ₁ * δ₁ = τ₂ * δ₂) (hτδ₃ : τ₃ * δ₃ = 1)
    (hΘdeg : 1 + τ₁ * (f₁ : ℤ) + τ₂ * f₂ + τ₃ * f₃ = 0)
    (hdeg : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0) :
    τ₁ = δ₁ ∧ τ₂ = δ₂ ∧ τ₃ = δ₃ := by
  have hs₃ : τ₃ = δ₃ := by
    rcases hτ₃ with rfl | rfl <;> rcases hδ₃ with rfl | rfl <;> omega
  subst hs₃
  rcases hτ₁ with rfl | rfl <;> rcases hτ₂ with rfl | rfl <;> rcases hδ₁ with rfl | rfl <;>
    rcases hδ₂ with rfl | rfl <;> rcases hτ₃ with rfl | rfl <;> omega

theorem odd_degree_reciprocal_rat {q f₁ f₂ f₃ : ℕ} {ε δ₁ δ₂ δ₃ : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hδ₁ : δ₁ = 1 ∨ δ₁ = -1) (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (hδ₃ : δ₃ = 1 ∨ δ₃ = -1)
    (h : 1 + (δ₁ : ℂ) * ((δ₁ : ℂ) * ε * q * ((δ₁ : ℂ) * ε * q) / f₁) +
      (δ₂ : ℂ) * (-(δ₂ : ℂ) * ε * q * (-(δ₂ : ℂ) * ε * q) / f₂) +
        (δ₃ : ℂ) * (-(δ₃ : ℂ) * -(δ₃ : ℂ) / f₃) = 0) :
    (1 : ℚ) + δ₁ * q ^ 2 / f₁ + δ₂ * q ^ 2 / f₂ + δ₃ / f₃ = 0 := by
  have sq : ∀ a : ℤ, (a = 1 ∨ a = -1) → (a : ℂ) * a = 1 := by
    rintro a (rfl | rfl) <;> norm_num
  have he := sq ε hε
  have hd1 := sq δ₁ hδ₁
  have hd2 := sq δ₂ hδ₂
  have hd3 := sq δ₃ hδ₃
  have hC : (((1 : ℚ) + δ₁ * q ^ 2 / f₁ + δ₂ * q ^ 2 / f₂ + δ₃ / f₃ : ℚ) : ℂ) = 0 := by
    push_cast
    linear_combination h - ((δ₁ : ℂ) * q ^ 2 / f₁) * ((δ₁ : ℂ) * δ₁ * he + hd1) -
      ((δ₂ : ℂ) * q ^ 2 / f₂) * ((δ₂ : ℂ) * δ₂ * he + hd2) - ((δ₃ : ℂ) / f₃) * hd3
  exact_mod_cast hC

theorem odd_degree_product_algebra {q f₁ f₂ f₃ : ℕ} {δ₁ δ₂ δ₃ : ℤ} (hq : 0 < q)
    (hf₁ : 1 < f₁) (hf₂ : 1 < f₂) (hf₃ : 1 < f₃) (hδ₁ : δ₁ = 1 ∨ δ₁ = -1)
    (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (hδ₃ : δ₃ = 1 ∨ δ₃ = -1)
    (hdeg : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0)
    (hQ : (1 : ℚ) + δ₁ * q ^ 2 / f₁ + δ₂ * q ^ 2 / f₂ + δ₃ / f₃ = 0) :
    ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) ∧ f₁ * f₂ = q ^ 2 * f₃ := by
  have hf₁0 : (f₁ : ℚ) ≠ 0 := by exact_mod_cast (by omega : f₁ ≠ 0)
  have hf₂0 : (f₂ : ℚ) ≠ 0 := by exact_mod_cast (by omega : f₂ ≠ 0)
  have hf₃0 : (f₃ : ℚ) ≠ 0 := by exact_mod_cast (by omega : f₃ ≠ 0)
  have hI : (f₁ : ℤ) * f₂ * f₃ + δ₁ * q ^ 2 * f₂ * f₃ + δ₂ * q ^ 2 * f₁ * f₃ + δ₃ * f₁ * f₂ =
      0 := by
    have h : (((f₁ : ℤ) * f₂ * f₃ + δ₁ * q ^ 2 * f₂ * f₃ + δ₂ * q ^ 2 * f₁ * f₃ +
        δ₃ * f₁ * f₂ : ℤ) : ℚ) = (f₁ * f₂ * f₃ : ℚ) *
          ((1 : ℚ) + δ₁ * q ^ 2 / f₁ + δ₂ * q ^ 2 / f₂ + δ₃ / f₃) := by
      push_cast
      field_simp
    rw [hQ, mul_zero] at h
    exact_mod_cast h
  have sq : ∀ a : ℤ, (a = 1 ∨ a = -1) → a * a = 1 := by
    rintro a (rfl | rfl) <;> norm_num
  have hd1 := sq δ₁ hδ₁
  have hd2 := sq δ₂ hδ₂
  have hd3 := sq δ₃ hδ₃
  have hfac : (1 + δ₃ * (f₃ : ℤ)) * (δ₁ * δ₂ * f₁ * f₂ - q ^ 2 * (δ₃ * f₃)) = 0 := by
    linear_combination (δ₁ * δ₂ * δ₃) * hI - ((q : ℤ) ^ 2 * δ₃ * f₃) * hdeg -
      (δ₁ * δ₂ * f₁ * f₂ : ℤ) * hd3 - ((q : ℤ) ^ 2 * δ₂ * δ₃ * f₂ * f₃) * hd1 -
      ((q : ℤ) ^ 2 * δ₁ * δ₃ * f₁ * f₃) * hd2
  have h1a : (1 + δ₃ * (f₃ : ℤ)) ≠ 0 := by
    rcases hδ₃ with rfl | rfl <;> omega
  have hprod : δ₁ * δ₂ * ((f₁ : ℤ) * f₂) = δ₃ * (q ^ 2 * f₃) := by
    have := (mul_eq_zero.mp hfac).resolve_left h1a
    linarith
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hf₃' : (0 : ℤ) < f₃ := by exact_mod_cast (by omega : 0 < f₃)
  have hpos : 0 < (q : ℤ) ^ 2 * f₃ := mul_pos (pow_pos hq' 2) hf₃'
  have hnn : 0 ≤ (f₁ : ℤ) * f₂ := by positivity
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = (f₁ : ℤ) * f₂ := ⟨_, rfl⟩
  obtain ⟨Q, hQ'⟩ : ∃ Q : ℤ, Q = (q : ℤ) ^ 2 * f₃ := ⟨_, rfl⟩
  rw [← hP, ← hQ'] at hprod
  rw [← hP] at hnn
  rw [← hQ'] at hpos
  have hmain : ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) ∧ P = Q := by
    rcases hδ₁ with rfl | rfl <;> rcases hδ₂ with rfl | rfl <;> rcases hδ₃ with rfl | rfl <;>
      omega
  refine ⟨hmain.1, ?_⟩
  have h := hmain.2
  rw [hP, hQ'] at h
  exact_mod_cast h

theorem principal_Fourier_odd_degree_product_of_degrees (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (c₁ c₂ c₃ : basis.index)
    (hc₁B : c₁ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hc₂B : c₂ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hc₃B : c₃ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (h01 : principal ≠ c₁) (h02 : principal ≠ c₂) (h03 : principal ≠ c₃) (h12 : c₁ ≠ c₂)
    (h13 : c₁ ≠ c₃) (h23 : c₂ ≠ c₃)
    (hodd : ∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (∃ d : ℕ, Odd d ∧ (basis.representation c).character 1 = d) ↔
        (c = principal ∨ c = c₁ ∨ c = c₂ ∨ c = c₃))
    (f₁ f₂ f₃ : ℕ) (hf₁ : (basis.representation c₁).character 1 = f₁)
    (hf₂ : (basis.representation c₂).character 1 = f₂)
    (hf₃ : (basis.representation c₃).character 1 = f₃) (q : ℕ) (hq : 0 < q)
    (ε δ₁ δ₂ δ₃ : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hδ₁ : δ₁ = 1 ∨ δ₁ = -1) (hδ₂ : δ₂ = 1 ∨ δ₂ = -1)
    (hδ₃ : δ₃ = 1 ∨ δ₃ = -1) (Φ : G → ℂ)
    (hΦ : ∃ y₁ ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)},
      ∃ y₂ ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)},
        Odd (orderOf y₁) ∧ Odd (orderOf y₂) ∧ Φ y₁ ≠ Φ y₂)
    (hΦ1 : Φ 1 = q)
    (hχ₁ : ∀ y ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)}, Odd (orderOf y) →
      (basis.representation c₁).character ((e (r n) : G) ^ (modulus n / 2) * y) =
        δ₁ * ε * Φ y)
    (hχ₂ : ∀ y ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)}, Odd (orderOf y) →
      (basis.representation c₂).character ((e (r n) : G) ^ (modulus n / 2) * y) =
        -δ₂ * ε * Φ y)
    (hχ₃ : ∀ y ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)}, Odd (orderOf y) →
      (basis.representation c₃).character ((e (r n) : G) ^ (modulus n / 2) * y) = -δ₃)
    (hdeg : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0)
    (hf₁1 : 1 < f₁) (hf₂1 : 1 < f₂) (hf₃1 : 1 < f₃) :
    principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
        principal) (e (r n) : G) (fun x => 1 - cyclicLinearCharacter (e (r n) : G) (modulus n)
          ((modulus n / 2 : ℕ) : ℤ) x) =
      1 + (δ₁ : ℂ) • (basis.representation c₁).character +
        (δ₂ : ℂ) • (basis.representation c₂).character +
          (δ₃ : ℂ) • (basis.representation c₃).character ∧
    ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) ∧
    (1 : ℚ) + δ₁ * q ^ 2 / f₁ + δ₂ * q ^ 2 / f₂ + δ₃ / f₃ = 0 ∧
    f₁ * f₂ = q ^ 2 * f₃ := by
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set t : G := (e (r n) : G) ^ (modulus n / 2) with ht
  have hpB : principal ∈ B := coefficientBlock_self_mem _ _ _
  obtain ⟨hcoefΘ, -, hΘapply, -, hΘ1, -, hθp, -, -, -, hθθ, -⟩ :=
    even_cyclic_principal_Fourier_family hn e basis ideal principal hprincipal
  let θ : basis.index → ℤ := fun c =>
    multiplicityColumn basis (e (r n) : G) (modulus n) 0 c -
      multiplicityColumn basis (e (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) c
  have hθp' : θ principal = 1 := hθp
  have hθθ' : ∑ c ∈ B, θ c * θ c = 4 := hθθ
  have hθodd : ∀ c ∈ B, Odd (θ c) ↔ (c = principal ∨ c = c₁ ∨ c = c₂ ∨ c = c₃) := by
    intro c hc
    rw [← hodd c hc]
    have hpar := principal_Fourier_theta_parity hn e basis c
    have hiff : Odd (θ c) ↔ Odd (Module.finrank ℂ (basis.representation c).vector) := by
      rw [Int.odd_iff, Nat.odd_iff]
      change ((multiplicityColumn basis (e (r n) : G) (modulus n) 0 c -
        multiplicityColumn basis (e (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) c) -
          (Module.finrank ℂ (basis.representation c).vector : ℤ)) % 2 = 0 at hpar
      change (multiplicityColumn basis (e (r n) : G) (modulus n) 0 c -
        multiplicityColumn basis (e (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) c) % 2 = 1 ↔ _
      omega
    rw [hiff]
    constructor
    · intro hodd'
      exact ⟨_, hodd', (basis_character_one basis c).1⟩
    · rintro ⟨d, hdodd, hdval⟩
      have hd : Module.finrank ℂ (basis.representation c).vector = d := by
        have h := (basis_character_one basis c).1
        rw [hdval] at h
        exact_mod_cast h.symm
      rw [hd]
      exact hdodd
  have hsq1 : ∀ c ∈ B, (c = principal ∨ c = c₁ ∨ c = c₂ ∨ c = c₃) → 1 ≤ θ c * θ c := by
    intro c hc hmem
    obtain ⟨m, hm⟩ := (hθodd c hc).mpr hmem
    have hne : θ c ≠ 0 := by omega
    have hpos := mul_self_pos.mpr hne
    omega
  let F4 : Finset basis.index := {principal, c₁, c₂, c₃}
  have hF4 : F4 ⊆ B := by
    intro x hx
    simp only [F4, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hpB
    · exact hc₁B
    · exact hc₂B
    · exact hc₃B
  have hsplit := Finset.sum_sdiff hF4 (f := fun c => θ c * θ c)
  have hF4sum : ∑ c ∈ F4, θ c * θ c =
      θ principal * θ principal + θ c₁ * θ c₁ + θ c₂ * θ c₂ + θ c₃ * θ c₃ := by
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_pair h23]
    · ring
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h12, h13⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01, h02, h03⟩
  have hs1 := hsq1 c₁ hc₁B (Or.inr (Or.inl rfl))
  have hs2 := hsq1 c₂ hc₂B (Or.inr (Or.inr (Or.inl rfl)))
  have hs3 := hsq1 c₃ hc₃B (Or.inr (Or.inr (Or.inr rfl)))
  have hrestnn : 0 ≤ ∑ c ∈ B \ F4, θ c * θ c :=
    Finset.sum_nonneg fun c _ => mul_self_nonneg (θ c)
  rw [hF4sum, hθθ', hθp'] at hsplit
  have hrest : ∑ c ∈ B \ F4, θ c * θ c = 0 := by linarith
  have hzero : ∀ c ∈ B, c ∉ F4 → θ c = 0 := by
    intro c hc hcF
    have hle : θ c * θ c ≤ ∑ c ∈ B \ F4, θ c * θ c :=
      Finset.single_le_sum (f := fun c => θ c * θ c) (fun c _ => mul_self_nonneg (θ c))
        (Finset.mem_sdiff.mpr ⟨hc, hcF⟩)
    exact mul_self_eq_zero.mp (le_antisymm (by linarith) (mul_self_nonneg (θ c)))
  have hτ₁ : θ c₁ = 1 ∨ θ c₁ = -1 := mul_self_eq_one_iff.mp (by linarith)
  have hτ₂ : θ c₂ = 1 ∨ θ c₂ = -1 := mul_self_eq_one_iff.mp (by linarith)
  have hτ₃ : θ c₃ = 1 ∨ θ c₃ = -1 := mul_self_eq_one_iff.mp (by linarith)
  have hθform : ∀ x ∈ B, θ x = (if x = principal then 1 else 0) +
      θ c₁ * (if x = c₁ then 1 else 0) + θ c₂ * (if x = c₂ then 1 else 0) +
      θ c₃ * (if x = c₃ then 1 else 0) := by
    intro x hx
    by_cases hxp : x = principal
    · rw [hxp, ite_eq_left rfl, ite_eq_right h01, ite_eq_right h02, ite_eq_right h03, hθp']
      ring
    by_cases hx1 : x = c₁
    · rw [hx1, ite_eq_right (Ne.symm h01), ite_eq_left rfl, ite_eq_right h12, ite_eq_right h13]
      ring
    by_cases hx2 : x = c₂
    · rw [hx2, ite_eq_right (Ne.symm h02), ite_eq_right (Ne.symm h12), ite_eq_left rfl,
        ite_eq_right h23]
      ring
    by_cases hx3 : x = c₃
    · rw [hx3, ite_eq_right (Ne.symm h03), ite_eq_right (Ne.symm h13),
        ite_eq_right (Ne.symm h23), ite_eq_left rfl]
      ring
    · have hxF : x ∉ F4 := by
        simp only [F4, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxp, hx1, hx2, hx3⟩
      rw [hzero x hx hxF, ite_eq_right hxp, ite_eq_right hx1, ite_eq_right hx2,
        ite_eq_right hx3]
      ring
  have hΘval : ∀ g : G, ∑ c ∈ B, (θ c : ℂ) * (basis.representation c).character g =
      1 + (θ c₁ : ℂ) * (basis.representation c₁).character g +
        (θ c₂ : ℂ) * (basis.representation c₂).character g +
        (θ c₃ : ℂ) * (basis.representation c₃).character g := by
    intro g
    have hsum : ∑ c ∈ B, (θ c : ℂ) * (basis.representation c).character g =
        ∑ c ∈ B, ((((if c = principal then 1 else 0) + θ c₁ * (if c = c₁ then 1 else 0) +
          θ c₂ * (if c = c₂ then 1 else 0) + θ c₃ * (if c = c₃ then 1 else 0) : ℤ)) : ℂ) *
            (basis.representation c).character g :=
      Finset.sum_congr rfl fun c hc => by rw [hθform c hc]
    rw [hsum, basis_combination_four basis hpB hc₁B hc₂B hc₃B, hprincipal, Pi.one_apply]
  have hvals := (cyclic_principal_Fourier_projection_values hn e basis ideal principal
    hprincipal).2.2
  have ht2 : orderOf t = 2 := suppliedRotation_half_orderOf hn e
  have hΘty : ∀ y ∈ Subgroup.centralizer {t}, Odd (orderOf y) →
      1 + (θ c₁ : ℂ) * (δ₁ * ε * Φ y) + (θ c₂ : ℂ) * (-δ₂ * ε * Φ y) + (θ c₃ : ℂ) * (-δ₃) =
        0 := by
    intro y hy hyodd
    have hcomm : Commute t y := (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
    have h0 := (hvals (t * y) t y rfl hcomm ht2 hyodd).1
    have h1 := (hΘapply (t * y)).symm.trans h0
    rw [hΘval (t * y), hχ₁ y hy hyodd, hχ₂ y hy hyodd, hχ₃ y hy hyodd] at h1
    exact h1
  obtain ⟨y₁, hy₁, y₂, hy₂, hy₁odd, hy₂odd, hΦne⟩ := hΦ
  have e1 := hΘty y₁ hy₁ hy₁odd
  have e2 := hΘty y₂ hy₂ hy₂odd
  have hκ : θ c₁ * δ₁ = θ c₂ * δ₂ := by
    have h : (ε : ℂ) * (((θ c₁ * δ₁ - θ c₂ * δ₂ : ℤ)) : ℂ) * (Φ y₁ - Φ y₂) = 0 := by
      push_cast
      linear_combination e1 - e2
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exfalso
        rcases hε with rfl | rfl <;> norm_num at h
      · have h' : θ c₁ * δ₁ - θ c₂ * δ₂ = 0 := by exact_mod_cast h
        linarith
    · exact absurd (sub_eq_zero.mp h) hΦne
  have hτδ₃ : θ c₃ * δ₃ = 1 := by
    have h : ((1 - θ c₃ * δ₃ : ℤ) : ℂ) +
        (ε : ℂ) * ((θ c₁ * δ₁ - θ c₂ * δ₂ : ℤ) : ℂ) * Φ y₁ = 0 := by
      push_cast
      linear_combination e1
    rw [show θ c₁ * δ₁ - θ c₂ * δ₂ = 0 by linarith, Int.cast_zero, mul_zero, zero_mul,
      add_zero] at h
    have h' : (1 - θ c₃ * δ₃ : ℤ) = 0 := by exact_mod_cast h
    linarith
  have hΘdeg : 1 + θ c₁ * (f₁ : ℤ) + θ c₂ * f₂ + θ c₃ * f₃ = 0 := by
    have h := (hΘapply 1).symm.trans hΘ1
    rw [hΘval 1, hf₁, hf₂, hf₃] at h
    exact_mod_cast h
  obtain ⟨hs₁, hs₂, hs₃⟩ := odd_degree_sign_alignment hτ₁ hτ₂ hτ₃ hδ₁ hδ₂ hδ₃ hf₃1 hκ hτδ₃
    hΘdeg hdeg
  have hΘdec : principalCyclicProjection basis B (e (r n) : G) (fun x => 1 -
      cyclicLinearCharacter (e (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) x) =
      1 + (δ₁ : ℂ) • (basis.representation c₁).character +
        (δ₂ : ℂ) • (basis.representation c₂).character +
          (δ₃ : ℂ) • (basis.representation c₃).character := by
    funext g
    refine (hΘapply g).trans ?_
    rw [hΘval g, hs₁, hs₂, hs₃]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
  have hrec := principal_Fourier_involution_square_sum hn e basis ideal principal
  have hθw : ∀ w : basis.index → ℂ, ∑ c ∈ B, (θ c : ℂ) * w c =
      w principal + θ c₁ * w c₁ + θ c₂ * w c₂ + θ c₃ * w c₃ := by
    intro w
    have hsum : ∑ c ∈ B, (θ c : ℂ) * w c =
        ∑ c ∈ B, ((((if c = principal then 1 else 0) + θ c₁ * (if c = c₁ then 1 else 0) +
          θ c₂ * (if c = c₂ then 1 else 0) + θ c₃ * (if c = c₃ then 1 else 0) : ℤ)) : ℂ) * w c :=
      Finset.sum_congr rfl fun c hc => by rw [hθform c hc]
    rw [hsum, sum_four_labels hpB hc₁B hc₂B hc₃B]
  have hrec' : ∑ c ∈ B, (θ c : ℂ) * ((basis.representation c).character t *
      (basis.representation c).character t / (basis.representation c).character 1) = 0 :=
    (Finset.sum_congr rfl fun c _ => congrArg (fun z => z * ((basis.representation c).character t *
      (basis.representation c).character t / (basis.representation c).character 1))
        (hcoefΘ c).symm).trans hrec
  rw [hθw, hs₁, hs₂, hs₃, hprincipal] at hrec'
  have hone_mem : (1 : G) ∈ Subgroup.centralizer {t} := Subgroup.one_mem _
  have hone_odd : Odd (orderOf (1 : G)) := by rw [orderOf_one]; exact odd_one
  have hv₁ := hχ₁ 1 hone_mem hone_odd
  have hv₂ := hχ₂ 1 hone_mem hone_odd
  have hv₃ := hχ₃ 1 hone_mem hone_odd
  rw [mul_one] at hv₁ hv₂ hv₃
  rw [hv₁, hv₂, hv₃, hf₁, hf₂, hf₃, hΦ1] at hrec'
  simp only [Pi.one_apply, mul_one, div_one] at hrec'
  have hQ := odd_degree_reciprocal_rat (q := q) (f₁ := f₁) (f₂ := f₂) (f₃ := f₃) hε hδ₁ hδ₂ hδ₃
    (by linear_combination hrec')
  obtain ⟨hsign, hprod⟩ := odd_degree_product_algebra hq hf₁1 hf₂1 hf₃1 hδ₁ hδ₂ hδ₃ hdeg hQ
  exact ⟨hΘdec, hsign, hQ, hprod⟩

theorem degree_one_eq_principal_of_simple [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis G) {principal : basis.index}
    (hprincipal : (basis.representation principal).character = 1) (c : basis.index)
    (hdeg : (basis.representation c).character 1 = 1) : c = principal := by
  set u := degreeOneCharacterUnits (basis.representation c) hdeg with hu
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal u.ker with hbot | htop
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    apply (MonoidHom.ker_eq_bot_iff u).mp hbot
    rw [map_mul, map_mul, mul_comm]
  · apply basis.distinct
    funext g
    have hg : g ∈ u.ker := htop ▸ Subgroup.mem_top g
    rw [MonoidHom.mem_ker] at hg
    show (basis.representation c).character g = (basis.representation principal).character g
    rw [hprincipal, Pi.one_apply, ← degreeOneCharacterUnits_val _ hdeg, ← hu, hg, Units.val_one]

theorem one_lt_degree_of_ne_principal (basis : FiniteIrreducibleCharacterBasis G)
    {principal c : basis.index} (hne : c ≠ principal)
    (hone : (basis.representation c).character 1 = 1 → c = principal) {f : ℕ}
    (hf : (basis.representation c).character 1 = f) : 1 < f := by
  have hpos := (basis_character_one basis c).2
  have hval := (basis_character_one basis c).1
  rw [hf] at hval
  have hfd : f = Module.finrank ℂ (basis.representation c).vector := by exact_mod_cast hval
  rcases Nat.lt_or_ge 1 f with h | h
  · exact h
  · exfalso
    have hf1 : f = 1 := by omega
    exact hne (hone (by rw [hf, hf1, Nat.cast_one]))

theorem principal_Fourier_odd_degree_product [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (c₁ c₂ c₃ : basis.index)
    (hc₁B : c₁ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hc₂B : c₂ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hc₃B : c₃ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (h01 : principal ≠ c₁) (h02 : principal ≠ c₂) (h03 : principal ≠ c₃) (h12 : c₁ ≠ c₂)
    (h13 : c₁ ≠ c₃) (h23 : c₂ ≠ c₃)
    (hodd : ∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (∃ d : ℕ, Odd d ∧ (basis.representation c).character 1 = d) ↔
        (c = principal ∨ c = c₁ ∨ c = c₂ ∨ c = c₃))
    (f₁ f₂ f₃ : ℕ) (hf₁ : (basis.representation c₁).character 1 = f₁)
    (hf₂ : (basis.representation c₂).character 1 = f₂)
    (hf₃ : (basis.representation c₃).character 1 = f₃) (q : ℕ) (hq3 : 3 ≤ q) (_hqodd : Odd q)
    (ε δ₁ δ₂ δ₃ : ℤ) (hε : ε = 1 ∨ ε = -1) (hδ₁ : δ₁ = 1 ∨ δ₁ = -1)
    (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (hδ₃ : δ₃ = 1 ∨ δ₃ = -1) (Φ : G → ℂ)
    (hΦ : ∃ y₁ ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)},
      ∃ y₂ ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)},
        Odd (orderOf y₁) ∧ Odd (orderOf y₂) ∧ Φ y₁ ≠ Φ y₂)
    (hΦ1 : Φ 1 = q)
    (hχ₁ : ∀ y ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)}, Odd (orderOf y) →
      (basis.representation c₁).character ((e (r n) : G) ^ (modulus n / 2) * y) =
        δ₁ * ε * Φ y)
    (hχ₂ : ∀ y ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)}, Odd (orderOf y) →
      (basis.representation c₂).character ((e (r n) : G) ^ (modulus n / 2) * y) =
        -δ₂ * ε * Φ y)
    (hχ₃ : ∀ y ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)}, Odd (orderOf y) →
      (basis.representation c₃).character ((e (r n) : G) ^ (modulus n / 2) * y) = -δ₃)
    (hdeg : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : G := (e (r n) : G)
    let M : ℕ := modulus n
    let χ : basis.index → G → ℂ := fun c => (basis.representation c).character
    let lam := cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ)
    let Θ := principalCyclicProjection basis B ρ (fun x => 1 - lam x)
    lam ⟨ρ, Subgroup.mem_zpowers ρ⟩ = -1 ∧
    Θ = 1 + (δ₁ : ℂ) • χ c₁ + (δ₂ : ℂ) • χ c₂ + (δ₃ : ℂ) • χ c₃ ∧
    1 < f₁ ∧ 1 < f₂ ∧ 1 < f₃ ∧
    ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) ∧
    (1 : ℚ) + δ₁ * q ^ 2 / f₁ + δ₂ * q ^ 2 / f₂ + δ₃ / f₃ = 0 ∧
    f₁ * f₂ = q ^ 2 * f₃ := by
  intro B ρ M χ lam Θ
  have hone := fun c (_ : c ∈ B) (hdeg1 : (basis.representation c).character 1 = 1) =>
    degree_one_eq_principal_of_simple hnonab basis hprincipal c hdeg1
  have hf₁1 := one_lt_degree_of_ne_principal basis (Ne.symm h01) (hone c₁ hc₁B) hf₁
  have hf₂1 := one_lt_degree_of_ne_principal basis (Ne.symm h02) (hone c₂ hc₂B) hf₂
  have hf₃1 := one_lt_degree_of_ne_principal basis (Ne.symm h03) (hone c₃ hc₃B) hf₃
  obtain ⟨hΘ, hsign, hQ, hprod⟩ := principal_Fourier_odd_degree_product_of_degrees hn e basis
    ideal principal hprincipal c₁ c₂ c₃ hc₁B hc₂B hc₃B h01 h02 h03 h12 h13 h23 hodd f₁ f₂ f₃
    hf₁ hf₂ hf₃ q (by omega) ε δ₁ δ₂ δ₃ hε hδ₁ hδ₂ hδ₃ Φ hΦ hΦ1 hχ₁ hχ₂ hχ₃ hdeg hf₁1 hf₂1
    hf₃1
  have hlam : lam ⟨ρ, Subgroup.mem_zpowers ρ⟩ = -1 := by
    have h := cyclicLinearCharacter_zpow (suppliedRotation_orderOf (n := n) (by omega) e)
      ((modulus n / 2 : ℕ) : ℤ) 1
    rw [mul_one, cyclicRoot_zpow_half hn] at h
    rw [← h]
    congr 1
    exact Subtype.ext (zpow_one _).symm
  exact ⟨hlam, hΘ, hf₁1, hf₂1, hf₃1, hsign, hQ, hprod⟩

end CFSG.Semidihedral.Principal
