module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneSignedDegrees
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneExtension
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneOrderBound
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneNumerics
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.Principal CFSG.TwoRankLowerBound.Helpers

theorem principal_family_cubic_moment {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (t : G)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (e : ℤ) (he : e = 1 ∨ e = -1) (k : ℕ) (hk : 1 ≤ k) (φ : C t → ℂ)
    (hφ1 : φ 1 = q) (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e k φ
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄) :
    1 + δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) +
        δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) +
        δ₃ * (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) = 0 ∧
    δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) *
        (δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ)) =
      (q : ℤ) ^ 2 * (δ₃ * (Module.finrank ℂ (basis.representation χ₃).vector : ℤ)) ∧
    1 + δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) ≠ 0 ∧
    1 + δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) ≠ 0 ∧
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character t ^ 3 / (basis.representation χ).character 1 =
      1 + (e : ℂ) * (q : ℂ) ^ 3 /
          ((δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) : ℤ) : ℂ) -
        (e : ℂ) * (q : ℂ) ^ 3 /
          ((δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) : ℤ) : ℂ) -
        1 / ((δ₃ * (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) : ℤ) : ℂ) -
        (1 - (e : ℂ) * q) ^ 3 /
          (1 + ((δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) : ℤ) : ℂ)) -
        (1 + (e : ℂ) * q) ^ 3 /
          (1 + ((δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) : ℤ) : ℂ)) := by
  obtain ⟨-, hδ₁, hδ₂, hδ₃, hδ₄, hnd, hψinj, hνinj, hψne, hνne, hνψ, hB, -, -, hsec, hrel⟩ :=
    hfam
  obtain ⟨hf₁, hf₂, -, -, hsigns, hδ₄₂, hf₄, hprod, -⟩ := hdeg
  set f : basis.index → ℤ := fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ)
    with hfdef
  have hdeg1 : ∀ χ : basis.index, (basis.representation χ).character 1 = (f χ : ℂ) := fun χ => by
    rw [(basis_character_one basis χ).1]
    simp [hfdef]
  obtain ⟨hv1, hv2, hv3, hv4, hvψ, hvν⟩ := hsec 1 (by rw [orderOf_one]; exact odd_one)
  simp only [OneMemClass.coe_one, mul_one, hφ1] at hv1 hv2 hv3 hv4 hvψ hvν
  obtain ⟨hψ1, hν1, hr1, -⟩ := hrel 1 (by rw [orderOf_one]; exact odd_one)
  have hvp : (basis.representation principal).character t = 1 := by rw [hprincipal]; rfl
  have hdp : (basis.representation principal).character 1 = 1 := by rw [hprincipal]; rfl
  have hsum : 1 + δ₁ * f χ₁ + δ₂ * f χ₂ + δ₃ * f χ₃ = 0 := by
    rw [hdeg1, hdeg1, hdeg1] at hr1
    exact_mod_cast hr1
  have hδ₁₂ : δ₁ * δ₂ = δ₃ := by
    rcases hsigns with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> norm_num
  have hconic : δ₁ * f χ₁ * (δ₂ * f χ₂) = (q : ℤ) ^ 2 * (δ₃ * f χ₃) := by
    have h : f χ₁ * f χ₂ = (q : ℤ) ^ 2 * f χ₃ := by
      simp only [hfdef]
      exact_mod_cast hprod
    rw [← hδ₁₂]
    linear_combination (δ₁ * δ₂) * h
  have hne : ∀ {δ' : ℤ} {g : ℕ}, (δ' = 1 ∨ δ' = -1) → 1 < g → 1 + δ' * (g : ℤ) ≠ 0 :=
    fun h hg => by rcases h with rfl | rfl <;> omega
  refine ⟨hsum, hconic, hne hδ₁ hf₁, hne hδ₂ hf₂, ?_⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hnd
  have hdisj1 : Disjoint ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index)
      ((Finset.Icc 1 (k - 1)).image ψ) := by
    rw [Finset.disjoint_left]
    intro x hx hxψ
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hxψ
    obtain ⟨a0, a1, a2, a3, a4⟩ := hψne l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h | h <;> contradiction
  have hdisj2 : Disjoint (({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index) ∪
      (Finset.Icc 1 (k - 1)).image ψ) ((Finset.range k).image ν) := by
    rw [Finset.disjoint_left]
    intro x hx hxν
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxν
    obtain ⟨a0, a1, a2, a3, a4⟩ := hνne i hi
    rcases Finset.mem_union.mp hx with hx | hx
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h | h | h <;> contradiction
    · obtain ⟨l, hl, hlν⟩ := Finset.mem_image.mp hx
      exact hνψ i hi l hl hlν.symm
  rw [hB, Finset.sum_union hdisj2, Finset.sum_union hdisj1,
    Finset.sum_image fun x hx y hy hxy => hψinj (Finset.mem_coe.mpr hx)
      (Finset.mem_coe.mpr hy) hxy,
    Finset.sum_image fun x hx y hy hxy => hνinj (Finset.mem_coe.mpr hx)
      (Finset.mem_coe.mpr hy) hxy,
    Finset.sum_insert (by simp [h01, h02, h03, h04]),
    Finset.sum_insert (by simp [h12, h13, h14]), Finset.sum_insert (by simp [h23, h24]),
    Finset.sum_insert (by simp [h34]), Finset.sum_singleton]
  have hk1' : (((k - 1 + 1 - 1 : ℕ)) : ℂ) = (k : ℂ) - 1 := by
    rw [show k - 1 + 1 - 1 = k - 1 by omega, Nat.cast_sub hk, Nat.cast_one]
  have hfψ : (δ₁ : ℂ) * ((f χ₁ : ℂ) + δ₁) = 1 + ((δ₁ * f χ₁ : ℤ) : ℂ) := by
    rcases hδ₁ with rfl | rfl <;> push_cast <;> ring
  have hψpart : ∑ l ∈ Finset.Icc 1 (k - 1), (basis.representation (ψ l)).character t ^ 3 /
      (basis.representation (ψ l)).character 1 = ((k : ℂ) - 1) * ((1 + (e : ℂ) * q) ^ 3 /
        (1 + ((δ₁ * f χ₁ : ℤ) : ℂ))) := by
    rw [Finset.sum_congr rfl fun (l : ℕ) (hl : l ∈ Finset.Icc 1 (k - 1)) => by
      rw [hvψ l hl, hψ1 l hl, hdeg1 χ₁, sign_cube_div hδ₁, hfψ], Finset.sum_const,
      Nat.card_Icc, nsmul_eq_mul, hk1']
  have hνpart : ∑ i ∈ Finset.range k, (basis.representation (ν i)).character t ^ 3 /
      (basis.representation (ν i)).character 1 = (k : ℂ) * ((-(1 + (e : ℂ) * q)) ^ 3 /
        (1 + ((δ₁ * f χ₁ : ℤ) : ℂ))) := by
    rw [Finset.sum_congr rfl fun (i : ℕ) (hi : i ∈ Finset.range k) => by
      rw [hvν i hi, hν1 i hi, hdeg1 χ₁, show -((δ₁ : ℂ) * (1 + (e : ℂ) * q)) =
        (δ₁ : ℂ) * (-(1 + (e : ℂ) * q)) by ring, sign_cube_div hδ₁, hfψ], Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  have hf4 : (δ₄ : ℂ) * (f χ₄ : ℂ) = -(1 + ((δ₂ * f χ₂ : ℤ) : ℂ)) := by
    have h : (f χ₄ : ℂ) = (f χ₂ : ℂ) + δ₂ := by
      simp only [hfdef]
      exact_mod_cast hf₄
    rw [h, hδ₄₂]
    rcases hδ₂ with rfl | rfl <;> push_cast <;> ring
  rw [hψpart, hνpart, hvp, hdp, hv1, hv2, hv3, hv4, hdeg1, hdeg1, hdeg1, hdeg1,
    show (δ₁ : ℂ) * e * q = (δ₁ : ℂ) * ((e : ℂ) * q) by ring,
    show -((δ₂ : ℂ) * e * q) = (δ₂ : ℂ) * (-((e : ℂ) * q)) by ring,
    show -(δ₃ : ℂ) = (δ₃ : ℂ) * (-1) by ring, sign_cube_div hδ₁, sign_cube_div hδ₂,
    sign_cube_div hδ₃, sign_cube_div hδ₄, hf4, div_neg]
  simp only [hfdef]
  push_cast
  rcases he with rfl | rfl <;> ring

open CFSG.Wreathed CFSG.Wreathed.LinearLocalTwistMoment in
theorem centralizer_linear_character_extends_of_order_bound
    (G : Type) [Group G] [Finite G] (hindex : ∀ V : Subgroup G, V.index ≠ 2)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hLnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hbound : 2 * p ^ f * Nat.card G *
        Nat.card (C t ⊓ Subgroup.centralizer ({(fS (s n) : G)} : Set G) : Subgroup G) ^ 2 <
      5 * Nat.card (C t) ^ 3 * (p ^ f - 1))
    (θ : C t →* ℂˣ) (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c) :
    ∃ lam : G →* ℂˣ, ∀ c : C t, lam c = θ c := by
  let _ : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨normalizerBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.normalizer ((S : Subgroup G) : Set G))
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨hM4, hKeven, hK2, hhalf⟩ := modulus_eq_four_mul hn
  set k : ℕ := 2 ^ (n - 3) with hk
  have hkpow : ∃ m : ℕ, k = 2 ^ m := ⟨n - 3, rfl⟩
  obtain ⟨lambdaLabel, hlambda, B, hB⟩ := exists_typeStar_block fS hn ht hindex θ hθS hθT basis
    ideal normalizerBasis
  obtain ⟨e, a₀, a₁, a₂, a₃, c₀, he1, he3, he, hqe, ha₀, ha₁, ha₂, ha₃, h01, h02, hsum, hrec,
      hc₀, hc₁, hc₂, hc₃, hSa, -, -, hext⟩ :=
    typeStar_signed_degrees fS hn ht hindex hLnonab hcentral hnc p f hp hpodd hf hmodel θ hθS
      hθT basis ideal normalizerBasis lambdaLabel hlambda B hB
  obtain ⟨F, hF, hFfin, ρ, hcard, -, -, -, hrest⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hindex t (orderOf_t fS hn ht)
      hLnonab hcentral hnc p f hp hpodd hf hmodel ideal basis (principalCharacterLabel basis)
      (principalCharacterLabel_character basis) localBasis (principalCharacterLabel localBasis)
      (principalCharacterLabel_character localBasis)
  obtain ⟨hφ1, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg, -, hOF⟩ := hrest
  have hcent : (fS (r n) : G) ^ (modulus n / 2) = t := by
    rw [ht, show modulus n / 2 = 2 ^ (n - 2) by omega]
  have hOF' := hOF S fS hcent
  have hqodd : Odd (p ^ f) := hpodd.pow
  have heS : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = e := by
    rw [hcard]
    split_ifs with h
    · exact (he1 h).symm
    · have h3 : p ^ f % 4 = 3 := by
        obtain ⟨m, hm⟩ := hqodd
        omega
      exact (he3 h3).symm
  rw [heS] at hfam hOF'
  rw [hcard] at hfam hOF' hdeg hφ1
  have hdeg' := hdeg
  obtain ⟨hf₁, hf₂, -⟩ := hdeg'
  have hfam' := hfam
  obtain ⟨-, hδ₁, hδ₂, -⟩ := hfam'
  obtain ⟨hsumS, hconicS, h1S, h2S, hSS⟩ := principal_family_cubic_moment basis ideal
    (principalCharacterLabel basis) (principalCharacterLabel_character basis) t localBasis
    (principalCharacterLabel localBasis) (p ^ f) e he k (by omega) _ hφ1 δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃
    χ₄ ψ ν hfam hdeg
  set q : ℤ := ((p ^ f : ℕ) : ℤ) with hqdef
  have hq3 : 3 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      obtain ⟨m, hm⟩ := hpodd
      omega
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  have hq3Z : 3 ≤ q := by rw [hqdef]; exact_mod_cast hq3
  have hqoddZ : Odd q := by rw [hqdef]; exact_mod_cast hqodd
  set s₁ : ℤ := δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) with hs₁
  set s₂ : ℤ := δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) with hs₂
  set s₃ : ℤ := δ₃ * (Module.finrank ℂ (basis.representation χ₃).vector : ℤ) with hs₃
  obtain ⟨hconic, -, hQrel⟩ := type_star_signed_degree_relations q e he k hK2 a₀ a₁ a₂ a₃ ha₀
    ha₁ ha₂ ha₃ h01 h02 hsum hrec hc₀ hc₃
  have hmom := typeStar_cubic_moment fS hn ht hindex θ hθS hθT basis ideal normalizerBasis
    lambdaLabel hlambda B hB
  rw [hSa, hSS] at hmom
  have heC : (e : ℂ) = 1 ∨ (e : ℂ) = -1 := by
    rcases he with h | h <;> rw [h] <;> norm_num
  have hqC : ((p ^ f : ℕ) : ℂ) = (q : ℂ) := by rw [hqdef, Int.cast_natCast]
  have hq1C : (q : ℂ) ^ 2 ≠ 1 := by
    intro h
    have h' : q ^ 2 = 1 := by exact_mod_cast h
    nlinarith
  have hqeC : (q : ℂ) + e ≠ 0 := by
    intro h
    have h' : q + e = 0 := by exact_mod_cast h
    rcases he with rfl | rfl <;> omega
  have hfa := cubic_moment_formula (q := (q : ℂ)) (e := (e : ℂ)) (a₀ := (a₀ : ℂ))
    (a₁ := (a₁ : ℂ)) (a₂ := (a₂ : ℂ)) (a₃ := (a₃ : ℂ)) heC hq1C hqeC (by exact_mod_cast ha₀)
    (by exact_mod_cast ha₁) (by exact_mod_cast h01) (by exact_mod_cast hsum)
    (by exact_mod_cast hconic)
  have hs₁0 : s₁ ≠ 0 := by
    rw [hs₁]
    rcases hδ₁ with rfl | rfl <;> omega
  have hfb := cubic_moment_formula (q := (q : ℂ)) (e := (e : ℂ)) (a₀ := (1 : ℂ))
    (a₁ := (s₁ : ℂ)) (a₂ := (s₂ : ℂ)) (a₃ := (s₃ : ℂ)) heC hq1C hqeC one_ne_zero
    (by exact_mod_cast hs₁0) (by exact_mod_cast h1S) (by exact_mod_cast hsumS)
    (by rw [mul_one]; exact_mod_cast hconicS)
  rw [hqC] at hmom
  rw [div_one] at hfb
  rw [hfa, hfb] at hmom
  have hfac : (4 : ℂ) * q / (q + e) ≠ 0 := by
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    exact div_ne_zero (mul_ne_zero (by norm_num) hq0) hqeC
  have hQ₁C := mul_left_cancel₀ hfac hmom
  have hQ₁ : ((a₁ - e * q * a₀) ^ 2 / (a₀ * a₁ * (a₀ + a₁)) : ℚ) =
      ((s₁ - e * q * 1) ^ 2 / (1 * s₁ * (1 + s₁)) : ℚ) := by
    have h : (((a₁ - e * q * a₀) ^ 2 / (a₀ * a₁ * (a₀ + a₁)) : ℚ) : ℂ) =
        (((s₁ - e * q * 1) ^ 2 / (1 * s₁ * (1 + s₁)) : ℚ) : ℂ) := by
      push_cast
      exact hQ₁C
    exact_mod_cast h
  have hbound' : 2 * p ^ f * Nat.card G *
      Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) ^ 2 <
      5 * Nat.card (C t) ^ 3 * (p ^ f - 1) := hbound
  obtain ⟨hB₁, hB₂, hrelS⟩ := principal_quotients_gt_of_order_bound (by omega) he hδ₁ hδ₂ hf₁
    hf₂ hOF' hbound'
  have hQS₁ : ((s₁ - e * q * 1) ^ 2 / (1 * s₁ * (1 + s₁)) : ℚ) =
      (((δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) : ℤ) : ℚ) -
          e * ((p ^ f : ℕ) : ℚ) * 1) ^ 2 /
        (1 * ((δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) : ℤ) : ℚ) *
          (1 + ((δ₁ * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) : ℤ) : ℚ))) := by
    rw [hs₁, hqdef]
    push_cast
    rfl
  have hQS₂ : ((s₂ + e * q * 1) ^ 2 / (1 * s₂ * (1 + s₂)) : ℚ) =
      (((δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) : ℤ) : ℚ) +
          e * ((p ^ f : ℕ) : ℚ) * 1) ^ 2 /
        (1 * ((δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) : ℤ) : ℚ) *
          (1 + ((δ₂ * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) : ℤ) : ℚ))) := by
    rw [hs₂, hqdef]
    push_cast
    rfl
  have hqQ : ((q : ℤ) : ℚ) = ((p ^ f : ℕ) : ℚ) := by rw [hqdef, Int.cast_natCast]
  have hqeQ : (q : ℚ) + e ≠ 0 := by
    intro h
    have h' : q + e = 0 := by exact_mod_cast h
    rcases he with rfl | rfl <;> omega
  have hQ₁' : (2 / 5 : ℚ) < (a₁ - e * q * a₀) ^ 2 / (a₀ * a₁ * (a₀ + a₁)) := by
    rw [hQ₁, hQS₁]
    exact hB₁
  have hQ₂' : (2 / 5 : ℚ) < (a₂ + e * q * a₀) ^ 2 / (a₀ * a₂ * (a₀ + a₂)) := by
    have h : ((a₂ + e * q * a₀) ^ 2 / (a₀ * a₂ * (a₀ + a₂)) : ℚ) =
        ((s₂ + e * q * 1) ^ 2 / (1 * s₂ * (1 + s₂)) : ℚ) := by
      apply mul_right_cancel₀ hqeQ
      rw [← hQrel, hQ₁, hQS₁, hQS₂, hqQ]
      exact hrelS
    rw [h, hQS₂]
    exact hB₂
  have ha01 : a₀ = 1 := type_star_degree_one q hq3Z hqoddZ e he k hK2 hkpow hqe a₀ a₁ a₂ a₃ ha₀
    ha₁ ha₂ ha₃ h01 h02 hsum hrec hc₀ hc₁ hc₂ hc₃ hQ₁' hQ₂'
  obtain ⟨hdeg₀, hval⟩ := hext ha01
  exact extends_of_degree_one fS hn ht hindex θ hθS basis c₀ hdeg₀ hval

end CFSG.Semidihedral.FieldFactorOne
