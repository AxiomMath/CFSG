module

public import CFSG.CharacterTheory.Wreathed.FourPointOrderFourBases
public import CFSG.CharacterTheory.Wreathed.PrincipalSectionColumns

public noncomputable section

namespace CFSG.Wreathed.FourPointGaussianColumns

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.FourPointOrderFour

open scoped BigOperators Classical Matrix

theorem odd_iff_not_two_dvd (n : ℕ) : Odd n ↔ ¬ 2 ∣ n := by
  rw [← even_iff_two_dvd, Nat.not_even_iff_odd]

theorem exists_coeff_of_mem_span {K : Type} [Group K] [Fintype K]
    (basis : FiniteIrreducibleCharacterBasis K) (B : Finset basis.index) (f : K → ℂ)
    (hf : f ∈ Submodule.span ℂ
      ((fun θ => (basis.representation θ).character) '' (B : Set basis.index))) :
    ∃ c : basis.index → ℂ, f = ∑ θ ∈ B, c θ • (basis.representation θ).character := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨θ₀, hθ₀, rfl⟩ := hg
    refine ⟨fun θ => if θ = θ₀ then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single θ₀ (fun θ _ hθ => by simp [hθ]) (fun h => absurd hθ₀ h)]
    simp
  | zero => exact ⟨0, by simp⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨c, rfl⟩ := hg
    obtain ⟨c', rfl⟩ := hg'
    exact ⟨c + c', by rw [← Finset.sum_add_distrib]; simp [add_smul]⟩
  | smul a g _ hg =>
    obtain ⟨c, rfl⟩ := hg
    exact ⟨a • c, by rw [Finset.smul_sum]; simp [smul_smul]⟩

theorem section_rows_of_oddRestrictionBasis {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {u : G} {r : ℕ} (hr : 1 ≤ r)
    (hu : orderOf u = 2 ^ r) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ r)) (K : Subgroup G)
    (hK : Subgroup.centralizer (Subgroup.zpowers u : Set G) = K)
    (localBasis : FiniteIrreducibleCharacterBasis K) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (b : Fin 2 → OddElements K → ℂ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hb : OddRestrictionComplexBasis localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal) b M) :
    ∃ V : basis.index → Fin 2 → ℂ,
      (∀ χ j, V χ j ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ y : OddElements K,
          (basis.representation χ).character (u * y) = ∑ j, V χ j * b j y) ∧
      (∀ j k, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        starRingEnd ℂ (V χ j) * V χ k = M j k) ∧
      (∀ j, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        V χ j * starRingEnd ℂ ((basis.representation χ).character 1) = 0) := by
  subst hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B₀K := coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal
    with hB₀K
  obtain ⟨D, hDrow, hDgram⟩ := hb.rows
  set b' : Fin 2 → Subgroup.centralizer (Subgroup.zpowers u : Set G) → ℂ :=
    fun j y => if h : Odd (orderOf y) then b j ⟨y, h⟩ else 0 with hb'def
  set d : localBasis.index → Fin 2 → ℤ :=
    fun θ j => if h : θ ∈ B₀K then D ⟨θ, h⟩ j else 0 with hddef
  have hb' : ∀ j (y : OddElements (Subgroup.centralizer (Subgroup.zpowers u : Set G))),
      b' j y = b j y := fun j y => dite_eq_left y.2
  have hbmem : ∀ j, ∃ c : localBasis.index → ℂ, ∀ y, ¬ 2 ∣ orderOf y →
      b' j y = ∑ θ ∈ B₀K, c θ * (localBasis.representation θ).character y := by
    intro j
    have hmem : b j ∈ (Submodule.span ℂ ((fun θ => (localBasis.representation θ).character) ''
        (B₀K : Set localBasis.index))).map (LinearMap.funLeft ℂ ℂ Subtype.val) := by
      rw [← hb.span_eq]
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨f, hf, hfb⟩ := Submodule.mem_map.mp hmem
    obtain ⟨c, rfl⟩ := exists_coeff_of_mem_span localBasis B₀K f hf
    refine ⟨c, fun y hy => ?_⟩
    have hodd : Odd (orderOf y) := (odd_iff_not_two_dvd _).mpr hy
    have h := congrFun hfb ⟨y, hodd⟩
    rw [LinearMap.funLeft_apply] at h
    rw [hb' j ⟨y, hodd⟩, ← h]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hbindep : ∀ c : Fin 2 → ℂ, (∀ y, ¬ 2 ∣ orderOf y → ∑ j, c j * b' j y = 0) → c = 0 := by
    intro c hc
    funext j
    refine Fintype.linearIndependent_iff.mp hb.linearIndependent c ?_ j
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h := hc g.1 ((odd_iff_not_two_dvd _).mp g.2)
    simp only [hb'] at h
    exact h
  have hd : ∀ θ ∈ B₀K, ∀ y, ¬ 2 ∣ orderOf y →
      (localBasis.representation θ).character y = ∑ j, (d θ j : ℂ) * b' j y := by
    intro θ hθ y hy
    have hodd : Odd (orderOf y) := (odd_iff_not_two_dvd _).mpr hy
    have h := (hDrow ⟨θ, hθ⟩ fun j => (D ⟨θ, hθ⟩ j : ℂ)).mpr (fun j => rfl) ⟨y, hodd⟩
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb' j ⟨y, hodd⟩]
    simp only [hddef, dite_eq_left hθ]
  obtain ⟨U, m, lam, -, -, -, hUint, hrow, -, hgram, hvanish⟩ :=
    principal_primary_section_cyclotomic_basis_columns basis ideal 2 principal hprincipal hr hu
      localBasis localPrincipal hlocalPrincipal hζ 2 (by norm_num) b' hbmem hbindep d hd
  refine ⟨U, hUint, ?_, ?_, ?_⟩
  · intro χ hχ y
    rw [hrow χ hχ y.1 ((odd_iff_not_two_dvd _).mp y.2)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb']
  · intro j k
    rw [hgram j k]
    have hsum : ∑ θ ∈ B₀K, d θ j * d θ k = (Dᵀ * D) j k := by
      rw [Matrix.mul_apply, ← Finset.sum_coe_sort B₀K]
      refine Finset.sum_congr rfl fun θ _ => ?_
      simp only [hddef, dite_eq_left θ.2, Matrix.transpose_apply]
    rw [hDgram] at hsum
    rw [← hsum]
    push_cast
    rfl
  · intro j
    refine hvanish 1 (fun a c hac _ he hc hconj => ?_) j
    obtain ⟨e, he⟩ := he
    have hca : c = a⁻¹ := eq_inv_of_mul_eq_one_right hac
    rw [hca, orderOf_inv, he] at hc
    have he0 : e = 0 := by
      by_contra h
      exact hc (dvd_pow_self 2 h)
    rw [he0, pow_zero, orderOf_eq_one_iff] at he
    rw [he, isConj_one_right] at hconj
    rw [hconj, orderOf_one] at hu
    exact absurd hu (Nat.one_lt_two_pow (by omega)).ne

end CFSG.Wreathed.FourPointGaussianColumns
