module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseSections
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsSections
public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsSupport

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FourPointRemainingOrderFour

open CFSG.TwoRankLowerBound.Helpers

theorem exists_eq_add_mul_of_mem_adjoin {ζ : ℂ} (hζ : ζ ^ 2 = -1) {t : ℂ}
    (ht : t ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) : ∃ p q : ℤ, t = p + q * ζ := by
  induction ht using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by rw [hy]; push_cast; ring⟩
  | algebraMap k => exact ⟨k, 0, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨p, q, rfl⟩ := hy
    obtain ⟨p', q', rfl⟩ := hy'
    exact ⟨p + p', q + q', by push_cast; ring⟩
  | mul y y' _ _ hy hy' =>
    obtain ⟨p, q, rfl⟩ := hy
    obtain ⟨p', q', rfl⟩ := hy'
    exact ⟨p * p' - q * q', p * q' + q * p', by
      push_cast
      linear_combination ((q : ℂ) * q') * hζ⟩

theorem exists_int_of_mem_adjoin {ζ : ℂ} (hζ : ζ ^ 2 = -1) {t : ℂ}
    (ht : t ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) (hreal : conj t = t) : ∃ k : ℤ, t = k := by
  obtain ⟨p, q, rfl⟩ := exists_eq_add_mul_of_mem_adjoin hζ ht
  have hre := congrArg Complex.re hζ
  have him := congrArg Complex.im hζ
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.one_re,
    Complex.neg_im, Complex.one_im, neg_zero] at hre him
  have hζim : ζ.im ≠ 0 := by
    intro h0
    rw [h0] at hre
    nlinarith [sq_nonneg ζ.re]
  have h := congrArg Complex.im hreal
  simp only [Complex.conj_im, Complex.add_im, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, add_zero, zero_add] at h
  have hq : (q : ℝ) * ζ.im = 0 := by linarith
  have hq0 : (q : ℂ) = 0 := by
    have : (q : ℝ) = 0 := (mul_eq_zero.mp hq).resolve_right hζim
    exact_mod_cast this
  exact ⟨p, by rw [hq0, zero_mul, add_zero]⟩

theorem section_columns_of_comm {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {u : G} {r : ℕ} (hr : 1 ≤ r) (hu : orderOf u = 2 ^ r)
    (N : Subgroup (Subgroup.centralizer ({u} : Set G))) [N.Normal] (hN : Odd (Nat.card N))
    (hquotient : IsPGroup 2 (Subgroup.centralizer ({u} : Set G) ⧸ N))
    (hcomm : ∀ p q : Subgroup.centralizer ({u} : Set G) ⧸ N, p * q = q * p)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ r)) :
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ y ∈ Subgroup.centralizer ({u} : Set G), ¬ 2 ∣ orderOf y →
        (basis.representation χ).character (u * y) = (basis.representation χ).character u) ∧
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character u ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
    (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        conj ((basis.representation χ).character u) * (basis.representation χ).character u =
      Nat.card (Subgroup.centralizer ({u} : Set G) ⧸ N)) ∧
    ∀ g : G, (∀ a c : G, a * c = g → Commute a c →
      (∃ e : ℕ, orderOf a = 2 ^ e) → ¬ 2 ∣ orderOf c → ¬ IsConj a u) →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character u *
          conj ((basis.representation χ).character g) = 0 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : NeZero (2 ^ r) := ⟨pow_ne_zero _ (by decide)⟩
  have hCD := CFSG.BlockBasics.centralizer_zpowers_eq_centralizer_singleton u
  let e₀ : Subgroup.centralizer (Subgroup.zpowers u : Set G) ≃*
      Subgroup.centralizer ({u} : Set G) := MulEquiv.subgroupCongr hCD
  let N' : Subgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G)) := N.comap e₀.toMonoidHom
  have : N'.Normal := Subgroup.Normal.comap inferInstance _
  have hN' : Odd (Nat.card N') := by
    rw [show N' = N.map e₀.symm.toMonoidHom from Subgroup.comap_equiv_eq_map_symm e₀ N,
      Subgroup.card_map_of_injective e₀.symm.injective]
    exact hN
  let ψ : Subgroup.centralizer (Subgroup.zpowers u : Set G) ⧸ N' ≃*
      Subgroup.centralizer ({u} : Set G) ⧸ N :=
    QuotientGroup.congr N' N e₀ (Subgroup.map_comap_eq_self_of_surjective e₀.surjective N)
  have hquotient' : IsPGroup 2 (Subgroup.centralizer (Subgroup.zpowers u : Set G) ⧸ N') :=
    hquotient.of_equiv ψ.symm
  have : IsMulCommutative (Subgroup.centralizer (Subgroup.zpowers u : Set G) ⧸ N') :=
    ⟨⟨fun p q => ψ.injective (by rw [map_mul, map_mul, hcomm])⟩⟩
  let localBasis : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) :=
    Classical.choice finiteIrreducibleCharacterBasis_exists
  obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
    finiteIrreducibleCharacterBasis_contains_irreducible localBasis
      (principalFiniteComplexRepresentation _)
      (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨hbmem, hbindep, hd⟩ := ConditionalGeneralBase.principal_singleton_integral_basis_of_comm
    localBasis ideal localPrincipal hlocalPrincipal N' hN' hquotient'
  obtain ⟨U, m, lam, _, _, _, hadj, hvalues, _, hgram, hoff⟩ :=
    CFSG.Wreathed.principal_primary_section_cyclotomic_basis_columns basis ideal 2 principal
      hprincipal hr hu localBasis localPrincipal hlocalPrincipal hζ 1 (by omega)
      (fun _ _ => 1) hbmem hbindep (fun _ _ => 1) hd
  have hU : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      U χ 0 = (basis.representation χ).character u := by
    intro χ hχ
    simpa using (hvalues χ hχ 1 (by norm_num)).symm
  refine ⟨fun χ hχ y hy hyodd => ?_, fun χ hχ => ?_, ?_, fun g hg => ?_⟩
  · have hy' : y ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G) := hCD ▸ hy
    have h := hvalues χ hχ ⟨y, hy'⟩ (by rwa [Subgroup.orderOf_mk])
    simpa [hU χ hχ] using h
  · rw [← hU χ hχ]
    exact hadj χ 0
  · have h := hgram 0 0
    rw [Finset.sum_congr rfl fun χ hχ => by rw [hU χ hχ]] at h
    rw [h]
    simp only [mul_one, Int.cast_one, Finset.sum_const, nsmul_eq_mul]
    rw [ConditionalGeneralBase.card_principal_block_of_comm localBasis ideal localPrincipal
      hlocalPrincipal N' hN' hquotient', Nat.card_congr ψ.toEquiv]
  · have h := hoff g hg 0
    rwa [Finset.sum_congr rfl fun χ hχ => by rw [hU χ hχ]] at h

theorem not_isConj_two_part {G : Type} [Group G] {g a₀ c₀ u : G} (hg : a₀ * c₀ = g)
    (hcomm : Commute a₀ c₀) (ha₀ : ∃ e : ℕ, orderOf a₀ = 2 ^ e) (hc₀ : Odd (orderOf c₀))
    (hnot : ¬ IsConj a₀ u) :
    ∀ a c : G, a * c = g → Commute a c → (∃ e : ℕ, orderOf a = 2 ^ e) → ¬ 2 ∣ orderOf c →
      ¬ IsConj a u := by
  intro a c hac hcomm' ha hc
  have hc' : Odd (orderOf c) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hc)
  rw [← ConditionalFourier.two_part_unique hg hcomm ha₀ hc₀ hac hcomm' ha hc']
  exact hnot

theorem sum_mul_re_imCoeff_eq_zero {ι : Type*} (B : Finset ι) (W v : ι → ℂ) (i : ℂ)
    (h₁ : ∑ χ ∈ B, W χ * v χ = 0) (h₂ : ∑ χ ∈ B, W χ * conj (v χ) = 0) :
    ∑ χ ∈ B, W χ * ((v χ).re : ℂ) = 0 ∧
      ∑ χ ∈ B, W χ * ((FourPointGaussianColumns.imCoeff i (v χ) : ℝ) : ℂ) = 0 := by
  have hre : ∑ χ ∈ B, W χ * ((v χ).re : ℂ) =
      (∑ χ ∈ B, W χ * v χ + ∑ χ ∈ B, W χ * conj (v χ)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.re_eq_add_conj]
    ring
  have him : ∑ χ ∈ B, W χ * ((FourPointGaussianColumns.imCoeff i (v χ) : ℝ) : ℂ) =
      (∑ χ ∈ B, W χ * v χ - ∑ χ ∈ B, W χ * conj (v χ)) / (2 * Complex.I) / (i.im : ℂ) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_div]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [FourPointGaussianColumns.imCoeff, Complex.ofReal_div, Complex.im_eq_sub_conj]
    ring
  rw [hre, him, h₁, h₂]
  simp

end CFSG.Wreathed.FourPointRemainingOrderFour
