module

public import CFSG.CharacterTheory.Wreathed.ConditionalCentralPowerRegularBases
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsAlgebra
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralInvolutionSectionMask
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionIntegralColumns

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalFourier

open CFSG.TwoRankLowerBound.Helpers

theorem sum_range_sub_one_mul_pow_int {ζ : ℂ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m)
    (j : ℕ) {s : ℂ} (hs : s ^ m = 1) :
    ∃ n : ℤ, (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m, (ζ ^ (j * k) - 1) * s ^ k = n := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨e, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hs
  have hterm : ∀ k, (ζ ^ (j * k) - 1) * (ζ ^ e) ^ k = ζ ^ ((j + e) * k) - ζ ^ (e * k) := by
    intro k
    rw [← pow_mul, add_mul, pow_add]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib, sum_range_pow_mul hζ,
    sum_range_pow_mul hζ]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨(if m ∣ j + e then 1 else 0) - (if m ∣ e then 1 else 0), ?_⟩
  split_ifs <;> simp [hm0]

theorem character_pow_mul_of_scalar {H : Type*} [Group H] (data : FiniteComplexRepresentation H)
    (z : H) (s : ℂ) (hs : data.representation z = s • 1) (k : ℕ) (c : H) :
    data.character (z ^ k * c) = s ^ k * data.character c := by
  rw [FiniteComplexRepresentation.character, Representation.character, map_mul, map_pow, hs,
    smul_pow, one_pow, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  rfl

theorem fourier_difference_integer_expansion {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index) {C : Subgroup G}
    (localBasis : FiniteIrreducibleCharacterBasis C) {a : G} (haC : a ∈ C)
    (hcomm : ∀ c ∈ C, c * a = a * c) {m : ℕ} (hm : orderOf a = m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (j : ℕ) :
    ∃ N : localBasis.index → ℤ, ∀ c : C,
      (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m, (ζ ^ (j * k) - 1) *
          (basis.representation χ).character (a ^ k * c) =
        ∑ θ, (N θ : ℂ) * (localBasis.representation θ).character c := by
  obtain ⟨z, hz⟩ : ∃ z : C, (z : G) = a := ⟨⟨a, haC⟩, rfl⟩
  have hzc : z ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun c => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
    exact hcomm c c.2)
  have hm0 : 0 < m := by
    rw [← hm]
    exact orderOf_pos a
  have hzm : z ^ m = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hz, ← hm, pow_orderOf_eq_one, Subgroup.coe_one])
  choose s hs using fun θ => irreducible_central_scalar_root (localBasis.representation θ)
    (localBasis.irreducible θ) z hzc m hm0 hzm
  have hspow : ∀ θ, (s θ : ℂ) ^ m = 1 := fun θ => by
    have h := congrArg Subtype.val (hs θ).1
    simpa using h
  choose μ hμ using fun θ =>
    CFSG.Semidihedral.Principal.restriction_pairing_nat basis localBasis χ θ
  choose w hw using fun θ => sum_range_sub_one_mul_pow_int hζ hm0 j (hspow θ)
  refine ⟨fun θ => μ θ * w θ, fun c => ?_⟩
  have hclass : ∀ c g : C, (basis.representation χ).character ((g * c * g⁻¹ : C) : G) =
      (basis.representation χ).character (c : G) := fun c g => by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Representation.char_conj _ _ _
  have hres : ∀ k : ℕ, (basis.representation χ).character (a ^ k * c) =
      ∑ θ, (μ θ : ℂ) * (s θ : ℂ) ^ k * (localBasis.representation θ).character c := by
    intro k
    have h : (basis.representation χ).character ((z ^ k * c : C) : G) =
        ∑ θ, characterPairing (fun c : C => (basis.representation χ).character (c : G))
          (localBasis.representation θ).character *
          (localBasis.representation θ).character (z ^ k * c) :=
      finiteIrreducibleCharacterBasis_reconstruction localBasis
        (fun c : C => (basis.representation χ).character (c : G)) hclass (z ^ k * c)
    rw [Subgroup.coe_mul, Subgroup.coe_pow, hz] at h
    rw [h]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [hμ θ, character_pow_mul_of_scalar _ z _ (hs θ).2 k c]
    ring
  rw [Finset.sum_congr rfl fun k _ => by rw [hres k, Finset.mul_sum], Finset.sum_comm,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun θ _ => ?_
  push_cast
  rw [← hw θ]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem eq_zero_of_odd_combination {E : Type*} [Group E] (Φ : E → ℂ) (ε : ℤ) (q : ℕ)
    (hq : Φ 1 = q)
    (hind : LinearIndependent ℤ ![oddRestriction (1 : E → ℂ), oddRestriction (1 + (ε : ℂ) • Φ)])
    {α β : ℂ} (h : ∀ y : E, Odd (orderOf y) → α + β * (1 + ε * Φ y) = 0) : α = 0 ∧ β = 0 := by
  have h1 := h 1 (by rw [orderOf_one]; exact odd_one)
  rw [hq] at h1
  by_cases hβ : β = 0
  · rw [hβ, zero_mul, add_zero] at h1
    exact ⟨h1, hβ⟩
  · exfalso
    have hconst : ∀ y : E, Odd (orderOf y) → (1 + ε * Φ y : ℂ) = 1 + ε * q := fun y hy => by
      have hdiff : β * ((1 + ε * Φ y) - (1 + ε * q)) = 0 := by linear_combination h y hy - h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hβ)
    have hrel : (1 + ε * q : ℤ) • oddRestriction (1 : E → ℂ) +
        (-1 : ℤ) • oddRestriction (1 + (ε : ℂ) • Φ) = 0 := by
      funext y
      simp only [oddRestriction, Pi.add_apply, Pi.mul_apply, Pi.intCast_apply, Pi.one_apply,
        Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Pi.zero_apply]
      rw [hconst y.1 y.2]
      push_cast
      ring
    have := (LinearIndependent.pair_iff.mp hind _ _ hrel).2
    norm_num at this

theorem fourierTransform_integral_of_regular_basis {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    {a : G} {m : ℕ} (hm : orderOf a = m) (hm2 : ∃ r : ℕ, m = 2 ^ r)
    (C : Subgroup G) (hC : C = Subgroup.centralizer {a})
    (localBasis : FiniteIrreducibleCharacterBasis C) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (Φ : C → ℂ) (ε : ℤ) (q : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdata : PrincipalRegularIntegralBasisData localBasis ideal localPrincipal Φ ε q M)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (χ : basis.index) (v : ℕ → Fin 2 → ℂ)
    (hv : ∀ k ∈ Finset.Ico 1 m, ∀ y : C, Odd (orderOf y) →
      (basis.representation χ).character (a ^ k * y) = v k 0 + v k 1 * (1 + ε * Φ y))
    {j : ℕ} (hj1 : 1 ≤ j) (hjm : j < m) (ℓ : Fin 2) :
    ∃ z : ℤ, fourierTransform m ζ (fun k => v k ℓ) j = z := by
  have hm0 : 0 < m := by omega
  have haC : a ∈ C := by
    rw [hC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcomm : ∀ c ∈ C, c * a = a * c := fun c hc => by
    rw [hC] at hc
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  set f : Fin 2 → ℂ := fun ℓ => fourierTransform m ζ (fun k => v k ℓ) j with hfdef
  obtain ⟨N, hN⟩ := fourier_difference_integer_expansion basis χ localBasis haC hcomm hm hζ j
  set Δ : C → ℂ := fun c => ∑ θ, (N θ : ℂ) * (localBasis.representation θ).character c
    with hΔdef
  have hΔodd : ∀ y : C, Odd (orderOf y) → Δ y = f 0 + f 1 * (1 + ε * Φ y) := by
    intro y hy
    have hsplit : ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) *
        (basis.representation χ).character (a ^ k * y) =
        ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) * v k 0 +
          (∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) * v k 1) * (1 + ε * Φ y) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hv k hk y hy]
      ring
    have hΔy : Δ y = (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m, (ζ ^ (j * k) - 1) *
        (basis.representation χ).character (a ^ k * y) := (hN y).symm
    rw [hΔy, Finset.sum_range_eq_add_Ico _ hm0]
    simp only [mul_zero, pow_zero, sub_self, zero_mul, zero_add]
    rw [hsplit, hfdef]
    simp only [fourierTransform]
    ring
  have hcommute := coefficientBlock_section_mask_commute localBasis ideal 2 localPrincipal
    {c : C | Odd (orderOf c)} oddOrderElements_primeSectionUnion
  have hmem := coefficientBlock_section_mask_mem localBasis ideal 2 localPrincipal
    {c : C | Odd (orderOf c)} oddOrderElements_primeSectionUnion
  have hspan := hdata.span
  obtain ⟨l, hl, hlΦ⟩ := hdata.irreducible
  have hpr := coefficientBlock_self_mem localBasis (localizedComplexIntegerRing ideal)
    localPrincipal
  set B₀ := coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal
    with hB₀
  set F : C → ℂ := f 0 • (1 : C → ℂ) + f 1 • (1 + (ε : ℂ) • Φ) with hFdef
  have hone : (1 : C → ℂ) ∈ coefficientCharacterSpace localBasis B₀ := by
    rw [← hlocalPrincipal]
    exact Submodule.subset_span ⟨localPrincipal, hpr, rfl⟩
  have hΦ : Φ ∈ coefficientCharacterSpace localBasis B₀ := by
    rw [← hlΦ]
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  have hF : F ∈ coefficientCharacterSpace localBasis B₀ :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hone)
      (Submodule.smul_mem _ _ (Submodule.add_mem _ hone (Submodule.smul_mem _ _ hΦ)))
  have hmaskΔ : characterFunctionMask {c : C | Odd (orderOf c)} Δ =
      characterFunctionMask {c : C | Odd (orderOf c)} F := by
    funext c
    simp only [characterFunctionMask]
    split_ifs with hc
    · rw [hΔodd c hc, hFdef]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    · rfl
  have hmask : characterFunctionMask {c : C | Odd (orderOf c)}
      (characterSubsetProjection localBasis B₀ Δ) =
      characterFunctionMask {c : C | Odd (orderOf c)} F := by
    rw [← hcommute Δ, hmaskΔ, characterSubsetProjection_identity localBasis B₀ _ (hmem F hF)]
  have hPodd : ∀ y : C, Odd (orderOf y) →
      characterSubsetProjection localBasis B₀ Δ y = f 0 + f 1 * (1 + ε * Φ y) := by
    intro y hy
    have hy' : y ∈ {c : C | Odd (orderOf c)} := hy
    have h := congrFun hmask y
    simp only [characterFunctionMask, ite_eq_left hy'] at h
    rw [h, hFdef]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  have hPN : ∀ c : C, characterSubsetProjection localBasis B₀ Δ c =
      ∑ θ ∈ B₀, (N θ : ℂ) * (localBasis.representation θ).character c := by
    intro c
    rw [CFSG.RankTwoShapes.characterSubsetProjection_apply']
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [hΔdef, characterPairing_distinct_expansion_coefficient localBasis.representation
      localBasis.irreducible localBasis.distinct (fun θ => (N θ : ℂ)) θ]
  have hlattice : oddRestriction (characterSubsetProjection localBasis B₀ Δ) ∈
      oddRestrictionLattice localBasis B₀ := by
    have heq : oddRestriction (characterSubsetProjection localBasis B₀ Δ) =
        ∑ θ ∈ B₀, N θ • oddRestriction (localBasis.representation θ).character := by
      funext y
      simp only [oddRestriction, Finset.sum_apply, zsmul_eq_mul]
      exact hPN y.1
    rw [heq]
    exact Submodule.sum_mem _ fun θ hθ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨θ, hθ, rfl⟩)
  rw [← hspan] at hlattice
  obtain ⟨z₀, z₁, hz⟩ := Submodule.mem_span_pair.mp hlattice
  have hzodd := (oddRestriction_eq_zsmul_add_iff _ _ _ z₀ z₁).mp hz.symm
  have hcmp := eq_zero_of_odd_combination Φ ε q hdata.degree hdata.linearIndependent
    (α := f 0 - z₀) (β := f 1 - z₁) fun y hy => by
      have h1 := hPodd y hy
      have h2 := hzodd y hy
      simp only [Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one] at h2
      linear_combination h2 - h1
  obtain rfl | rfl : ℓ = 0 ∨ ℓ = 1 := by fin_cases ℓ <;> simp
  · exact ⟨z₀, sub_eq_zero.mp hcmp.1⟩
  · exact ⟨z₁, sub_eq_zero.mp hcmp.2⟩

end CFSG.Wreathed.ConditionalFourier
