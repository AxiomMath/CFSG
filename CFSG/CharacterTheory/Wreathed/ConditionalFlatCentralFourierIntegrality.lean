module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCentralFourierRows
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsIntegrality

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FlatCentralFourier

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier

variable {G : Type} [Group G] [Fintype G]

theorem twisted_fourierTransform_integral (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {a : G} {m : ℕ} (hm : orderOf a = m)
    (C : Subgroup G) (hC : C = Subgroup.centralizer {a})
    (localBasis : FiniteIrreducibleCharacterBasis C) (ℓ : localBasis.index)
    (lamG ΦG : G → ℂ) (ε : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdata : TwistedRegularIntegralBasisData localBasis ideal ℓ (fun c => lamG c)
      (fun c => ΦG c) ε M)
    (hlam0 : ∀ c ∈ C, lamG c ≠ 0)
    (hindep : ∀ α β : ℂ, (∀ y ∈ C, Odd (orderOf y) → α + β * (1 + ε * ΦG y) = 0) →
      α = 0 ∧ β = 0)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (χ : basis.index) (v : ℕ → Fin 2 → ℂ)
    (hv : ∀ k ∈ Finset.Ico 1 m, ∀ y ∈ C, Odd (orderOf y) →
      (basis.representation χ).character (a ^ k * y) =
        lamG y * (v k 0 + v k 1 * (1 + ε * ΦG y)))
    {j : ℕ} (hj1 : 1 ≤ j) (hjm : j < m) (s : Fin 2) :
    ∃ z : ℤ, fourierTransform m ζ (fun k => v k s) j = z := by
  have hm0 : 0 < m := by omega
  have haC : a ∈ C := by
    rw [hC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcomm : ∀ c ∈ C, c * a = a * c := fun c hc => by
    rw [hC] at hc
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  set f : Fin 2 → ℂ := fun t => fourierTransform m ζ (fun k => v k t) j with hfdef
  obtain ⟨N, hN⟩ := fourier_difference_integer_expansion basis χ localBasis haC hcomm hm hζ j
  set Δ : C → ℂ := fun c => ∑ θ, (N θ : ℂ) * (localBasis.representation θ).character c
    with hΔdef
  have hΔodd : ∀ y : C, Odd (orderOf y) → Δ y = lamG y * (f 0 + f 1 * (1 + ε * ΦG y)) := by
    intro y hy
    have hy' : Odd (orderOf (y : G)) := by rwa [Subgroup.orderOf_coe]
    have hsplit : ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) *
        (basis.representation χ).character (a ^ k * y) =
        lamG y * (∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) * v k 0 +
          (∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) * v k 1) * (1 + ε * ΦG y)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hv k hk y y.2 hy']
      ring
    have hΔy : Δ y = (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m, (ζ ^ (j * k) - 1) *
        (basis.representation χ).character (a ^ k * y) := (hN y).symm
    rw [hΔy, Finset.sum_range_eq_add_Ico _ hm0]
    simp only [mul_zero, pow_zero, sub_self, zero_mul, zero_add]
    rw [hsplit, hfdef]
    simp only [fourierTransform]
    ring
  have hb0mem : oddRestriction (fun c : C => lamG c) ∈ oddRestrictionLattice localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ) := by
    rw [← hdata.span]
    exact Submodule.subset_span (Set.mem_insert _ _)
  have hb1mem : oddRestriction ((fun c : C => lamG c) * (1 + (ε : ℂ) • fun c : C => ΦG c)) ∈
      oddRestrictionLattice localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ) := by
    rw [← hdata.span]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨c₀, hc₀⟩ := exists_combination_of_mem_oddRestrictionLattice localBasis _ hb0mem
  obtain ⟨c₁, hc₁⟩ := exists_combination_of_mem_oddRestrictionLattice localBasis _ hb1mem
  set β := coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ with hβ
  set F : C → ℂ := ∑ θ ∈ β, (f 0 * c₀ θ + f 1 * c₁ θ) • (localBasis.representation θ).character
    with hFdef
  have hF : F ∈ coefficientCharacterSpace localBasis β :=
    Submodule.sum_mem _ fun θ hθ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨θ, hθ, rfl⟩)
  have hFodd : ∀ y : C, Odd (orderOf y) → F y = lamG y * (f 0 + f 1 * (1 + ε * ΦG y)) := by
    intro y hy
    have h0 := hc₀ y hy
    have h1 := hc₁ y hy
    simp only [Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [hFdef, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hsplit : lamG y * (f 0 + f 1 * (1 + ε * ΦG y)) =
        f 0 * lamG y + f 1 * (lamG y * (1 + ε * ΦG y)) := by ring
    rw [hsplit, h1, h0, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    ring
  have hcommute := coefficientBlock_section_mask_commute localBasis ideal 2 ℓ
    {c : C | Odd (orderOf c)} oddOrderElements_primeSectionUnion
  have hmem := coefficientBlock_section_mask_mem localBasis ideal 2 ℓ
    {c : C | Odd (orderOf c)} oddOrderElements_primeSectionUnion
  have hmaskΔ : characterFunctionMask {c : C | Odd (orderOf c)} Δ =
      characterFunctionMask {c : C | Odd (orderOf c)} F := by
    funext c
    simp only [characterFunctionMask]
    split_ifs with hc
    · rw [hΔodd c hc, hFodd c hc]
    · rfl
  have hmask : characterFunctionMask {c : C | Odd (orderOf c)}
      (characterSubsetProjection localBasis β Δ) =
      characterFunctionMask {c : C | Odd (orderOf c)} F := by
    rw [← hcommute Δ, hmaskΔ, characterSubsetProjection_identity localBasis β _ (hmem F hF)]
  have hPodd : ∀ y : C, Odd (orderOf y) →
      characterSubsetProjection localBasis β Δ y = lamG y * (f 0 + f 1 * (1 + ε * ΦG y)) := by
    intro y hy
    have hy' : y ∈ {c : C | Odd (orderOf c)} := hy
    have h := congrFun hmask y
    simp only [characterFunctionMask, ite_eq_left hy'] at h
    rw [h, hFodd y hy]
  have hPN : ∀ c : C, characterSubsetProjection localBasis β Δ c =
      ∑ θ ∈ β, (N θ : ℂ) * (localBasis.representation θ).character c := by
    intro c
    rw [CFSG.RankTwoShapes.characterSubsetProjection_apply']
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [hΔdef, characterPairing_distinct_expansion_coefficient localBasis.representation
      localBasis.irreducible localBasis.distinct (fun θ => (N θ : ℂ)) θ]
  have hlattice : oddRestriction (characterSubsetProjection localBasis β Δ) ∈
      oddRestrictionLattice localBasis β := by
    have heq : oddRestriction (characterSubsetProjection localBasis β Δ) =
        ∑ θ ∈ β, N θ • oddRestriction (localBasis.representation θ).character := by
      funext y
      simp only [oddRestriction, Finset.sum_apply, zsmul_eq_mul]
      exact hPN y.1
    rw [heq]
    exact Submodule.sum_mem _ fun θ hθ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨θ, hθ, rfl⟩)
  rw [← hdata.span] at hlattice
  obtain ⟨z₀, z₁, hz⟩ := Submodule.mem_span_pair.mp hlattice
  have hzodd := (oddRestriction_eq_zsmul_add_iff _ _ _ z₀ z₁).mp hz.symm
  have hcmp := hindep (f 0 - z₀) (f 1 - z₁) fun y hy hyodd => by
    have hyodd' : Odd (orderOf (⟨y, hy⟩ : C)) := by rwa [Subgroup.orderOf_mk]
    have h1 := hPodd ⟨y, hy⟩ hyodd'
    have h2 := hzodd ⟨y, hy⟩ hyodd'
    simp only [Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul] at h2
    have h3 : lamG y * ((f 0 - z₀) + (f 1 - z₁) * (1 + ε * ΦG y)) = 0 := by
      linear_combination h2 - h1
    exact (mul_eq_zero.mp h3).resolve_left (hlam0 y hy)
  obtain rfl | rfl : s = 0 ∨ s = 1 := by fin_cases s <;> simp
  · exact ⟨z₀, sub_eq_zero.mp hcmp.1⟩
  · exact ⟨z₁, sub_eq_zero.mp hcmp.2⟩

end CFSG.Wreathed.FlatCentralFourier
