module

public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsIntegrality
public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsSupport
public import CFSG.CharacterTheory.Wreathed.FourPointOrderFourBases
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.Wreathed.FourPointCentralFourier

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.FourPointGaussianColumns CFSG.Wreathed.FourPointOrderFour

open scoped BigOperators Classical

theorem fourierTransform_integral_of_oddRestrictionBasis {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {a : G} {m : ℕ}
    (hm : orderOf a = m) (C : Subgroup G) (hC : C = Subgroup.centralizer {a})
    (localBasis : FiniteIrreducibleCharacterBasis C) (localPrincipal : localBasis.index)
    (b : Fin 2 → OddElements C → ℂ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hb : OddRestrictionComplexBasis localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal) b M)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (χ : basis.index) (v : ℕ → Fin 2 → ℂ)
    (hv : ∀ k ∈ Finset.Ico 1 m, ∀ y : OddElements C,
      (basis.representation χ).character (a ^ k * y) = v k 0 * b 0 y + v k 1 * b 1 y)
    (j : ℕ) (ℓ : Fin 2) : ∃ z : ℤ, fourierTransform m ζ (fun k => v k ℓ) j = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : 0 < m := by
    rw [← hm]
    exact orderOf_pos a
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
  have hΔodd : ∀ y : OddElements C, Δ y = f 0 * b 0 y + f 1 * b 1 y := by
    intro y
    have hsplit : ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) *
        (basis.representation χ).character (a ^ k * y) =
        (∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) * v k 0) * b 0 y +
          (∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) * v k 1) * b 1 y := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hv k hk y]
      ring
    have hΔy : Δ y = (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m, (ζ ^ (j * k) - 1) *
        (basis.representation χ).character (a ^ k * y) := (hN y).symm
    rw [hΔy, Finset.sum_range_eq_add_Ico _ hm0]
    simp only [mul_zero, pow_zero, sub_self, zero_mul, zero_add]
    rw [hsplit, hfdef]
    simp only [fourierTransform]
    ring
  set B₀ := coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal
    with hB₀
  have hrep : ∀ k, ∃ F ∈ coefficientCharacterSpace localBasis B₀,
      ∀ y : OddElements C, F y = b k y := by
    intro k
    have hmemk : b k ∈ (Submodule.span ℂ ((fun θ => (localBasis.representation θ).character) ''
        (B₀ : Set localBasis.index))).map (LinearMap.funLeft ℂ ℂ Subtype.val) := by
      rw [← hb.span_eq]
      exact Submodule.subset_span ⟨k, rfl⟩
    obtain ⟨F, hF, hFb⟩ := Submodule.mem_map.mp hmemk
    exact ⟨F, hF, fun y => congrFun hFb y⟩
  choose F hFspan hFb using hrep
  set Ftot : C → ℂ := f 0 • F 0 + f 1 • F 1 with hFtotdef
  have hFtot : Ftot ∈ coefficientCharacterSpace localBasis B₀ :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hFspan 0)) (Submodule.smul_mem _ _ (hFspan 1))
  have hcommute := coefficientBlock_section_mask_commute localBasis ideal 2 localPrincipal
    {c : C | Odd (orderOf c)} oddOrderElements_primeSectionUnion
  have hmem := coefficientBlock_section_mask_mem localBasis ideal 2 localPrincipal
    {c : C | Odd (orderOf c)} oddOrderElements_primeSectionUnion
  have hmaskΔ : characterFunctionMask {c : C | Odd (orderOf c)} Δ =
      characterFunctionMask {c : C | Odd (orderOf c)} Ftot := by
    funext c
    simp only [characterFunctionMask]
    split_ifs with hc
    · rw [show Δ c = Δ ((⟨c, hc⟩ : OddElements C) : C) from rfl, hΔodd ⟨c, hc⟩, hFtotdef]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [show F 0 c = F 0 ((⟨c, hc⟩ : OddElements C) : C) from rfl,
        show F 1 c = F 1 ((⟨c, hc⟩ : OddElements C) : C) from rfl, hFb 0, hFb 1]
    · rfl
  have hmask : characterFunctionMask {c : C | Odd (orderOf c)}
      (characterSubsetProjection localBasis B₀ Δ) =
      characterFunctionMask {c : C | Odd (orderOf c)} Ftot := by
    rw [← hcommute Δ, hmaskΔ, characterSubsetProjection_identity localBasis B₀ _ (hmem Ftot hFtot)]
  have hPodd : ∀ y : OddElements C,
      characterSubsetProjection localBasis B₀ Δ y = f 0 * b 0 y + f 1 * b 1 y := by
    intro y
    have hy' : (y : C) ∈ {c : C | Odd (orderOf c)} := y.2
    have h := congrFun hmask y
    simp only [characterFunctionMask, ite_eq_left hy'] at h
    rw [h, hFtotdef]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hFb 0, hFb 1]
  have hPN : ∀ c : C, characterSubsetProjection localBasis B₀ Δ c =
      ∑ θ ∈ B₀, (N θ : ℂ) * (localBasis.representation θ).character c := by
    intro c
    rw [CFSG.RankTwoShapes.characterSubsetProjection_apply']
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [hΔdef, characterPairing_distinct_expansion_coefficient localBasis.representation
      localBasis.irreducible localBasis.distinct (fun θ => (N θ : ℂ)) θ]
  obtain ⟨D, hDrow, -⟩ := hb.rows
  set z : Fin 2 → ℤ := fun ℓ => ∑ θ : B₀, N θ * D θ ℓ with hzdef
  have hcomb : ∀ y : OddElements C,
      characterSubsetProjection localBasis B₀ Δ y = (z 0 : ℂ) * b 0 y + (z 1 : ℂ) * b 1 y := by
    intro y
    rw [hPN, ← Finset.sum_coe_sort B₀]
    have hθ : ∀ θ : B₀, (localBasis.representation θ).character y =
        ∑ ℓ, (D θ ℓ : ℂ) * b ℓ y :=
      fun θ => (hDrow θ fun ℓ => (D θ ℓ : ℂ)).mpr (fun ℓ => rfl) y
    simp only [hθ, Fin.sum_univ_two, hzdef]
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    ring
  have hzero := Fintype.linearIndependent_iff.mp hb.linearIndependent
    (fun ℓ => f ℓ - z ℓ) (funext fun y => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Pi.zero_apply]
      have h1 := hPodd y
      have h2 := hcomb y
      linear_combination h2 - h1)
  exact ⟨z ℓ, sub_eq_zero.mp (hzero ℓ)⟩

theorem row_gram {ι : Type*} (B : Finset ι) (P Q P' Q' : ι → ℂ) (c₀₀ c₀₁ c₁₀ c₁₁ : ℂ)
    (h₀₀ : ∑ χ ∈ B, starRingEnd ℂ (P χ) * P' χ = c₀₀)
    (h₀₁ : ∑ χ ∈ B, starRingEnd ℂ (P χ) * Q' χ = c₀₁)
    (h₁₀ : ∑ χ ∈ B, starRingEnd ℂ (Q χ) * P' χ = c₁₀)
    (h₁₁ : ∑ χ ∈ B, starRingEnd ℂ (Q χ) * Q' χ = c₁₁) :
    ∑ χ ∈ B, starRingEnd ℂ ((P χ + 2 * Q χ) / 3) * ((P' χ + 2 * Q' χ) / 3) =
      (c₀₀ + 2 * c₀₁ + 2 * c₁₀ + 4 * c₁₁) / 9 ∧
    ∑ χ ∈ B, starRingEnd ℂ ((P χ + 2 * Q χ) / 3) * ((P' χ - Q' χ) / 3) =
      (c₀₀ - c₀₁ + 2 * c₁₀ - 2 * c₁₁) / 9 ∧
    ∑ χ ∈ B, starRingEnd ℂ ((P χ - Q χ) / 3) * ((P' χ + 2 * Q' χ) / 3) =
      (c₀₀ + 2 * c₀₁ - c₁₀ - 2 * c₁₁) / 9 ∧
    ∑ χ ∈ B, starRingEnd ℂ ((P χ - Q χ) / 3) * ((P' χ - Q' χ) / 3) =
      (c₀₀ - c₀₁ - c₁₀ + c₁₁) / 9 := by
  have hexp : ∀ (α β γ δ : ℂ), ∑ χ ∈ B, (α * (starRingEnd ℂ (P χ) * P' χ) +
      β * (starRingEnd ℂ (P χ) * Q' χ) + γ * (starRingEnd ℂ (Q χ) * P' χ) +
      δ * (starRingEnd ℂ (Q χ) * Q' χ)) = α * c₀₀ + β * c₀₁ + γ * c₁₀ + δ * c₁₁ := by
    intro α β γ δ
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h₀₀, h₀₁, h₁₀, h₁₁]
  have hconj3 : starRingEnd ℂ (3 : ℂ) = 3 := map_ofNat _ 3
  have hconj2 : starRingEnd ℂ (2 : ℂ) = 2 := map_ofNat _ 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← show (1 / 9 : ℂ) * c₀₀ + (2 / 9) * c₀₁ + (2 / 9) * c₁₀ + (4 / 9) * c₁₁ =
        (c₀₀ + 2 * c₀₁ + 2 * c₁₀ + 4 * c₁₁) / 9 by ring, ← hexp]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_div₀, map_add, map_mul, hconj2, hconj3]
    ring
  · rw [← show (1 / 9 : ℂ) * c₀₀ + (-1 / 9) * c₀₁ + (2 / 9) * c₁₀ + (-2 / 9) * c₁₁ =
        (c₀₀ - c₀₁ + 2 * c₁₀ - 2 * c₁₁) / 9 by ring, ← hexp]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_div₀, map_add, map_mul, hconj2, hconj3]
    ring
  · rw [← show (1 / 9 : ℂ) * c₀₀ + (2 / 9) * c₀₁ + (-1 / 9) * c₁₀ + (-2 / 9) * c₁₁ =
        (c₀₀ + 2 * c₀₁ - c₁₀ - 2 * c₁₁) / 9 by ring, ← hexp]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_div₀, map_sub, hconj3]
    ring
  · rw [← show (1 / 9 : ℂ) * c₀₀ + (-1 / 9) * c₀₁ + (-1 / 9) * c₁₀ + (1 / 9) * c₁₁ =
        (c₀₀ - c₀₁ - c₁₀ + c₁₁) / 9 by ring, ← hexp]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_div₀, map_sub, hconj3]
    ring

@[expose] def evalRow (P Q : ℂ) : Fin 2 → ℂ := ![(P + 2 * Q) / 3, (P - Q) / 3]

theorem evalRow_gram {ι : Type*} (B : Finset ι) (P Q P' Q' : ι → ℂ) (c₀₀ c₀₁ c₁₀ c₁₁ : ℂ)
    (h₀₀ : ∑ χ ∈ B, starRingEnd ℂ (P χ) * P' χ = c₀₀)
    (h₀₁ : ∑ χ ∈ B, starRingEnd ℂ (P χ) * Q' χ = c₀₁)
    (h₁₀ : ∑ χ ∈ B, starRingEnd ℂ (Q χ) * P' χ = c₁₀)
    (h₁₁ : ∑ χ ∈ B, starRingEnd ℂ (Q χ) * Q' χ = c₁₁) (ℓ t : Fin 2) :
    ∑ χ ∈ B, starRingEnd ℂ (evalRow (P χ) (Q χ) ℓ) * evalRow (P' χ) (Q' χ) t =
      ![![(c₀₀ + 2 * c₀₁ + 2 * c₁₀ + 4 * c₁₁) / 9, (c₀₀ - c₀₁ + 2 * c₁₀ - 2 * c₁₁) / 9],
        ![(c₀₀ + 2 * c₀₁ - c₁₀ - 2 * c₁₁) / 9, (c₀₀ - c₀₁ - c₁₀ + c₁₁) / 9]] ℓ t := by
  obtain ⟨g₀₀, g₀₁, g₁₀, g₁₁⟩ := row_gram B P Q P' Q' c₀₀ c₀₁ c₁₀ c₁₁ h₀₀ h₀₁ h₁₀ h₁₁
  fin_cases ℓ <;> fin_cases t
  · exact g₀₀
  · exact g₀₁
  · exact g₁₀
  · exact g₁₁

end CFSG.Wreathed.FourPointCentralFourier
