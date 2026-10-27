module

public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherProjective

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem exists_gsp_apply_eq_of_isotropic_pair [FiniteDimensional K N] (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) {x y x' y' : N} (hxy : LinearIndependent K ![x, y])
    (hxy' : LinearIndependent K ![x', y']) (h : BN x y = 0) (h' : BN x' y' = 0) :
    ∃ g : Gsp BN, g.app x = x' ∧ g.app y = y' := by
  obtain ⟨m, b, hb, hb1, hb2, hdim⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.alternating_isotropic_pair_extension
      hBN hBNnd hxy h
  obtain ⟨m', b', hb', hb1', hb2', hdim'⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.alternating_isotropic_pair_extension
      hBN hBNnd hxy' h'
  obtain rfl : m = m' := by omega
  have hgram : ∀ i j, BN (b i) (b j) = BN (b' i) (b' j) := fun i j => by
    have hb0 : BilinForm.toMatrix b BN = Matrix.fromBlocks 0 1 (-1) 0 := hb
    have hb0' : BilinForm.toMatrix b' BN = Matrix.fromBlocks 0 1 (-1) 0 := hb'
    have h1 := congrFun (congrFun hb0 i) j
    have h2 := congrFun (congrFun hb0' i) j
    rw [BilinForm.toMatrix_apply] at h1 h2
    exact h1.trans h2.symm
  obtain ⟨e, he⟩ : ∃ e : N ≃ₗ[K] N, ∀ i, e (b i) = b' i :=
    ⟨b.equiv b' (Equiv.refl _), fun i => by simp only [Basis.equiv_apply, Equiv.refl_apply]⟩
  have hext : BN.compl₁₂ (e : N →ₗ[K] N) (e : N →ₗ[K] N) = BN :=
    BilinForm.ext_basis b fun i j => by
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, he]
      exact (hgram i j).symm
  have hiso : ∀ u v, BN (e u) (e v) = BN u v := fun u v => by
    have h0 := LinearMap.congr_fun₂ hext u v
    simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe] using h0
  refine ⟨⟨LinearMap.GeneralLinearGroup.ofLinearEquiv e,
    CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.mpr hiso⟩, ?_, ?_⟩
  · show e x = x'
    rw [← hb1, he, hb1']
  · show e y = y'
    rw [← hb2, he, hb2']

theorem exists_gsp_apply_eq_of_form_eq [FiniteDimensional K N] (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) {x y x' y' : N} {κ : K} (hκ : κ ≠ 0) (h : BN x y = κ)
    (h' : BN x' y' = κ) : ∃ g : Gsp BN, g.app x = x' ∧ g.app y = y' := by
  have h1 : BN x (κ⁻¹ • y) = 1 := by
    rw [map_smul, smul_eq_mul, h, inv_mul_cancel₀ hκ]
  have h1' : BN x' (κ⁻¹ • y') = 1 := by
    rw [map_smul, smul_eq_mul, h', inv_mul_cancel₀ hκ]
  obtain ⟨g, hg1, hg2⟩ := exists_gsp_pair hBN hBNnd h1 h1'
  refine ⟨g, hg1, ?_⟩
  have hy : g.app y = κ • g.app (κ⁻¹ • y) := by
    rw [← Gsp.map_smul, smul_inv_smul₀ hκ]
  rw [hy, hg2, smul_inv_smul₀ hκ]

end CFSG.ClassicalGroups.Alternating
