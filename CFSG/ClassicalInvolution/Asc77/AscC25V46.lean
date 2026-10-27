module

public import CFSG.ClassicalInvolution.Asc77.AscC25V40

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.GorensteinWalter
open scoped MatrixGroups

section Absorb

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem inl_inv_mul_eq (α : PGammaL2 (GaloisField p f)) (γ : PGL2 (GaloisField p f)) :
    (SemidirectProduct.inl (α.left * (pgl2FieldAut (GaloisField p f) α.right γ) * γ⁻¹) :
        PGammaL2 (GaloisField p f))⁻¹ * α =
      SemidirectProduct.inl γ * SemidirectProduct.inr α.right * (SemidirectProduct.inl γ)⁻¹ := by
  apply SemidirectProduct.ext
  · simp [mul_assoc]
  · simp

variable (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
  (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))

include hp hq in
theorem exists_mem_K_nuG_eq_conj_inr (γ : PGL2 (GaloisField p f)) {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) (hδ : diagChar hp hq e ⟨n, hn⟩ = 1) :
    ∃ k ∈ K, nuG hp hq e (k⁻¹ * n) =
      SemidirectProduct.inl γ * SemidirectProduct.inr (fieldChar hp hq e ⟨n, hn⟩) *
        (SemidirectProduct.inl γ)⁻¹ := by
  classical
  let α : PGammaL2 (GaloisField p f) := nuK hp hq e ⟨n, hn⟩
  have hαδ : diagPGL α.left = 1 := by
    rw [← diagGamma_apply]
    exact hδ
  have hy1 : diagPGL (α.left * (pgl2FieldAut (GaloisField p f) α.right γ) * γ⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hαδ, pgl2FieldAut_apply, diagPGL_field, one_mul,
      mul_inv_cancel]
  obtain ⟨y, hy⟩ := exists_toPGL_of_diagPGL_eq_one _ hy1
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_surjective (e.symm s)
  have hs : e (QuotientGroup.mk κ) = s := by rw [hκ, MulEquiv.apply_symm_apply]
  refine ⟨(κ : G), κ.2, ?_⟩
  have hκN : (κ : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer κ.2
  have hk := Hall196.normalizerToPGammaL2Mod_of_mem e (gf_facts hp hq).2.1
    (gf_facts hp hq).2.2.1 (gf_facts hp hq).2.2.2 κ.2
  rw [hs] at hk
  rw [nuG_of_mem hp hq e (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκN) hn)]
  have e1 : (⟨(κ : G)⁻¹ * n, Subgroup.mul_mem _ (Subgroup.inv_mem _ hκN) hn⟩ :
      Subgroup.normalizer (K : Set G)) = ⟨(κ : G), hκN⟩⁻¹ * ⟨n, hn⟩ := rfl
  rw [e1, map_mul, map_inv]
  have hk' : nuK hp hq e ⟨(κ : G), hκN⟩ = SemidirectProduct.inl
      (α.left * (pgl2FieldAut (GaloisField p f) α.right γ) * γ⁻¹) := by
    rw [hy]
    exact hk
  rw [hk']
  exact inl_inv_mul_eq α γ

end Absorb

end CFSG.ClassicalInvolution.Asc77.C25V
