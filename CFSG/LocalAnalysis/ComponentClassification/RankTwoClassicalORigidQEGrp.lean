module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidLevi

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Grp

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι] [DecidableEq ι]
  (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))

@[expose] noncomputable def oQE : Subgroup (GL ι K) where
  carrier := Set.range fun p : (Fin 2 → ι₂ → K) × K => qEGL oe Q₂ p.1 p.2
  mul_mem' := by
    rintro _ _ ⟨⟨u, c⟩, rfl⟩ ⟨⟨u', c'⟩, rfl⟩
    exact ⟨⟨u + u', c + c' + Q₂.polarBilin (u' 0) (u 1)⟩,
      Units.ext (qE_mul oe Q₂ u u' c c').symm⟩
  one_mem' := ⟨⟨0, 0⟩, Units.ext (qE_zero oe Q₂)⟩
  inv_mem' := by
    rintro _ ⟨⟨u, c⟩, rfl⟩
    exact ⟨⟨u, c + Q₂.polarBilin (u 0) (u 1)⟩, Units.ext rfl⟩

theorem mem_oQE {g : GL ι K} : g ∈ oQE oe Q₂ ↔ ∃ u c, qEGL oe Q₂ u c = g :=
  ⟨fun ⟨⟨u, c⟩, h⟩ => ⟨u, c, h⟩, fun ⟨u, c, h⟩ => ⟨⟨u, c⟩, h⟩⟩

theorem qEGL_mem_oQE (u : Fin 2 → ι₂ → K) (c : K) : qEGL oe Q₂ u c ∈ oQE oe Q₂ :=
  ⟨⟨u, c⟩, rfl⟩

variable [Fintype ι₂] [DecidableEq ι₂]

theorem oQE_le_cenM₀ : oQE oe Q₂ ≤ cenM₀ K oe := by
  rintro _ ⟨⟨u, c⟩, rfl⟩
  exact qEGL_mem_cenM₀ oe Q₂ u c

end Grp

section Levi

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}

theorem oKappaGL_mem_cenM₀ (Y : GL ι₂ K) : oKappaGL oe Y ∈ cenM₀ K oe := by
  rw [mem_centralizer_singleton_iff]
  simp only [oKappaGL, oRhoOneGL, MonoidHom.comp_apply, ← map_mul]
  congr 1
  ext <;> simp

theorem oRhoTwoGL_mem_cenM₀ [CharP K 2] (A : SL(2, K)) : oRhoTwoGL oe A ∈ cenM₀ K oe := by
  rw [mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_oRhoTwoGL, coe_oRhoOneGL, oblk_mul, oblk_mul,
    rhoOne_mul_rhoTwo]

end Levi

section Conj

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit [CharP K 2] in
theorem isometry_levi {Y : GL ι₂ K} (hY : ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w)
    (A : SL(2, K)) (v : ι → K) :
    Q (((oKappaGL oe Y * oRhoTwoGL oe A : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := by
  rw [Units.val_mul, coe_oKappaGL, coe_oRhoTwoGL, oblk_mul, Matrix.mul_one, Matrix.one_mul]
  exact quad_oblk_mulVec_eq hQ hY (quadPlus_two_rhoTwo A) v

omit hQ [CharP K 2] [Fintype ι₂] [DecidableEq ι₂] in
theorem isometry_mul {g h : GL ι K} (hg : ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v)
    (hh : ∀ v, Q ((h : Matrix ι ι K) *ᵥ v) = Q v) (v : ι → K) :
    Q (((g * h : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := by
  rw [Units.val_mul, ← mulVec_mulVec, hg, hh]

omit hQ [CharP K 2] [Fintype ι₂] [DecidableEq ι₂] in
theorem isometry_inv' {g : GL ι K} (hg : ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v) (v : ι → K) :
    Q (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := by
  have h1 := hg (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h1
  exact h1.symm

theorem conj_qE_levi {Y : GL ι₂ K} (hY : ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w)
    (A : SL(2, K)) (u : Fin 2 → ι₂ → K) (c : K) :
    ∃ c' : K, oKappaGL oe Y * oRhoTwoGL oe A * qEGL oe Q₂ u c *
        (oKappaGL oe Y * oRhoTwoGL oe A)⁻¹ =
      qEGL oe Q₂ (fun t => (Y : Matrix ι₂ ι₂ K) *ᵥ ∑ r, (A : Matrix (Fin 2) (Fin 2) K) t r • u r)
        c' := by
  set l := oKappaGL oe Y * oRhoTwoGL oe A with hl
  have hlC : l ∈ cenM₀ K oe := mul_mem (oKappaGL_mem_cenM₀ Y) (oRhoTwoGL_mem_cenM₀ A)
  have hqC := qEGL_mem_cenM₀ oe Q₂ u c
  set g := l * qEGL oe Q₂ u c * l⁻¹ with hg
  have hgC : g ∈ cenM₀ K oe := mul_mem (mul_mem hlC hqC) (inv_mem hlC)
  have hlQ := isometry_levi hQ hY A
  have hqQ : ∀ v, Q (((qEGL oe Q₂ u c : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v :=
    qE_isometry hQ u c
  have hgQ : ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v :=
    isometry_mul (isometry_mul hlQ hqQ) (isometry_inv' hlQ)
  have hsub : (⟨g, hgC⟩ : cenM₀ K oe) =
      ⟨l, hlC⟩ * ⟨qEGL oe Q₂ u c, hqC⟩ * (⟨l, hlC⟩ : cenM₀ K oe)⁻¹ := rfl
  have he : eBlk oe (g : Matrix ι ι K) = 1 := by
    have h1 : (eBlkHom K oe).toHomUnits ⟨qEGL oe Q₂ u c, hqC⟩ = 1 :=
      Units.ext (eBlk_qE oe Q₂ u c)
    have h2 := congrArg (fun x : cenM₀ K oe => (eBlkHom K oe).toHomUnits x) hsub
    simp only [map_mul, map_inv, h1, mul_one, mul_inv_cancel] at h2
    exact congrArg Units.val h2
  have hu : uBlk oe (g : Matrix ι ι K) = 1 := by
    have h1 : (uBlkHom K oe).toHomUnits ⟨qEGL oe Q₂ u c, hqC⟩ = 1 :=
      Units.ext (uBlk_qE oe Q₂ u c)
    have h2 := congrArg (fun x : cenM₀ K oe => (uBlkHom K oe).toHomUnits x) hsub
    simp only [map_mul, map_inv, h1, mul_one, mul_inv_cancel] at h2
    exact congrArg Units.val h2
  have h1 := eq_qE_of hQ (commute_oN₀_of_mem hgC) hgQ he hu
  refine ⟨(g : Matrix ι ι K) (ox oe 1) (oy oe 0), Units.ext (h1.trans ?_)⟩
  rw [coe_qEGL]
  congr 1
  funext t
  change avec₂ oe (g : Matrix ι ι K) t = _
  have hgv : (g : Matrix ι ι K) = oblk oe (Y : Matrix ι₂ ι₂ K) (rhoTwoMat A) *
      qE oe Q₂ u c * oblk oe ((Y⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K) (rhoTwoMat A⁻¹) := by
    rw [hg, hl, _root_.mul_inv_rev, ← map_inv, ← map_inv]
    simp only [Units.val_mul, coe_oKappaGL, coe_oRhoTwoGL, coe_qEGL]
    rw [oblk_mul, oblk_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  have hqx : ∀ a r, qE oe Q₂ u c (ou oe a) (ox oe r) = 0 := fun a r => by
    rw [qE_apply, qE_mulVec_single_ox]
    simp
  rw [hgv, avec₂_oblk_mul_mul _ _ _ _ hqx t, avec₂_qE]
  simp [rhoTwoMat_inv_inr_inr]

end Conj

end CFSG.ComponentClassification.RankTwoClassical.ORigid
