module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidQEGrp

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Iso

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit [CharP K 2] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] in
theorem polarBilin_single_ox_oy (s t : Fin 2) :
    Q.polarBilin (Pi.single (ox oe s) 1) (Pi.single (oy oe t) 1) = if s = t then 1 else 0 := by
  have h : Pi.single (ox oe s) (1 : K) = oVec oe 0 (uE (.inl s)) := by
    refine oVec_ext oe (fun a => ?_) (fun d => ?_)
    · simp [oVec_apply_inl]
    · simp [oVec_apply_inr, Pi.single_apply]
  rw [h, single_oy_eq, polarBilin_oVec hQ, polarBilin_quadPlus_two]
  fin_cases s <;> fin_cases t <;> simp

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem det_eBlk {g : Matrix ι ι K} (hg : g * oN₀ K oe = oN₀ K oe * g)
    (hgQ : ∀ v, Q (g *ᵥ v) = Q v) : (eBlk oe g).det = 1 := by
  obtain ⟨d00, -, d10, -⟩ := commute_oN₀_diag hg
  have hux : ∀ a s, g (ou oe a) (ox oe s) = 0 := fun a s =>
    commute_oN₀_col hg (fun r => ou_ne_ox oe a r) s
  have hyx : ∀ r s, g (oy oe r) (ox oe s) = 0 := fun r s =>
    commute_oN₀_col hg (fun t => oy_ne_ox oe r t) s
  have hB0 : Q.polarBilin (Pi.single (ox oe 0) 1) (Pi.single (oy oe 0) 1) = 1 := by
    rw [polarBilin_single_ox_oy hQ]
    simp
  have h1 := polarBilin_mulVec_of_isometry Q hgQ (Pi.single (ox oe 0) 1) (Pi.single (oy oe 0) 1)
  rw [polarBilin_col hQ, hB0] at h1
  have hU : (fun a => g (ou oe a) (ox oe 0)) = 0 := funext fun a => hux a 0
  rw [hU, map_zero, LinearMap.zero_apply, zero_add, hyx, hyx, d00, d10] at h1
  rw [det_fin_two]
  simp only [eBlk, zero_mul, add_zero] at h1 ⊢
  rw [CharTwo.sub_eq_add]
  linear_combination h1

omit [CharP K 2] [DecidableEq ι₂] in
theorem isometry_uBlk {g : Matrix ι ι K} (hg : g * oN₀ K oe = oN₀ K oe * g)
    (hgQ : ∀ v, Q (g *ᵥ v) = Q v) (w : ι₂ → K) : Q₂ (uBlk oe g *ᵥ w) = Q₂ w := by
  have hyu : ∀ s b, g (oy oe s) (ou oe b) = 0 := fun s b =>
    commute_oN₀_row hg (fun r => ou_ne_oy oe b r) s
  have h1 := hgQ (oVec oe w 0)
  rw [quad_oVec hQ, hQ] at h1
  have hU : (fun a => (g *ᵥ oVec oe w 0) (oe (.inl a))) = uBlk oe g *ᵥ w := by
    funext a
    simp only [mulVec, dotProduct, uBlk]
    rw [sum_oe oe]
    simp [oVec_apply_inl, oVec_apply_inr]
  have hy : ∀ s, (g *ᵥ oVec oe w 0) (oy oe s) = 0 := fun s => by
    simp only [mulVec, dotProduct]
    rw [sum_oe oe]
    simp [oVec_apply_inl, oVec_apply_inr, hyu]
  rw [hU] at h1
  simp only [StatedQuadPlus, Fin.sum_univ_two] at h1
  rw [show (g *ᵥ oVec oe w 0) (oe (.inr (.inr 0))) = 0 from hy 0,
    show (g *ᵥ oVec oe w 0) (oe (.inr (.inr 1))) = 0 from hy 1] at h1
  simpa using h1

theorem eq_levi_mul_qE {g : GL ι K} (hgC : g ∈ cenM₀ K oe)
    (hgQ : ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v) :
    ∃ (A : SL(2, K)) (u : Fin 2 → ι₂ → K) (c : K),
      (A : Matrix (Fin 2) (Fin 2) K) = eBlk oe (g : Matrix ι ι K) ∧
      g = oKappaGL oe ((uBlkHom K oe).toHomUnits ⟨g, hgC⟩) * oRhoTwoGL oe A *
        qEGL oe Q₂ u c := by
  have hhg := commute_oN₀_of_mem hgC
  set Y : GL ι₂ K := (uBlkHom K oe).toHomUnits ⟨g, hgC⟩ with hYdef
  have hYv : (Y : Matrix ι₂ ι₂ K) = uBlk oe (g : Matrix ι ι K) := rfl
  set A : SL(2, K) := ⟨eBlk oe (g : Matrix ι ι K), det_eBlk hQ hhg hgQ⟩ with hAdef
  have hY : ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w := fun w => by
    rw [hYv]
    exact isometry_uBlk hQ hhg hgQ w
  set l := oKappaGL oe Y * oRhoTwoGL oe A with hl
  have hlC : l ∈ cenM₀ K oe := mul_mem (oKappaGL_mem_cenM₀ Y) (oRhoTwoGL_mem_cenM₀ A)
  have hlv : (l : Matrix ι ι K) = oblk oe (Y : Matrix ι₂ ι₂ K) (rhoTwoMat A) := by
    rw [hl, Units.val_mul, coe_oKappaGL, coe_oRhoTwoGL, oblk_mul, Matrix.mul_one,
      Matrix.one_mul]
  have hhC : l⁻¹ * g ∈ cenM₀ K oe := mul_mem (inv_mem hlC) hgC
  have hlQ := isometry_levi hQ hY A
  have hhQ := isometry_mul (isometry_inv' hlQ) hgQ
  have hsub : (⟨l⁻¹ * g, hhC⟩ : cenM₀ K oe) = (⟨l, hlC⟩ : cenM₀ K oe)⁻¹ * ⟨g, hgC⟩ := rfl
  have he : eBlk oe ((l⁻¹ * g : GL ι K) : Matrix ι ι K) = 1 := by
    have hle : (eBlkHom K oe).toHomUnits ⟨l, hlC⟩ = (eBlkHom K oe).toHomUnits ⟨g, hgC⟩ := by
      apply Units.ext
      change eBlk oe (l : Matrix ι ι K) = eBlk oe (g : Matrix ι ι K)
      rw [hlv, eBlk_oblk]
      funext s t
      rw [rhoTwoMat_apply, fromBlocks_apply₁₁]
    have h2 := congrArg (fun x : cenM₀ K oe => (eBlkHom K oe).toHomUnits x) hsub
    simp only [map_mul, map_inv, hle, inv_mul_cancel] at h2
    exact congrArg Units.val h2
  have hu : uBlk oe ((l⁻¹ * g : GL ι K) : Matrix ι ι K) = 1 := by
    have hlu : (uBlkHom K oe).toHomUnits ⟨l, hlC⟩ = (uBlkHom K oe).toHomUnits ⟨g, hgC⟩ := by
      apply Units.ext
      change uBlk oe (l : Matrix ι ι K) = uBlk oe (g : Matrix ι ι K)
      rw [hlv, uBlk_oblk, hYv]
    have h2 := congrArg (fun x : cenM₀ K oe => (uBlkHom K oe).toHomUnits x) hsub
    simp only [map_mul, map_inv, hlu, inv_mul_cancel] at h2
    exact congrArg Units.val h2
  have h1 := eq_qE_of hQ (commute_oN₀_of_mem hhC) hhQ he hu
  refine ⟨A, fun t a => ((l⁻¹ * g : GL ι K) : Matrix ι ι K) (ou oe a) (oy oe t),
    ((l⁻¹ * g : GL ι K) : Matrix ι ι K) (ox oe 1) (oy oe 0), rfl, ?_⟩
  have hgl : g = l * (l⁻¹ * g) := by rw [mul_inv_cancel_left]
  conv_lhs => rw [hgl]
  congr 1
  exact Units.ext h1

end Iso

end CFSG.ComponentClassification.RankTwoClassical.ORigid
