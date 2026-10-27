module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidEich

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Blocks

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem qE_apply (u : Fin 2 → ι₂ → K) (c : K) (i j : ι) :
    qE oe Q₂ u c i j = (qE oe Q₂ u c *ᵥ Pi.single j 1) i := by
  rw [mulVec_single_one, col_apply]

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem eBlk_qE (u : Fin 2 → ι₂ → K) (c : K) : eBlk oe (qE oe Q₂ u c) = 1 := by
  ext s t
  rw [eBlk, qE_apply, qE_mulVec_single_ox, Matrix.one_apply]
  simp [Pi.single_apply]

omit [Fintype ι₂] in
theorem uBlk_qE (u : Fin 2 → ι₂ → K) (c : K) : uBlk oe (qE oe Q₂ u c) = 1 := by
  ext a b
  rw [uBlk, qE_apply, qE_mulVec_ou, Matrix.one_apply]
  simp [Pi.single_apply]

variable [CharP K 2]

theorem qEGL_mem_cenM₀ (u : Fin 2 → ι₂ → K) (c : K) : qEGL oe Q₂ u c ∈ cenM₀ K oe := by
  rw [mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_qEGL, oRhoOneGL_slTr_one, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, qE_commute]

end Blocks

section Vectors

variable {K : Type} [Field K] {ι₂ ι : Type} [DecidableEq ι₂] [DecidableEq ι]
  {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}

theorem single_ou_eq (b : ι₂) : Pi.single (ou oe b) (1 : K) = oVec oe (Pi.single b 1) 0 := by
  refine oVec_ext oe (fun a => ?_) (fun d => ?_)
  · simp [oVec_apply_inl, Pi.single_apply]
  · simp [oVec_apply_inr]

omit [DecidableEq ι₂] in
theorem single_oy_eq (s : Fin 2) : Pi.single (oy oe s) (1 : K) = oVec oe 0 (uE (.inr s)) := by
  refine oVec_ext oe (fun a => ?_) (fun d => ?_)
  · simp [oVec_apply_inl]
  · simp [oVec_apply_inr, Pi.single_apply]

omit [DecidableEq ι₂] in
theorem vU_single_oy (s : Fin 2) : vU oe (Pi.single (oy oe s) (1 : K)) = 0 := by
  funext a
  simp [vU]

theorem vU_single_ou (b : ι₂) : vU oe (Pi.single (ou oe b) (1 : K)) = Pi.single b 1 := by
  funext a
  simp [vU, Pi.single_apply]

end Vectors

section Param

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit [CharP K 2] [Fintype ι₂] [Fintype ι] in
theorem polarBilin_single_ou_oy (b : ι₂) (s : Fin 2) :
    Q.polarBilin (Pi.single (ou oe b) 1) (Pi.single (oy oe s) 1) = 0 := by
  rw [single_ou_eq, single_oy_eq, polarBilin_oVec hQ, polarBilin_quadPlus_two]
  simp

omit [CharP K 2] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] in
theorem polarBilin_single_oy_oy (s t : Fin 2) :
    Q.polarBilin (Pi.single (oy oe s) 1) (Pi.single (oy oe t) 1) = 0 := by
  rw [single_oy_eq, single_oy_eq, polarBilin_oVec hQ, polarBilin_quadPlus_two]
  simp

omit [CharP K 2] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] in
theorem quad_single_oy (s : Fin 2) : Q (Pi.single (oy oe s) 1) = 0 := by
  rw [single_oy_eq, quad_oVec hQ]
  simp [StatedQuadPlus]

omit [Fintype ι₂] in
theorem eq_qE_of {g : Matrix ι ι K} (hg : g * oN₀ K oe = oN₀ K oe * g)
    (hgQ : ∀ v, Q (g *ᵥ v) = Q v) (he : eBlk oe g = 1) (hu : uBlk oe g = 1) :
    g = qE oe Q₂ (fun t a => g (ou oe a) (oy oe t)) (g (ox oe 1) (oy oe 0)) := by
  obtain ⟨d00, d11, d10, d01⟩ := commute_oN₀_diag hg
  have hxx : ∀ s t, g (ox oe s) (ox oe t) = if s = t then 1 else 0 := fun s t => by
    have := congrFun (congrFun he s) t
    simpa [eBlk, Matrix.one_apply] using this
  have huu : ∀ a b, g (ou oe a) (ou oe b) = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun hu a) b
    simpa [uBlk, Matrix.one_apply] using this
  have hyy : ∀ s t, g (oy oe s) (oy oe t) = if s = t then 1 else 0 := by
    intro s t
    fin_cases s <;> fin_cases t <;> simp [d00, d11, d10, d01, hxx]
  have hyu : ∀ s b, g (oy oe s) (ou oe b) = 0 := fun s b =>
    commute_oN₀_row hg (fun r => ou_ne_oy oe b r) s
  have hux : ∀ a s, g (ou oe a) (ox oe s) = 0 := fun a s =>
    commute_oN₀_col hg (fun r => ou_ne_ox oe a r) s
  have hyx : ∀ r s, g (oy oe r) (ox oe s) = 0 := fun r s =>
    commute_oN₀_col hg (fun t => oy_ne_ox oe r t) s
  have hB := polarBilin_mulVec_of_isometry Q hgQ
  have hcolU : ∀ b, (fun a => g (ou oe a) (ou oe b)) = Pi.single b 1 := fun b => by
    funext a
    rw [huu]
    simp [Pi.single_apply]
  ext i j
  rw [qE_apply]
  obtain ⟨d, rfl⟩ := oe.surjective j
  obtain ⟨d', rfl⟩ := oe.surjective i
  rcases d with b | t | t
  ·
    rcases d' with a | s | s
    · rw [qE_mulVec_ou]
      simp [Pi.single_apply, huu]
    · rw [qE_mulVec_ox, qAlpha, vU_single_ou]
      have h1 := hB (Pi.single (ou oe b) 1) (Pi.single (oy oe s) 1)
      rw [polarBilin_col hQ, polarBilin_single_ou_oy hQ, hcolU] at h1
      fin_cases s <;> simp [hyu, hyy] at h1 ⊢ <;>
        rw [CharTwo.add_eq_zero] at h1 <;> exact h1.symm
    · rw [qE_mulVec_oy]
      simp [hyu]
  ·
    rw [qE_mulVec_single_ox]
    rcases d' with a | s | s
    · simp [hux]
    · simp [Pi.single_apply, hxx]
    · simp [hyx]
  ·
    rcases d' with a | s | s
    · rw [qE_mulVec_ou]
      simp [Pi.single_apply]
    · rw [qE_mulVec_ox, qAlpha, vU_single_oy]
      fin_cases s <;> fin_cases t
      · have h1 := hgQ (Pi.single (oy oe 0) 1)
        rw [quad_col hQ, quad_single_oy hQ] at h1
        simp [hyy] at h1 ⊢
        rw [CharTwo.add_eq_zero] at h1
        exact h1.symm
      · have h1 := hB (Pi.single (oy oe 0) 1) (Pi.single (oy oe 1) 1)
        rw [polarBilin_col hQ, polarBilin_single_oy_oy hQ] at h1
        simp [hyy] at h1 ⊢
        have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
        linear_combination h1 - (g (ox oe 1) (oy oe 0) +
          polar (⇑Q₂) (fun a => g (ou oe a) (oy oe 0)) fun a => g (ou oe a) (oy oe 1)) * h2
      · simp
      · have h1 := hgQ (Pi.single (oy oe 1) 1)
        rw [quad_col hQ, quad_single_oy hQ] at h1
        simp [hyy] at h1 ⊢
        rw [CharTwo.add_eq_zero] at h1
        exact h1.symm
    · rw [qE_mulVec_oy]
      simp [Pi.single_apply, hyy]

end Param

end CFSG.ComponentClassification.RankTwoClassical.ORigid
