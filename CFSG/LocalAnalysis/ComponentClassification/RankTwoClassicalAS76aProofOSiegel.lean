module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCommute
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitCTwo

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Vectors

variable {K : Type} {ι₂ ι : Type} {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}

theorem oVec_apply_inl (w : ι₂ → K) (u : Fin 2 ⊕ Fin 2 → K) (a : ι₂) :
    oVec oe w u (oe (.inl a)) = w a := by
  simp [oVec]

theorem oVec_apply_inr (w : ι₂ → K) (u : Fin 2 ⊕ Fin 2 → K) (b : Fin 2 ⊕ Fin 2) :
    oVec oe w u (oe (.inr b)) = u b := by
  simp [oVec]

variable (oe) in
theorem oVec_ext {v v' : ι → K} (h₂ : ∀ a, v (oe (.inl a)) = v' (oe (.inl a)))
    (h₁ : ∀ b, v (oe (.inr b)) = v' (oe (.inr b))) : v = v' := by
  funext i
  obtain ⟨c, rfl⟩ := oe.surjective i
  rcases c with a | b
  exacts [h₂ a, h₁ b]

variable [Field K]

theorem oVec_add (w w' : ι₂ → K) (u u' : Fin 2 ⊕ Fin 2 → K) :
    oVec oe w u + oVec oe w' u' = oVec oe (w + w') (u + u') :=
  oVec_ext oe (fun a => by simp only [Pi.add_apply, oVec_apply_inl])
    (fun b => by simp only [Pi.add_apply, oVec_apply_inr])

theorem smul_oVec (c : K) (w : ι₂ → K) (u : Fin 2 ⊕ Fin 2 → K) :
    c • oVec oe w u = oVec oe (c • w) (c • u) :=
  oVec_ext oe (fun a => by simp only [Pi.smul_apply, oVec_apply_inl])
    (fun b => by simp only [Pi.smul_apply, oVec_apply_inr])

theorem oVec_zero : oVec oe (0 : ι₂ → K) (0 : Fin 2 ⊕ Fin 2 → K) = 0 :=
  oVec_ext oe (fun a => by simp only [Pi.zero_apply, oVec_apply_inl])
    (fun b => by simp only [Pi.zero_apply, oVec_apply_inr])

variable [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι]

theorem oblk_mulVec_eq (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (v : ι → K) :
    oblk oe Y X *ᵥ v =
      oVec oe (Y *ᵥ fun a => v (oe (.inl a))) (X *ᵥ fun b => v (oe (.inr b))) :=
  oVec_ext oe (fun a => by rw [oblk_mulVec_inl, oVec_apply_inl])
    (fun b => by rw [oblk_mulVec_inr, oVec_apply_inr])

end Vectors

section Polar

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem quad_oe (v : ι → K) :
    Q v = Q₂ (fun a => v (oe (.inl a))) + quadPlus 2 K (fun b => v (oe (.inr b))) := by
  rw [hQ, coe_quadPlus]

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem polarBilin_oe (v w : ι → K) :
    Q.polarBilin v w = Q₂.polarBilin (fun a => v (oe (.inl a))) (fun a => w (oe (.inl a))) +
      (quadPlus 2 K).polarBilin (fun b => v (oe (.inr b))) (fun b => w (oe (.inr b))) := by
  simp only [polarBilin_apply_apply, polar]
  rw [quad_oe hQ, quad_oe hQ v, quad_oe hQ w]
  have e₂ : (fun a => (v + w) (oe (.inl a))) =
      (fun a => v (oe (.inl a))) + (fun a => w (oe (.inl a))) := rfl
  have e₁ : (fun b => (v + w) (oe (.inr b))) =
      (fun b => v (oe (.inr b))) + (fun b => w (oe (.inr b))) := rfl
  rw [e₂, e₁]
  ring

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem quad_oVec_inl (u : ι₂ → K) : Q (oVec oe u 0) = Q₂ u := by
  rw [quad_oe hQ, oVec_inl, oVec_inr, map_zero, add_zero]

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem quad_oVec_inr (u : Fin 2 ⊕ Fin 2 → K) : Q (oVec oe 0 u) = quadPlus 2 K u := by
  rw [quad_oe hQ, oVec_inl, oVec_inr, map_zero, zero_add]

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem polarBilin_oVec_inl (v : ι → K) (u : ι₂ → K) :
    Q.polarBilin v (oVec oe u 0) = Q₂.polarBilin (fun a => v (oe (.inl a))) u := by
  rw [polarBilin_oe hQ, oVec_inl, oVec_inr, map_zero, add_zero]

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem polarBilin_oVec_inr (v : ι → K) (u : Fin 2 ⊕ Fin 2 → K) :
    Q.polarBilin v (oVec oe 0 u) = (quadPlus 2 K).polarBilin (fun b => v (oe (.inr b))) u := by
  rw [polarBilin_oe hQ, oVec_inl, oVec_inr, map_zero, zero_add]

theorem cTwoX_oVec_inl (u z : ι₂ → K) :
    cTwoX Q (oVec oe u 0) (oVec oe z 0) = oblk oe (cTwoX Q₂ u z) 0 :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [cTwoX_mulVec, oblk_mulVec_eq, cTwoX_mulVec, zero_mulVec, polarBilin_oVec_inl hQ,
      polarBilin_oVec_inl hQ, smul_oVec, smul_oVec, oVec_add]
    simp only [smul_zero, add_zero]

theorem cTwoX_oVec_inr (u z : Fin 2 ⊕ Fin 2 → K) :
    cTwoX Q (oVec oe 0 u) (oVec oe 0 z) = oblk oe 0 (cTwoX (quadPlus 2 K) u z) :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [cTwoX_mulVec, oblk_mulVec_eq, cTwoX_mulVec, zero_mulVec, polarBilin_oVec_inr hQ,
      polarBilin_oVec_inr hQ, smul_oVec, smul_oVec, oVec_add]
    simp only [smul_zero, add_zero]

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem polarBilin_oVec_inl_inl (u z : ι₂ → K) :
    Q.polarBilin (oVec oe u 0) (oVec oe z 0) = Q₂.polarBilin u z := by
  rw [polarBilin_oVec_inl hQ, oVec_inl]

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem polarBilin_oVec_inr_inr (u z : Fin 2 ⊕ Fin 2 → K) :
    Q.polarBilin (oVec oe 0 u) (oVec oe 0 z) = (quadPlus 2 K).polarBilin u z := by
  rw [polarBilin_oVec_inr hQ, oVec_inr]

end Polar

section Rho

variable {K : Type} [Field K]

@[expose] def slTr (a : K) : SL(2, K) :=
  ⟨1 + single 0 1 a, det_transvection_of_ne 0 1 (by decide) a⟩

abbrev uE (c : Fin 2 ⊕ Fin 2) : Fin 2 ⊕ Fin 2 → K := Pi.single c 1

theorem polarBilin_quadPlus_uE (v : Fin 2 ⊕ Fin 2 → K) (s : Fin 2) :
    (quadPlus 2 K).polarBilin v (uE (.inl s)) = v (.inr s) := by
  rw [polarBilin_apply_apply, polar_quadPlus_single_inl]

theorem polarBilin_quadPlus_uE_inr (v : Fin 2 ⊕ Fin 2 → K) (s : Fin 2) :
    (quadPlus 2 K).polarBilin v (uE (.inr s)) = v (.inl s) := by
  rw [polarBilin_apply_apply, polar_quadPlus_single_inr]

theorem rhoOneMat_slTr (a : K) :
    rhoOneMat (slTr a) = 1 + a • cTwoX (quadPlus 2 K) (uE (.inl 0)) (uE (.inl 1)) := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [add_mulVec, one_mulVec, smul_mulVec, cTwoX_mulVec, polarBilin_quadPlus_uE,
    polarBilin_quadPlus_uE, rhoOneMat_apply]
  funext c
  rcases c with s | s <;> fin_cases s <;>
    simp [slTr, swapM, mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]

theorem quadPlus_two_uE_inl (s : Fin 2) : quadPlus 2 K (uE (.inl s)) = 0 := by
  rw [quadPlus_apply]
  simp [Pi.single_apply]

theorem polarBilin_uE_inl_inl (s t : Fin 2) :
    (quadPlus 2 K).polarBilin (uE (.inl s)) (uE (.inl t)) = 0 := by
  rw [polarBilin_quadPlus_uE]
  simp

theorem polarBilin_uE_inl_inr (s t : Fin 2) :
    (quadPlus 2 K).polarBilin (uE (.inl s)) (uE (.inr t)) = if s = t then 1 else 0 := by
  rw [polarBilin_quadPlus_uE_inr]
  simp [Pi.single_apply, eq_comm]

end Rho

section Targets

theorem oblk_one_add_smul {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
    [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} (a : K)
    (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    oblk oe 1 (1 + a • X) = 1 + a • oblk oe (0 : Matrix ι₂ ι₂ K) X := by
  rw [oblk_smul, smul_zero, ← oblk_one (oe := oe), oblk_add, add_zero]

theorem oblk_one_add_smul_left {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
    [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} (a : K) (Y : Matrix ι₂ ι₂ K) :
    oblk oe (1 + a • Y) 1 = 1 + a • oblk oe Y (0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  rw [oblk_smul, smul_zero, ← oblk_one (oe := oe), oblk_add, add_zero]

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

theorem oRhoOneGL_slTr (a : K) :
    ((oRhoOneGL oe (slTr a) : GL ι K) : Matrix ι ι K) =
      1 + a • cTwoX Q (oVec oe 0 (uE (.inl 0))) (oVec oe 0 (uE (.inl 1))) := by
  rw [coe_oRhoOneGL, rhoOneMat_slTr, cTwoX_oVec_inr hQ, oblk_one_add_smul]

theorem oKappaGL_oRhoOneGL_slTr {ι₃ : Type} [Fintype ι₃] [DecidableEq ι₃]
    {oe' : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂} {Q₃ : QuadraticForm K (ι₃ → K)}
    (hQ₂ : ∀ w, Q₂ w = Q₃ (fun a => w (oe' (.inl a))) +
      StatedQuadPlus 2 K (fun b => w (oe' (.inr b)))) (a : K) :
    ((oKappaGL oe (oRhoOneGL oe' (slTr a)) : GL ι K) : Matrix ι ι K) =
      1 + a • cTwoX Q (oVec oe (oVec oe' 0 (uE (.inl 0))) 0)
        (oVec oe (oVec oe' 0 (uE (.inl 1))) 0) := by
  rw [coe_oKappaGL, oRhoOneGL_slTr hQ₂, cTwoX_oVec_inl hQ, oblk_one_add_smul_left]

end Targets

end CFSG.ComponentClassification.RankTwoClassical
