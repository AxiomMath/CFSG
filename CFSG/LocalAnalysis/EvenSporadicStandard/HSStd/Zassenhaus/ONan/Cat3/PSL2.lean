module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

open Subgroup CFSG.Open
open Matrix

private def pslX (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, -1]

private lemma pslX_det (K : Type) [Field K] : (pslX K).det = 1 := by
  simp [pslX, Matrix.det_fin_two]

private lemma pslX_trace (K : Type) [Field K] : (pslX K).trace = -1 := by
  simp [pslX, Matrix.trace_fin_two]

private lemma pslX_pow_three (K : Type) [Field K] : (pslX K) ^ 3 = 1 := by
  rw [pow_three']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pslX, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private def pslXGL (K : Type) [Field K] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (pslX K) (by rw [pslX_det]; exact one_ne_zero)

private def pslXSL (K : Type) [Field K] : StatedSL 2 K :=
  ⟨pslXGL K, by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    show (pslX K).det = 1
    exact pslX_det K⟩

private lemma pslXSL_pow_three (K : Type) [Field K] :
    ((pslXSL K : StatedSL 2 K) : GL (Fin 2) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  show (pslX K) ^ 3 = 1
  exact pslX_pow_three K

private lemma pslXSL_not_mem_scalars (K : Type) [Field K] :
    ((pslXSL K : StatedSL 2 K) : GL (Fin 2) K) ∉ StatedScalars (Fin 2) K := by
  intro hmem
  obtain ⟨u, hu⟩ := (MonoidHom.mem_range).mp hmem
  have h := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 0) hu
  have hleft : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    simp
  have hright : (((pslXSL K : StatedSL 2 K) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    show (pslX K) 1 0 = 1
    simp [pslX]
  rw [hleft, hright] at h
  exact zero_ne_one h

private lemma commute_of_commute_pslX {K : Type} [Field K]
    {M N : Matrix (Fin 2) (Fin 2) K}
    (hM : M * pslX K = pslX K * M) (hN : N * pslX K = pslX K * N) :
    M * N = N * M := by
  have hM10 : M 1 0 = - M 0 1 := by
    have h := congrFun (congrFun hM 0) 0
    have h' : M 0 1 = - M 1 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, pslX] using h
    rw [h']; ring
  have hM11 : M 1 1 = M 0 0 + M 0 1 := by
    have h := congrFun (congrFun hM 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, pslX] at h
    have h' : M 0 0 + M 0 1 = M 1 1 := by
      apply neg_injective
      rw [neg_add]
      exact h
    exact h'.symm
  have hN10 : N 1 0 = - N 0 1 := by
    have h := congrFun (congrFun hN 0) 0
    have h' : N 0 1 = - N 1 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, pslX] using h
    rw [h']; ring
  have hN11 : N 1 1 = N 0 0 + N 0 1 := by
    have h := congrFun (congrFun hN 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, pslX] at h
    have h' : N 0 0 + N 0 1 = N 1 1 := by
      apply neg_injective
      rw [neg_add]
      exact h
    exact h'.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hM10, hM11, hN10, hN11] <;> ring

private lemma mat_comm_of_proj_comm {K : Type} [Field K] (g : StatedSL 2 K)
    (h : (QuotientGroup.mk g : StatedProj (StatedSL 2 K)) *
        QuotientGroup.mk (pslXSL K) =
      QuotientGroup.mk (pslXSL K) * QuotientGroup.mk g) :
    ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * pslX K =
      pslX K * ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  let Gm : Matrix (Fin 2) (Fin 2) K := ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  let Gi : Matrix (Fin 2) (Fin 2) K :=
    ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  have hcomm' : (QuotientGroup.mk (g * pslXSL K) : StatedProj (StatedSL 2 K)) =
      QuotientGroup.mk (pslXSL K * g) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact h
  obtain ⟨u, hu⟩ := (CFSG.Open.StatedAPI.statedProj_mk_eq_iff (StatedSL 2 K)
    (g * pslXSL K) (pslXSL K * g)).mp hcomm'
  have hu' : pslX K * Gm = Gm * pslX K *
      ((u : K) • (1 : Matrix (Fin 2) (Fin 2) K)) := by
    simpa [Gm, Subgroup.coe_mul, Units.val_mul, pslXSL, pslXGL] using hu
  have hGiG : Gi * Gm = 1 := by
    show ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGmGi : Gm * Gi = 1 := by
    show ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconj : Gi * pslX K * Gm = (u : K) • pslX K := by
    calc Gi * pslX K * Gm
        = Gi * (pslX K * Gm) := by rw [mul_assoc]
      _ = Gi * (Gm * pslX K * ((u : K) • (1 : Matrix (Fin 2) (Fin 2) K))) := by
            rw [hu']
      _ = (Gi * Gm) * pslX K * ((u : K) • (1 : Matrix (Fin 2) (Fin 2) K)) := by
            simp only [mul_assoc]
      _ = pslX K * ((u : K) • (1 : Matrix (Fin 2) (Fin 2) K)) := by rw [hGiG, one_mul]
      _ = (u : K) • pslX K := by rw [Matrix.mul_smul, Matrix.mul_one]
  have ht : (pslX K).trace = (u : K) * (pslX K).trace := by
    have h := congrArg Matrix.trace hconj
    rw [Matrix.trace_mul_cycle Gi (pslX K) Gm, hGmGi, Matrix.one_mul, Matrix.trace_smul,
      smul_eq_mul] at h
    exact h
  have hu1 : (u : K) = 1 := by
    rw [pslX_trace] at ht
    apply mul_right_cancel₀ (show (-1 : K) ≠ 0 by simp)
    simpa using ht.symm
  rw [hu1] at hu'
  simpa [Gm] using hu'.symm

theorem false_of_psl_two {K : Type} [Field K] [Finite K]
    (hC : CentHyp (StatedProj (StatedSL 2 K))) : False := by
  have hx : orderOf (QuotientGroup.mk (pslXSL K) : StatedProj (StatedSL 2 K)) = 3 := by
    apply orderOf_mk_eq_prime
    · rw [pslXSL_pow_three K]
      exact Subgroup.one_mem _
    · exact pslXSL_not_mem_scalars K
  obtain ⟨a, b, ha, hb, hne⟩ := CentHyp.not_comm hC hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
  have hgM := mat_comm_of_proj_comm g ha
  have hhM := mat_comm_of_proj_comm h hb
  have hmat := commute_of_commute_pslX hgM hhM
  have hgh : g * h = h * g := by
    apply Subtype.ext
    apply Units.ext
    simpa [Subgroup.coe_mul, Units.val_mul] using hmat
  have hmk : (QuotientGroup.mk g : StatedProj (StatedSL 2 K)) * QuotientGroup.mk h =
      (QuotientGroup.mk h : StatedProj (StatedSL 2 K)) * QuotientGroup.mk g := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hgh]
  exact hne hmk

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3