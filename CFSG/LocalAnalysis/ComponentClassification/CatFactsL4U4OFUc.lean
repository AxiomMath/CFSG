module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OFUa

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OFU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem scalar_mem_uMat {c : Kˣ} (hc : h.bar (c : K) * c = 1) :
    GeneralLinearGroup.scalar (Fin 4) c ∈ uMat h 4 := by
  rw [mem_uMat, GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.scalar_apply, hc]
  · simp [Matrix.scalar_apply, Matrix.one_apply_ne hij, Matrix.mul_apply, Matrix.diagonal_apply,
      hij]

theorem conj_mem_uMat (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {M : GL (Fin 4) K}
    (hM : uStar h (M : Matrix (Fin 4) (Fin 4) K) * stdG * (M : Matrix (Fin 4) (Fin 4) K) = stdG) :
    P * M * P⁻¹ ∈ uMat h 4 := by
  rw [mem_uMat]
  have hPi := uStar_inv_mul h P hP
  change uStar h ((P * M * P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * _ = 1
  rw [Units.val_mul, Units.val_mul, uStar_mul, uStar_mul]
  calc uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
        (uStar h (M : Matrix (Fin 4) (Fin 4) K) * uStar h (P : Matrix (Fin 4) (Fin 4) K)) *
        ((P : Matrix (Fin 4) (Fin 4) K) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
      uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
        (uStar h (M : Matrix (Fin 4) (Fin 4) K) *
          (uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K)) * M) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hP, hM]
        exact hPi

include h in
theorem exists_conj_hyp (P P' : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    (hP' : uStar h (P' : Matrix (Fin 4) (Fin 4) K) * (P' : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} {A : GL (Fin 4) K} (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l) :
    ∃ g : unitarySU p f K 4,
      (((g : GL (Fin 4) K) * A * (g : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) * P' = P' * X1 l := by
  classical
  set g₀ : GL (Fin 4) K := P' * P⁻¹ with hg₀
  have hg₀u : g₀ ∈ uMat h 4 := by
    rw [mem_uMat]
    change uStar h ((P' * P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * _ = 1
    rw [Units.val_mul, uStar_mul]
    calc uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * uStar h (P' : Matrix (Fin 4) (Fin 4) K) *
          ((P' : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
        uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          (uStar h (P' : Matrix (Fin 4) (Fin 4) K) * (P' : Matrix (Fin 4) (Fin 4) K)) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hP']; exact uStar_inv_mul h P hP
  set d : K := (g₀ : Matrix (Fin 4) (Fin 4) K).det with hd
  have hd0 : d ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 g₀.isUnit).ne_zero
  have hdN : h.bar d * d = 1 := by
    have e := congrArg Matrix.det ((mem_uMat h).1 hg₀u)
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at e
    have e2 : ((g₀ : Matrix (Fin 4) (Fin 4) K).map h.bar).det = h.bar d := by
      rw [hd, RingHom.map_det]
      rfl
    rw [e2] at e
    exact e
  have hNinv : h.norm d⁻¹ = 1 := by
    rw [UnitaryFieldData.norm, map_inv₀, ← mul_inv, mul_comm, hdN, inv_one]
  obtain ⟨r, hr0, hr⟩ := h.exists_div_bar_eq hNinv
  have hDdet : (dU h r).det ≠ 0 := by
    rw [det_dU, hr]
    exact inv_ne_zero hd0
  set D : GL (Fin 4) K := GeneralLinearGroup.mkOfDetNeZero (dU h r) hDdet with hD
  have hDm : (D : Matrix (Fin 4) (Fin 4) K) = dU h r := GeneralLinearGroup.val_mkOfDetNeZero _ _
  set c : GL (Fin 4) K := P * D * P⁻¹ with hc
  have hcu : c ∈ uMat h 4 := conj_mem_uMat h P hP (M := D) (by rw [hDm]; exact unitary_dU h hr0)
  have hcA : c * A = A * c := by
    apply Units.ext
    have hAm : (A : Matrix (Fin 4) (Fin 4) K) =
        (P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
      rw [← hAP, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
    have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, hc, Units.val_mul, Units.val_mul, hDm, hAm]
    calc (P : Matrix (Fin 4) (Fin 4) K) * dU h r * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          ((P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
        (P : Matrix (Fin 4) (Fin 4) K) * (dU h r * X1 l) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K), hPP, Matrix.one_mul]
      _ = (P : Matrix (Fin 4) (Fin 4) K) * (X1 l * dU h r) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by rw [dU_comm_X1]
      _ = (P : Matrix (Fin 4) (Fin 4) K) * X1 l * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          ((P : Matrix (Fin 4) (Fin 4) K) * dU h r * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) (P : Matrix (Fin 4) (Fin 4) K),
            hPP, Matrix.one_mul]
  set g : GL (Fin 4) K := g₀ * c with hg
  have hgu : g ∈ uMat h 4 := mul_mem hg₀u hcu
  have hgdet : (g : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    have hcdet : (c : Matrix (Fin 4) (Fin 4) K).det = d⁻¹ := by
      rw [hc, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hDm, det_dU, hr,
        mul_comm, ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.det_one, one_mul]
    rw [hg, Units.val_mul, Matrix.det_mul, hcdet, ← hd, mul_inv_cancel₀ hd0]
  have hgSU : g ∈ unitarySU p f K 4 := (mem_unitarySU_iff h).2 ⟨hgdet, (mem_uMat h).1 hgu⟩
  refine ⟨⟨g, hgSU⟩, ?_⟩
  change ((g * A * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P' = P' * X1 l
  have e1 : g * A * g⁻¹ = P' * P⁻¹ * A * P * P'⁻¹ := by
    rw [hg, hg₀, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv]
    calc P' * P⁻¹ * c * A * (c⁻¹ * (P * P'⁻¹)) = P' * P⁻¹ * (c * A) * c⁻¹ * (P * P'⁻¹) := by
          group
      _ = P' * P⁻¹ * (A * c) * c⁻¹ * (P * P'⁻¹) := by rw [hcA]
      _ = P' * P⁻¹ * A * P * P'⁻¹ := by group
  rw [e1]
  have e2 : P' * P⁻¹ * A * P * P'⁻¹ * P' = P' * (P⁻¹ * A * P) := by group
  rw [← Units.val_mul, e2, Units.val_mul]
  congr 1
  rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mul]

end OFU

end CFSG.ComponentClassification.CatFactsL4U4
