module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4B

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher BS4 BL4

variable {p f : ℕ} {K : Type} [Field K]

abbrev MH (K : Type) [Field K] : Type := Matrix (HypIndex 2 0) (HypIndex 2 0) K

@[expose] noncomputable def cv (G : GL (HypIndex 2 0) K) (M : MH K) : MB K :=
  rv (((G⁻¹ : GL (HypIndex 2 0) K) : MH K) * M * (G : MH K))

@[expose] noncomputable def sv (h : UnitaryFieldData p f K) (G : GL (HypIndex 2 0) K)
    (A : MH K) : MB K :=
  rv (((G⁻¹ : GL (HypIndex 2 0) K) : MH K) * A * (G : MH K).map h.bar)

variable (G : GL (HypIndex 2 0) K)

theorem gi_mul_g : ((G⁻¹ : GL (HypIndex 2 0) K) : MH K) * (G : MH K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem g_mul_gi : (G : MH K) * ((G⁻¹ : GL (HypIndex 2 0) K) : MH K) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem g_mul_gi_assoc (X : MH K) :
    (G : MH K) * (((G⁻¹ : GL (HypIndex 2 0) K) : MH K) * X) = X := by
  rw [← Matrix.mul_assoc, g_mul_gi, Matrix.one_mul]

theorem cv_mul (M N : MH K) : cv G (M * N) = cv G M * cv G N := by
  simp only [cv]
  rw [← map_mul]
  congr 1
  simp only [Matrix.mul_assoc, g_mul_gi_assoc]

theorem cv_one : cv G (1 : MH K) = 1 := by
  rw [cv, Matrix.mul_one, gi_mul_g, map_one]

theorem cv_smul (μ : K) (M : MH K) : cv G (μ • M) = μ • cv G M := by
  rw [cv, cv, Matrix.mul_smul, Matrix.smul_mul, map_smul]

theorem cv_sq {M : MH K} {s : K} (hM : M * M = s • 1) : cv G M * cv G M = s • 1 := by
  rw [← cv_mul, hM, cv_smul, cv_one]

theorem cv_ns {M : MH K} (hM : ∀ μ : K, M ≠ μ • 1) : ∀ μ : K, cv G M ≠ μ • 1 := by
  intro μ hμ
  apply hM μ
  have e : ((G⁻¹ : GL (HypIndex 2 0) K) : MH K) * M * (G : MH K) = μ • 1 :=
    rv.injective (by rw [map_smul, map_one]; exact hμ)
  calc M = (G : MH K) * (((G⁻¹ : GL (HypIndex 2 0) K) : MH K) * M * (G : MH K)) *
        ((G⁻¹ : GL (HypIndex 2 0) K) : MH K) := by
        simp only [Matrix.mul_assoc, g_mul_gi_assoc, g_mul_gi, Matrix.mul_one]
    _ = μ • 1 := by
        rw [e, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, g_mul_gi]

theorem cv_herm {h : UnitaryFieldData p f K} (hG : G ∈ hypUnitary h 2 0) {M : MH K}
    (hM : (M.map h.bar)ᵀ * hypGram 2 0 K * M = hypGram 2 0 K) :
    ((cv G M).map h.bar)ᵀ * jU * cv G M = jU := by
  have hGi := mem_hypUnitary.mp (inv_mem hG)
  have hY := herm_mul (herm_mul hGi hM) (mem_hypUnitary.mp hG)
  rw [cv, ← rv_map, ← rv_transpose, ← rv_hypGram, ← map_mul, ← map_mul, hY]

theorem cv_sv (h : UnitaryFieldData p f K) (B A : MH K) :
    cv G B * sv h G A * (cv G B).map h.bar = sv h G (B * A * B.map h.bar) := by
  have hb : (G : MH K).map h.bar * ((G⁻¹ : GL (HypIndex 2 0) K) : MH K).map h.bar = 1 := by
    rw [← Matrix.map_mul, g_mul_gi, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  have hb' : ∀ X : MH K, (G : MH K).map h.bar *
      (((G⁻¹ : GL (HypIndex 2 0) K) : MH K).map h.bar * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hb, Matrix.one_mul]
  simp only [cv, sv]
  rw [← rv_map, ← map_mul, ← map_mul]
  congr 1
  simp only [Matrix.map_mul, Matrix.mul_assoc, g_mul_gi_assoc, hb']

theorem det_sv (h : UnitaryFieldData p f K) (A : GL (HypIndex 2 0) K) :
    (sv h G (A : MH K)).det ≠ 0 := by
  have hb : ((G : MH K).map h.bar).det *
      (((G⁻¹ : GL (HypIndex 2 0) K) : MH K).map h.bar).det = 1 := by
    rw [← det_mul, ← Matrix.map_mul, g_mul_gi, Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
      det_one]
  rw [sv, det_rv, det_mul, det_mul]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (left_ne_zero_of_mul_eq_one hb)
  · exact ((Matrix.isUnit_iff_isUnit_det _).mp (G⁻¹ : GL (HypIndex 2 0) K).isUnit).ne_zero
  · exact ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
