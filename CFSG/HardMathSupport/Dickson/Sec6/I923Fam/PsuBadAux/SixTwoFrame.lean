module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Frame

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryFrame CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

variable {ℓ f m : ℕ} {K : Type} [Field K]

@[expose] def cframe (i₀ : Fin (m + 1)) : Fin m → Fin (m + 1) → K :=
  fun j => Pi.single (i₀.succAbove j) 1

theorem cframe_apply (i₀ : Fin (m + 1)) (j : Fin m) (k : Fin (m + 1)) :
    cframe (K := K) i₀ j k = if k = i₀.succAbove j then 1 else 0 := by
  simp [cframe, Pi.single_apply]

theorem frameMat_cframe_apply (i₀ : Fin (m + 1)) (k : Fin (m + 1)) (j : Fin m) :
    frameMat (cframe (K := K) i₀) k j = if k = i₀.succAbove j then 1 else 0 := by
  rw [frameMat, Matrix.of_apply, cframe_apply]

theorem cframe_isOrthonormal (h : UnitaryFieldData ℓ f K) (i₀ : Fin (m + 1)) :
    IsOrthonormalFamily h (cframe (K := K) i₀) := by
  intro j k
  rw [idForm_eq_dotProduct]
  simp only [cframe, dotProduct_single, Pi.single_apply, mul_one]
  by_cases hjk : j = k
  · subst hjk; simp
  · have : i₀.succAbove k ≠ i₀.succAbove j := fun hh => hjk (Fin.succAbove_right_injective hh).symm
    simp [this, hjk]

variable (h : UnitaryFieldData ℓ f K)

theorem frameEmb_cframe_apply (i₀ : Fin (m + 1)) (Y : Matrix (Fin m) (Fin m) K)
    (k l : Fin (m + 1)) :
    frameEmb h (cframe (K := K) i₀) Y k l =
      (if k = l then 1 else 0) + ∑ a : Fin m, ∑ b : Fin m,
        (if k = i₀.succAbove a then 1 else 0) * (Y a b - (if a = b then 1 else 0)) *
          (if l = i₀.succAbove b then 1 else 0) := by
  classical
  simp only [frameEmb, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.sub_apply,
    frameAdj_apply, frameMat_cframe_apply, cframe_apply]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb : h.bar (if l = i₀.succAbove b then (1 : K) else 0) =
      if l = i₀.succAbove b then 1 else 0 := by
    split_ifs <;> simp
  rw [hb, Finset.sum_mul]

theorem frameEmb_cframe_sigma (i₀ : Fin (m + 1)) (Y : Matrix (Fin m) (Fin m) K) (a b : Fin m) :
    frameEmb h (cframe (K := K) i₀) Y (i₀.succAbove a) (i₀.succAbove b) = Y a b := by
  classical
  rw [frameEmb_cframe_apply]
  have hinj : ∀ x y : Fin m, i₀.succAbove x = i₀.succAbove y ↔ x = y := fun x y =>
    Fin.succAbove_right_inj
  simp only [hinj, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab]

theorem frameEmb_cframe_left (i₀ : Fin (m + 1)) (Y : Matrix (Fin m) (Fin m) K) (l : Fin (m + 1)) :
    frameEmb h (cframe (K := K) i₀) Y i₀ l = if i₀ = l then 1 else 0 := by
  classical
  rw [frameEmb_cframe_apply]
  simp [(Fin.succAbove_ne i₀ _).symm]

theorem frameEmb_cframe_right (i₀ : Fin (m + 1)) (Y : Matrix (Fin m) (Fin m) K) (k : Fin (m + 1)) :
    frameEmb h (cframe (K := K) i₀) Y k i₀ = if k = i₀ then 1 else 0 := by
  classical
  rw [frameEmb_cframe_apply]
  simp [(Fin.succAbove_ne i₀ _).symm]

@[expose] def dmat (i₀ : Fin (m + 1)) (ν μ : K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  Matrix.diagonal (fun i => if i = i₀ then μ else ν)

theorem frameEmb_commute_dmat (i₀ : Fin (m + 1)) (ν μ : K) (Y : Matrix (Fin m) (Fin m) K) :
    dmat i₀ ν μ * frameEmb h (cframe i₀) Y = frameEmb h (cframe i₀) Y * dmat i₀ ν μ := by
  classical
  ext k l
  simp only [dmat, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hkl : (k = i₀ ↔ l = i₀)
  · have : (if k = i₀ then μ else ν) = (if l = i₀ then μ else ν) := by
      by_cases hk : k = i₀
      · simp [hk, hkl.1 hk]
      · simp [hk, (not_congr hkl).1 hk]
    rw [this, mul_comm]
  · have hz : frameEmb h (cframe i₀) Y k l = 0 := by
      by_cases hk : k = i₀
      · have hl : l ≠ i₀ := fun hl => hkl ⟨fun _ => hl, fun _ => hk⟩
        rw [hk, frameEmb_cframe_left, if_neg (Ne.symm hl)]
      · have hl : l = i₀ := by
          by_contra hl
          exact hkl ⟨fun h' => absurd h' hk, fun h' => absurd h' hl⟩
        rw [hl, frameEmb_cframe_right, if_neg hk]
    rw [hz]
    simp

theorem entry_eq_zero_left {ν μ : K} (hνμ : ν ≠ μ) (i₀ : Fin (m + 1))
    {W : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hW : W * dmat i₀ ν μ = dmat i₀ ν μ * W)
    (b : Fin m) : W i₀ (i₀.succAbove b) = 0 := by
  have h1 := congrFun (congrFun hW i₀) (i₀.succAbove b)
  simp only [dmat, Matrix.mul_diagonal, Matrix.diagonal_mul, if_pos, Fin.succAbove_ne, if_neg,
    not_false_eq_true, if_true] at h1
  have h2 : W i₀ (i₀.succAbove b) * (ν - μ) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3) hνμ

theorem entry_eq_zero_right {ν μ : K} (hνμ : ν ≠ μ) (i₀ : Fin (m + 1))
    {W : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hW : W * dmat i₀ ν μ = dmat i₀ ν μ * W)
    (a : Fin m) : W (i₀.succAbove a) i₀ = 0 := by
  have h1 := congrFun (congrFun hW (i₀.succAbove a)) i₀
  simp only [dmat, Matrix.mul_diagonal, Matrix.diagonal_mul, if_pos, Fin.succAbove_ne, if_neg,
    not_false_eq_true, if_true] at h1
  have h2 : W (i₀.succAbove a) i₀ * (μ - ν) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3).symm hνμ

theorem eq_smul_frameEmb_of_commute {ν μ : K} (hνμ : ν ≠ μ) (i₀ : Fin (m + 1))
    {W : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hW : W * dmat i₀ ν μ = dmat i₀ ν μ * W)
    (hc : W i₀ i₀ ≠ 0) :
    W = (W i₀ i₀) • frameEmb h (cframe i₀)
      ((W i₀ i₀)⁻¹ • W.submatrix i₀.succAbove i₀.succAbove) := by
  classical
  ext k l
  obtain hk | ⟨a, hk⟩ := Fin.eq_self_or_eq_succAbove i₀ k <;>
  obtain hl | ⟨b, hl⟩ := Fin.eq_self_or_eq_succAbove i₀ l
  · rw [hk, hl, Matrix.smul_apply, frameEmb_cframe_left, if_pos rfl]
    simp
  · rw [hk, hl, Matrix.smul_apply, frameEmb_cframe_left, if_neg (Fin.succAbove_ne i₀ b).symm,
      entry_eq_zero_left hνμ i₀ hW b]
    simp
  · rw [hk, hl, Matrix.smul_apply, frameEmb_cframe_right, if_neg (Fin.succAbove_ne i₀ a),
      entry_eq_zero_right hνμ i₀ hW a]
    simp
  · rw [hk, hl, Matrix.smul_apply, frameEmb_cframe_sigma, Matrix.smul_apply, Matrix.submatrix_apply]
    simp [hc]

end CFSG.HardMathSupport.Dickson.Sec6.I923
