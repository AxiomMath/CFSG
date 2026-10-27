module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3N
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUa
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3L
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatFactsL4U4 DiagU StabU UnitaryOut UnitaryConj HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {Q₀ : GL (Fin 4) K}
  (hQ : uStar h (Q₀ : Matrix (Fin 4) (Fin 4) K) * (Q₀ : Matrix (Fin 4) (Fin 4) K) = stdG)

include hQ in
theorem frame_mem_SU {D : GL (Fin 4) K} (hD1 : (D : Matrix (Fin 4) (Fin 4) K).det = 1)
    (hDu : uStar h (D : Matrix (Fin 4) (Fin 4) K) * stdG * (D : Matrix (Fin 4) (Fin 4) K) =
      stdG) :
    Q₀ * D * Q₀⁻¹ ∈ unitarySU p f K 4 := by
  rw [mem_unitarySU_iff h]
  set M₀ : Matrix (Fin 4) (Fin 4) K := (Q₀ : Matrix (Fin 4) (Fin 4) K) with hM₀
  set Mi : Matrix (Fin 4) (Fin 4) K := ((Q₀⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hMi
  have h1 : M₀ * Mi = 1 := by rw [hM₀, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : Mi * M₀ = 1 := by rw [hM₀, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hD1, mul_one, ← det_mul, h1, det_one]
  · change uStar h (M₀ * (D : Matrix (Fin 4) (Fin 4) K) * Mi) *
      (M₀ * (D : Matrix (Fin 4) (Fin 4) K) * Mi) = 1
    calc uStar h (M₀ * (D : Matrix (Fin 4) (Fin 4) K) * Mi) *
          (M₀ * (D : Matrix (Fin 4) (Fin 4) K) * Mi)
        = uStar h Mi * (uStar h (D : Matrix (Fin 4) (Fin 4) K) * (uStar h M₀ * M₀) *
            (D : Matrix (Fin 4) (Fin 4) K)) * Mi := by
          rw [uStar_mul, uStar_mul]
          simp only [Matrix.mul_assoc]
      _ = uStar h Mi * (uStar h M₀ * M₀) * Mi := by rw [hQ, hDu]
      _ = uStar h (M₀ * Mi) * (M₀ * Mi) := by rw [uStar_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, uStar_one, Matrix.one_mul]

@[expose] def pairU : SpecialLinearGroup (Fin 2) K →* unitarySU p f K 4 where
  toFun a := ⟨Q₀ * SpecialLinearGroup.toGL (pairSL h a) * Q₀⁻¹,
    frame_mem_SU h hQ (pairSL h a).2 (uStar_pair h a)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [map_mul, Subgroup.coe_mul]; group)

theorem coe_pairU (a : SpecialLinearGroup (Fin 2) K) :
    ((pairU h hQ a : unitarySU p f K 4) : GL (Fin 4) K) =
      Q₀ * SpecialLinearGroup.toGL (pairSL h a) * Q₀⁻¹ := rfl

@[expose] def swapGL : GL (Fin 4) K :=
  ⟨blk 0 1 1 0, -blk 0 1 1 0, by rw [Matrix.mul_neg, CSU.swap_mul_swap, neg_neg],
    by rw [Matrix.neg_mul, CSU.swap_mul_swap, neg_neg]⟩

@[expose] def kappaU : unitarySU p f K 4 :=
  ⟨Q₀ * swapGL * Q₀⁻¹, frame_mem_SU h hQ CSU.det_swap (CSU.unitary_swap h)⟩

theorem kappaU_sq : kappaU h hQ * kappaU h hQ = negOneU h := by
  apply Subtype.ext
  apply Units.ext
  change ((Q₀ * swapGL * Q₀⁻¹ * (Q₀ * swapGL * Q₀⁻¹) : GL (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K) = (((negOneU h : unitarySU p f K 4) : GL (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K)
  rw [coe_negOneU, show Q₀ * swapGL * Q₀⁻¹ * (Q₀ * swapGL * Q₀⁻¹) =
    Q₀ * (swapGL * swapGL) * Q₀⁻¹ by group, Units.val_mul, Units.val_mul, Units.val_mul]
  change (Q₀ : Matrix (Fin 4) (Fin 4) K) * (blk 0 1 1 0 * blk 0 1 1 0) *
    ((Q₀⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1
  rw [CSU.swap_mul_swap, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one]

theorem kappaU_conj_pairU (a : SpecialLinearGroup (Fin 2) K) :
    kappaU h hQ * pairU h hQ a * (kappaU h hQ)⁻¹ =
      pairU h hQ (SpecialLinearGroup.map h.bar a) := by
  have hsw : swapGL * SpecialLinearGroup.toGL (pairSL h a) =
      SpecialLinearGroup.toGL (pairSL h (SpecialLinearGroup.map h.bar a)) * swapGL :=
    Units.ext (swap_mul_pair h a)
  apply Subtype.ext
  change Q₀ * swapGL * Q₀⁻¹ * (Q₀ * SpecialLinearGroup.toGL (pairSL h a) * Q₀⁻¹) *
    (Q₀ * swapGL * Q₀⁻¹)⁻¹ = Q₀ * SpecialLinearGroup.toGL (pairSL h
      (SpecialLinearGroup.map h.bar a)) * Q₀⁻¹
  calc Q₀ * swapGL * Q₀⁻¹ * (Q₀ * SpecialLinearGroup.toGL (pairSL h a) * Q₀⁻¹) *
        (Q₀ * swapGL * Q₀⁻¹)⁻¹ =
        Q₀ * (swapGL * SpecialLinearGroup.toGL (pairSL h a)) * swapGL⁻¹ * Q₀⁻¹ := by group
    _ = Q₀ * SpecialLinearGroup.toGL (pairSL h (SpecialLinearGroup.map h.bar a)) * Q₀⁻¹ := by
        rw [hsw]; group

@[expose] def X1GL {l : K} (hl : l ≠ 0) : GL (Fin 4) K :=
  ⟨X1 l, X1 l⁻¹, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X1, Matrix.mul_apply, Fin.sum_univ_four, hl], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X1, Matrix.mul_apply, Fin.sum_univ_four, hl]⟩

theorem X1_swap_X1 {l : K} (hl : l ≠ 0) :
    ((X1GL hl * swapGL * (X1GL hl)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      -blk 0 1 1 0 := by
  change X1 l * blk 0 1 1 0 * X1 l⁻¹ = -blk 0 1 1 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1, blk, Matrix.mul_apply, Fin.sum_univ_four, hl]

end CFSG.ComponentClassification.HarrisLit.C3
