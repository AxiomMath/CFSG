module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3FiveLocE1

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.LocalAnalysis.ComponentInitial Matrix GenLocL3Pair GenLocL3Good GenLocL3Nine
  GenLocL3NineR3
open scoped MatrixGroups

namespace GenLocL3Five

@[expose] def dSL (a b c : K5) (h : a * b * c = 1) : SL(3, K5) :=
  ⟨Matrix.diagonal ![a, b, c], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using h⟩

theorem coe_dSL (a b c : K5) (h : a * b * c = 1) :
    ((dSL a b c h : SL(3, K5)) : Matrix (Fin 3) (Fin 3) K5) = Matrix.diagonal ![a, b, c] := rfl

theorem diag_sandwich (d : Fin 3 → K5) (A : Matrix (Fin 3) (Fin 3) K5) (i l : Fin 3) :
    (Matrix.diagonal d * A * (Matrix.diagonal d).transpose) i l = d i * A i l * d l := by
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_transpose]

theorem fixed_dSL_of_diag (u : Fin 3 → K5ˣ) (a b c : K5) (h : a * b * c = 1) :
    LinearFlag.conjAut 3 K5 (diag3 u) (LinearFlag.proj 3 K5 (dSL a b c h)) =
      LinearFlag.proj 3 K5 (dSL a b c h) := by
  rw [conjAut_fixed_iff, coe_diag3, coe_dSL, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem fixed_dual_dSL (u : Fin 3 → K5ˣ) (a b c : K5) (h : a * b * c = 1) (ha : a * a = 1)
    (hb : b * b = 1) (hc : c * c = 1) :
    (LinearFlag.conjAut 3 K5 (diag3 u) * LinearFlag.dualAut 3 K5) (LinearFlag.proj 3 K5 (dSL a b c h)) =
      LinearFlag.proj 3 K5 (dSL a b c h) := by
  rw [conjAut_dual_fixed_iff, coe_dSL, coe_diag3, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · show a * (u 0 : K5) * a = (u 0 : K5)
    linear_combination (u 0 : K5) * ha
  · show b * (u 1 : K5) * b = (u 1 : K5)
    linear_combination (u 1 : K5) * hb
  · show c * (u 2 : K5) * c = (u 2 : K5)
    linear_combination (u 2 : K5) * hc

theorem off_zero (d : Fin 3 → K5) (N : Matrix (Fin 3) (Fin 3) K5)
    (h : Matrix.diagonal d * N = N * Matrix.diagonal d) (i l : Fin 3) (hne : d i - d l ≠ 0) :
    N i l = 0 :=
  (mul_eq_zero.1 (comm_entry d N h i l)).resolve_left hne

theorem diag_pow4 (N : Matrix (Fin 3) (Fin 3) K5) (hdiag : N.IsDiag) (hdet : N.det ≠ 0) :
    N ^ 4 = 1 := by
  have hND : N = Matrix.diagonal (Matrix.diag N) := hdiag.diagonal_diag.symm
  have hne : ∀ i, N i i ≠ 0 := by
    intro i
    rw [hND, Matrix.det_diagonal] at hdet
    exact (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  have key4 : ∀ x : K5, x ≠ 0 → x ^ 4 = 1 := by decide
  rw [hND, Matrix.diagonal_pow]
  convert Matrix.diagonal_one (n := Fin 3) (α := K5) using 2
  ext i
  exact key4 _ (hne i)

theorem locE2_five (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K5))) (hfs : D ≤ frameStab 3 K5)
    (hA : CFSG.IsElementaryAbelian 2 ↥D) [Finite ↥D] : LocE2 D.subtype := by
  have hα : D.subtype.range ≤ frameStab 3 K5 := by rwa [Subgroup.range_subtype]
  have hadm := adm_comap_noDual hA D.subtype hα
  set E : Subgroup ↥D := (noDual K5).comap D.subtype with hE
  have hfix : ∀ (a b c : K5) (h : a * b * c = 1), ∀ ψ ∈ E.map D.subtype,
      ψ (LinearFlag.proj 3 K5 (dSL a b c h)) = LinearFlag.proj 3 K5 (dSL a b c h) := by
    rintro a b c h _ ⟨e, he, rfl⟩
    obtain ⟨x, σ, hx, hax⟩ := he
    obtain ⟨u, rfl⟩ := exists_diag3 hx
    have : D.subtype e = LinearFlag.conjAut 3 K5 (diag3 u) := by
      rw [hax, sigma_eq_one card_K5 σ, map_one, mul_one]
    rw [this]
    exact fixed_dSL_of_diag u a b c h
  refine locE2_of_fix D.subtype (fixedIn _ (E.map D.subtype)) (le_gammaAct D.subtype hadm) ?_
  intro φ hφ
  have hφ1 := hφ _ (mem_fixedIn.2 (hfix (-1) (-1) 1 (by decide)))
  have hφ2 := hφ _ (mem_fixedIn.2 (hfix (-1) 1 (-1) (by decide)))
  have hφ3 := hφ _ (mem_fixedIn.2 (hfix 2 2 4 (by decide)))
  obtain ⟨A, σ, ε, hε, hφeq⟩ := (LinearFlag.automorphism_generation (K := K5) (n := 3) le_rfl).2 φ
  rw [sigma_eq_one card_K5 σ, map_one, mul_one] at hφeq
  have hdet : (A : Matrix (Fin 3) (Fin 3) K5).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hφeq
    rw [hφeq] at hφ1 hφ2
    have c1 := (conjAut_fixed_iff A _).1 hφ1
    have c2 := (conjAut_fixed_iff A _).1 hφ2
    rw [coe_dSL] at c1 c2
    have hdiag : (A : Matrix (Fin 3) (Fin 3) K5).IsDiag := by
      intro i l hil
      fin_cases i <;> fin_cases l
      · exact absurd rfl hil
      · exact off_zero ![-1, 1, -1] _ c2.symm 0 1 (by decide)
      · exact off_zero ![-1, -1, 1] _ c1.symm 0 2 (by decide)
      · exact off_zero ![-1, 1, -1] _ c2.symm 1 0 (by decide)
      · exact absurd rfl hil
      · exact off_zero ![-1, -1, 1] _ c1.symm 1 2 (by decide)
      · exact off_zero ![-1, -1, 1] _ c1.symm 2 0 (by decide)
      · exact off_zero ![-1, -1, 1] _ c1.symm 2 1 (by decide)
      · exact absurd rfl hil
    have h4 : A ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, diag_pow4 _ hdiag hdet]; rfl)
    refine ⟨2, ?_⟩
    rw [hφeq, show (2 : ℕ) ^ 2 = 4 by norm_num, ← map_pow, h4, map_one]
  · exfalso
    rw [pow_one] at hφeq
    rw [hφeq] at hφ3
    have c3 := (conjAut_dual_fixed_iff A _).1 hφ3
    rw [coe_dSL] at c3
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero 0 fun l => ?_
    have h5 := congrFun (congrFun c3 0) l
    rw [diag_sandwich] at h5
    have e0 : (![(2 : K5), 2, 4] 0) = 2 := rfl
    rw [e0] at h5
    have hne : (2 * ![(2 : K5), 2, 4] l - 1) ≠ 0 := by fin_cases l <;> decide
    have h6 : (2 * ![(2 : K5), 2, 4] l - 1) * (A : Matrix (Fin 3) (Fin 3) K5) 0 l = 0 := by
      linear_combination h5
    exact (mul_eq_zero.1 h6).resolve_left hne

@[expose] def swapSL : SL(3, K5) :=
  ⟨!![0, 0, -1; 0, 1, 0; 1, 0, 0], by simp [Matrix.det_fin_three]⟩

theorem dSL_sq (a b c : K5) (h : a * b * c = 1) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    dSL a b c h ^ 2 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_dSL, Matrix.SpecialLinearGroup.coe_one, pow_two,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

theorem locE3_five (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K5))) (hfs : D ≤ frameStab 3 K5) :
    LocE3 D.subtype := by
  have ht1 : (-1 : K5) * -1 * 1 = 1 := by decide
  refine ⟨⊤, ?_, LinearFlag.proj 3 K5 (dSL (-1) (-1) 1 ht1), ?_, ⟨1, ?_⟩, LinearFlag.proj 3 K5 swapSL, ?_⟩
  · have h := GenLocBasic.pRank_congr (Subgroup.topEquiv : (⊤ : Subgroup ↥D) ≃* ↥D)
    omega
  · rw [mem_fixedIn]
    rintro φ ⟨d, -, rfl⟩
    rcases D_cases D hfs d with ⟨u, hu⟩ | ⟨u, hu⟩
    · show (d : MulAut (LinearFlag.projectiveSL 3 K5)) _ = _
      rw [hu]
      exact fixed_dSL_of_diag u _ _ _ ht1
    · show (d : MulAut (LinearFlag.projectiveSL 3 K5)) _ = _
      rw [hu]
      exact fixed_dual_dSL u _ _ _ ht1 (by decide) (by decide) (by decide)
  · rw [pow_one, ← map_pow, dSL_sq _ _ _ ht1 (by decide) (by decide) (by decide), map_one]
  · intro h
    rw [← map_mul, ← map_mul] at h
    have h' := congrArg (fun x : SL(3, K5) => (x : Matrix (Fin 3) (Fin 3) K5) 0 2) (proj_injective h)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dSL, Matrix.mul_diagonal, Matrix.diagonal_mul] at h'
    have e : ((swapSL : SL(3, K5)) : Matrix (Fin 3) (Fin 3) K5) 0 2 = -1 := rfl
    rw [e] at h'
    revert h'
    decide

end GenLocL3Five

end CFSG.GH74.Generic.BProg.B2
