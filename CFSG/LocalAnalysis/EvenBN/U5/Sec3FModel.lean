module

public import CFSG.LocalAnalysis.EvenBN.U5.Model
public import CFSG.RankThree.CentralLiftU.UnitaryTorus

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem lev_congr {A B : Matrix (Fin 2) (Fin 2) K} (e : A = B) (hA : IsUnit A.det)
    (hB : IsUnit B.det) : lev (hK := h) A hA = lev (hK := h) B hB := by
  subst e
  rfl

theorem lev_mul (A B : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) (hB : IsUnit B.det) :
    lev (hK := h) (A * B) (by rw [det_mul]; exact hA.mul hB) =
      lev (hK := h) A hA * lev (hK := h) B hB := by
  apply mat_injective
  rw [mat_mul, mat_lev, mat_lev, mat_lev, oddDiag_mul, det_mul, map_mul, mul_div_mul_comm]

theorem lev_one : lev (hK := h) (1 : Matrix (Fin 2) (Fin 2) K) (by simp) = 1 := by
  apply mat_injective
  rw [mat_lev, mat_one, det_one, map_one, div_one, oddDiag_one]

theorem lev_inv (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    (lev (hK := h) A hA)⁻¹ = lev (hK := h) A⁻¹ (by rw [det_nonsing_inv]; exact hA.ringInverse) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← lev_mul, lev_congr (mul_nonsing_inv A hA) _ (by simp), lev_one]

theorem lev_eq_leviSU (A : SpecialLinearGroup (Fin 2) K)
    (hA : IsUnit (A : Matrix (Fin 2) (Fin 2) K).det) :
    lev (hK := h) (A : Matrix (Fin 2) (Fin 2) K) hA = UnitaryHigher.leviSU h 1 A := by
  apply mat_injective
  have key := UnitaryHigher.bar_map_mul_inv h (SpecialLinearGroup.toGL A)
  rw [SpecialLinearGroup.coe_GL_coe_matrix] at key
  have hd : barInvT h (A : Matrix (Fin 2) (Fin 2) K) =
      UnitaryHigher.leviDual h (SpecialLinearGroup.toGL A) := by
    rw [barInvT, transpose_nonsing_inv]
    exact inv_eq_right_inv key
  rw [mat_lev, mat_leviSU, oddDiag, Matrix.SpecialLinearGroup.det_coe, map_one, div_one, hd]
  congr 1
  ext i j
  fin_cases i
  fin_cases j
  rfl

theorem lev_conj_mem_N₁sub (B : Matrix (Fin 2) (Fin 2) K) (hB : IsUnit B.det) {n : hypSU h 2 1}
    (hn : n ∈ N₁sub h) : lev (hK := h) B hB * n * (lev (hK := h) B hB)⁻¹ ∈ N₁sub h := by
  obtain ⟨A, rfl⟩ := hn
  have hA : IsUnit (A : Matrix (Fin 2) (Fin 2) K).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one
  have hdet : (B * (A : Matrix (Fin 2) (Fin 2) K) * B⁻¹).det = 1 := by
    rw [det_mul, det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one, ← det_mul,
      mul_nonsing_inv B hB, det_one]
  refine ⟨⟨B * A * B⁻¹, hdet⟩, ?_⟩
  rw [← lev_eq_leviSU (⟨B * (A : Matrix (Fin 2) (Fin 2) K) * B⁻¹, hdet⟩ :
      SpecialLinearGroup (Fin 2) K)
    (by change IsUnit (B * (A : Matrix (Fin 2) (Fin 2) K) * B⁻¹).det; rw [hdet]; exact isUnit_one),
    ← lev_eq_leviSU A hA, lev_inv,
    ← lev_mul, ← lev_mul]

theorem isUnit_det_diag {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsUnit (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) K).det := by
  rw [det_fin_two_of]
  simp [ha, hb]

theorem barInvT_diag {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    barInvT h (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) K) =
      !![(h.bar a)⁻¹, 0; 0, (h.bar b)⁻¹] := by
  have ha' : h.bar a ≠ 0 := (map_ne_zero h.bar).2 ha
  have hb' : h.bar b ≠ 0 := (map_ne_zero h.bar).2 hb
  have em : (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) K).map h.bar = !![h.bar a, 0; 0, h.bar b] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e : ((!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) K).map h.bar)⁻¹ =
      !![(h.bar a)⁻¹, 0; 0, (h.bar b)⁻¹] := by
    refine inv_eq_right_inv ?_
    rw [em]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha', hb']
  rw [barInvT, e]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mat_lev_diag {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    mat (lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb)) =
      blk3 !![a, 0; 0, b] 0 0 (of fun _ _ => h.bar (a * b) / (a * b)) 0
        !![(h.bar a)⁻¹, 0; 0, (h.bar b)⁻¹] := by
  rw [mat_lev, oddDiag, barInvT_diag ha hb, det_fin_two_of, mul_zero, sub_zero]

theorem lev_diag {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb) ∈ Isub h ∧
      mat (lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb)) ιe₁ ιe₁ = a ∧
      mat (lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb)) ιe₂ ιe₂ = b ∧
      mat (lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb)) ιf₁ ιf₁ = (h.bar a)⁻¹ ∧
      mat (lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb)) ιf₂ ιf₂ = (h.bar b)⁻¹ := by
  refine ⟨CFSG.RankThree.CentralLiftU.mem_hypTorus_of_diag h
    (q := fun c => mat (lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb)) c c) ?_, ?_, ?_,
    ?_, ?_⟩
  · change mat _ = _
    rw [mat_lev_diag ha hb]
    ext c c'
    rcases c with i | k | i <;> rcases c' with j | l | j <;> (try fin_cases i) <;>
      (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;> simp
  all_goals rw [mat_lev_diag ha hb]; simp

theorem lev_diag_mem_I₃sub {a : K} (ha : a ≠ 0) :
    lev (hK := h) !![1, 0; 0, a] (isUnit_det_diag one_ne_zero ha) ∈ I₃sub h := by
  obtain ⟨hI, h1, -, h3, -⟩ := lev_diag (h := h) one_ne_zero ha
  rw [mem_I₃sub]
  exact ⟨hI, by rw [h1, h3, map_one, inv_one]⟩

theorem rSU_conj_lev_diag {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    rSU h * lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb) * (rSU h)⁻¹ =
      lev (hK := h) !![b, 0; 0, a] (isUnit_det_diag hb ha) := by
  have hs : IsUnit (swapM : Matrix (Fin 2) (Fin 2) K).det := by rw [det_swapM h]; exact isUnit_one
  have hr : rSU h = lev (hK := h) swapM hs := by
    rw [rSU_eq_leviSU, ← lev_eq_leviSU (swapSL h) hs]
    rfl
  rw [hr, lev_inv, ← lev_mul, ← lev_mul]
  apply lev_congr
  rw [inv_eq_right_inv swapM_mul_swapM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM]

theorem exists_lev_eq_mul (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    ∃ n ∈ N₁sub h, lev (hK := h) A hA =
      n * lev (hK := h) !![A.det, 0; 0, 1] (isUnit_det_diag hA.ne_zero one_ne_zero) := by
  have hδ := hA.ne_zero
  set D' : Matrix (Fin 2) (Fin 2) K := !![A.det⁻¹, 0; 0, 1] with hD'
  have hdet : (A * D').det = 1 := by
    rw [det_mul, hD', det_fin_two_of]
    simp [hδ]
  have hD'u : IsUnit D'.det := isUnit_det_diag (inv_ne_zero hδ) one_ne_zero
  refine ⟨UnitaryHigher.leviSU h 1 ⟨A * D', hdet⟩, ⟨_, rfl⟩, ?_⟩
  rw [← lev_eq_leviSU ⟨A * D', hdet⟩ (by rw [hdet]; exact isUnit_one)]
  have e : A = (A * D') * !![A.det, 0; 0, 1] := by
    rw [Matrix.mul_assoc, hD']
    have : (!![A.det⁻¹, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![A.det, 0; 0, 1] = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hδ]
    rw [this, Matrix.mul_one]
  rw [lev_congr e hA (by rw [← e]; exact hA)]
  exact lev_mul _ _ _ _

theorem isUnit_det_upper (x : K) : IsUnit (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) K).det := by
  rw [det_fin_two_of]
  simp

theorem lev_upper_mem_U (x : K) :
    lev (hK := h) !![1, x; 0, 1] (isUnit_det_upper x) ∈ hypUnitriangular h 2 1 := by
  have hU : IsUnitriangular (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) K) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> rfl
  obtain ⟨g, hgU, hg⟩ := (exists_mem_hypUnitriangular_odd_iff (h := h)
    (mat (lev (hK := h) !![1, x; 0, 1] (isUnit_det_upper x)))).2
    ⟨!![1, x; 0, 1], 0, 0, hU, by simp, by
      rw [oddUni_zero, Matrix.mul_one, mat_lev, det_fin_two_of]
      simp⟩
  have e : g = lev (hK := h) !![1, x; 0, 1] (isUnit_det_upper x) := mat_injective hg
  exact e ▸ hgU

theorem bruhat_matrix {a b c d : K} (hdet : a * d - b * c = 1) (hc : c ≠ 0) (h2 : (2 : K) = 0) :
    !![a, b; c, d] = !![1, a / c; 0, 1] * swapM * !![1, d * c; 0, 1] * !![c, 0; 0, c⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
  · field_simp
    linear_combination (-1 : K) * hdet - h2
  · field_simp

theorem upper_matrix {a b d : K} (hdet : a * d = 1) :
    !![a, b; 0, d] = !![1, a * b; 0, 1] * !![a, 0; 0, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (-b) * hdet

theorem leviSU_bruhat (A : SpecialLinearGroup (Fin 2) K) :
    (∃ p ∈ hypUnitriangular h 2 1, ∃ j ∈ Isub h, UnitaryHigher.leviSU h 1 A = p * j) ∨
      ∃ p ∈ hypUnitriangular h 2 1, ∃ p' ∈ hypUnitriangular h 2 1, ∃ j ∈ Isub h,
        UnitaryHigher.leviSU h 1 A = p * rSU h * p' * j := by
  have := h.charP
  have hA : IsUnit (A : Matrix (Fin 2) (Fin 2) K).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one
  have hdet := A.det_coe
  rw [det_fin_two] at hdet
  rw [← lev_eq_leviSU A hA]
  have hA2 := Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) K)
  by_cases hc : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · left
    have hd' : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
      rw [hc, mul_zero, sub_zero] at hdet
      exact hdet
    have ha : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hd'
    have hd : (A : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hd'
    have e1 : !![(A : Matrix (Fin 2) (Fin 2) K) 0 0, (A : Matrix (Fin 2) (Fin 2) K) 0 1;
        (A : Matrix (Fin 2) (Fin 2) K) 1 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1] =
        !![(A : Matrix (Fin 2) (Fin 2) K) 0 0, (A : Matrix (Fin 2) (Fin 2) K) 0 1;
          0, (A : Matrix (Fin 2) (Fin 2) K) 1 1] := by rw [hc]
    have e := hA2.trans (e1.trans (upper_matrix hd'))
    refine ⟨_, lev_upper_mem_U (h := h) ((A : Matrix (Fin 2) (Fin 2) K) 0 0 *
      (A : Matrix (Fin 2) (Fin 2) K) 0 1), _, (lev_diag (h := h) ha hd).1, ?_⟩
    rw [lev_congr e hA (by rw [← e]; exact hA)]
    exact lev_mul _ _ _ _
  · right
    have e := hA2.trans (bruhat_matrix hdet hc CharTwo.two_eq_zero)
    have hs : IsUnit (swapM : Matrix (Fin 2) (Fin 2) K).det := by
      rw [det_swapM h]; exact isUnit_one
    have hr : rSU h = lev (hK := h) swapM hs := by
      rw [rSU_eq_leviSU, ← lev_eq_leviSU (swapSL h) hs]
      rfl
    have hu₁ := isUnit_det_upper (K := K) ((A : Matrix (Fin 2) (Fin 2) K) 0 0 /
      (A : Matrix (Fin 2) (Fin 2) K) 1 0)
    have hu₂ := isUnit_det_upper (K := K) ((A : Matrix (Fin 2) (Fin 2) K) 1 1 *
      (A : Matrix (Fin 2) (Fin 2) K) 1 0)
    have hD := isUnit_det_diag hc (inv_ne_zero hc)
    have h1 : IsUnit (!![1, (A : Matrix (Fin 2) (Fin 2) K) 0 0 / (A : Matrix (Fin 2) (Fin 2) K) 1 0;
        0, 1] * swapM).det := by rw [det_mul]; exact hu₁.mul hs
    have h12 : IsUnit (!![1, (A : Matrix (Fin 2) (Fin 2) K) 0 0 /
        (A : Matrix (Fin 2) (Fin 2) K) 1 0; 0, 1] * swapM *
        !![1, (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0;
          0, 1]).det := by rw [det_mul]; exact h1.mul hu₂
    refine ⟨_, lev_upper_mem_U (h := h) ((A : Matrix (Fin 2) (Fin 2) K) 0 0 /
      (A : Matrix (Fin 2) (Fin 2) K) 1 0), _, lev_upper_mem_U (h := h)
      ((A : Matrix (Fin 2) (Fin 2) K) 1 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0), _,
      (lev_diag (h := h) hc (inv_ne_zero hc)).1, ?_⟩
    rw [lev_congr e hA (by rw [← e]; exact hA), lev_mul _ _ h12 hD, lev_mul _ _ h1 hu₂,
      lev_mul _ _ hu₁ hs, hr]

theorem Yof_mul {g g' : hypSU h 2 1} (hg : g ∈ Vsub h) (hg' : g' ∈ Vsub h) :
    Yof (g * g') = Yof g + Yof g' := by
  obtain ⟨-, Y, hY⟩ := hg
  obtain ⟨-, Y', hY'⟩ := hg'
  have e : mat (g * g') = oddUni h 0 (Y + Y') := by
    rw [mat_mul, hY, hY', oddUni_mul]
    simp
  rw [Yof_eq hY, Yof_eq hY', Yof_eq e]

theorem exists_norm_one_ne_one (h : UnitaryFieldData 2 f K) :
    ∃ ζ : K, ζ ≠ 0 ∧ h.bar ζ * ζ = 1 ∧ ζ ≠ 1 := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hc0 : c ≠ 0 := fun e => hc (by rw [e, map_zero])
  have hb0 : h.bar c ≠ 0 := (map_ne_zero h.bar).2 hc0
  refine ⟨c / h.bar c, div_ne_zero hc0 hb0, ?_, fun e => hc ?_⟩
  · rw [map_div₀, h.bar_bar]
    field_simp
  · rw [div_eq_one_iff_eq hb0] at e
    exact e.symm

end CFSG.LocalAnalysis.EvenBN.U5
