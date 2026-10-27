module

public import CFSG.ClassicalInvolution.Q3.TL4MF163U3A
public import CFSG.ClassicalInvolution.Q3.TL4MF163LUM

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.U3

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p f : ℕ} {K : Type} [Field K]

theorem mat_of_conj {A Y Z : GL (Fin 3) K} {c : Kˣ}
    (hc : A * Y * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * Z) :
    (A : Matrix (Fin 3) (Fin 3) K) * (Y : Matrix (Fin 3) (Fin 3) K) *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (c : K) • (Z : Matrix (Fin 3) (Fin 3) K)
      ∧ (A : Matrix (Fin 3) (Fin 3) K) * (Y : Matrix (Fin 3) (Fin 3) K) =
        (c : K) • ((Z : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) := by
  have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
  have h2 : A * Y = GeneralLinearGroup.scalar (Fin 3) c * Z * A := by rw [← hc]; group
  have h3 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h2
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1 h3
  refine ⟨by rw [h1, ← Matrix.smul_eq_diagonal_mul], ?_⟩
  rw [h3, Matrix.mul_assoc, ← Matrix.smul_eq_diagonal_mul]

variable (h : UnitaryFieldData p f K)

theorem sigma_form (hq : 2 < p ^ f) {s : MulAut (unitaryPSU h 3)} {z₀ : unitarySU p f K 3}
    (hs2 : s * s = MulAut.conj (z₀ : unitaryPSU h 3))
    (hni : ∀ g : unitarySU p f K 3, s ≠ MulAut.conj (g : unitaryPSU h 3))
    {x : K} (hxu : h.bar x * x = 1) (hx2 : x ^ 2 ≠ 1) (hx3 : x ^ 3 ≠ 1)
    {dx w₀ : unitarySU p f K 3}
    (hdx : ((dx : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![x, x⁻¹, 1])
    (hw₀ : ((w₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; -1, 0, 0; 0, 0, 1])
    (hfx : s (dx : unitaryPSU h 3) = dx) (hfw : s (w₀ : unitaryPSU h 3) = w₀) :
    ∃ (M : unitaryIsom3 h) (m m' : K), s = psuConj h M * psuField h (barE h) ∧
      ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, m, 0; -m, 0, 0; 0, 0, m'] := by
  obtain ⟨M, τ, hs⟩ := exists_psuConj_mul_psuField (h := h) hq s
  have hτ : τ * τ = 1 := by
    rw [conj_mk_eq_psuConj, hs] at hs2
    exact field_mul_self_eq_one h hs2
  rcases eq_one_or_barE h hτ with rfl | rfl
  · exfalso
    rw [map_one, mul_one] at hs
    rw [hs] at hs2 hni
    obtain ⟨g', hg'⟩ := exists_eq_conj_of_sq h hs2
    exact hni g' hg'
  refine ⟨M, ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1,
    ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2, hs, ?_⟩
  rw [hs] at hfx hfw
  have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hxu
  have hbx : h.bar x = x⁻¹ := eq_inv_of_mul_eq_one_left hxu
  have hbxi : h.bar x⁻¹ = x := by rw [map_inv₀, hbx, inv_inv]
  obtain ⟨c₁, -, -, hc₁⟩ := exists_scalar_of_fix h hfx
  obtain ⟨hT₁, hE₁⟩ := mat_of_conj hc₁
  have hD' : ((glAut (barE h) (dx : GL (Fin 3) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![x⁻¹, x, 1] := by
    rw [coe_glAut, hdx, Matrix.diagonal_map (map_zero _)]
    congr 1
    ext i
    fin_cases i <;> simp [barE_apply, hbx]
  rw [hD', hdx] at hT₁ hE₁
  have htr := (MF163.trace_eq_of_conj hT₁).1
  simp only [trace_diagonal, Fin.sum_univ_three] at htr
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at htr
  have hs1 : x⁻¹ + x + 1 ≠ 0 := by
    intro h0
    apply hx3
    have h1 : x ^ 3 - 1 = (x - 1) * x * (x⁻¹ + x + 1) := by field_simp; ring
    rw [h0, mul_zero] at h1
    exact sub_eq_zero.mp h1
  have hc1 : (c₁ : K) = 1 := by
    have h1 : ((c₁ : K) - 1) * (x⁻¹ + x + 1) = 0 := by linear_combination -htr
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hs1)
  rw [hc1, one_smul] at hE₁
  obtain ⟨c₂, -, -, hc₂⟩ := exists_scalar_of_fix h hfw
  obtain ⟨hT₂, hE₂⟩ := mat_of_conj hc₂
  have hW' : ((glAut (barE h) (w₀ : GL (Fin 3) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
    rw [coe_glAut, hw₀]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [barE_apply]
  rw [hW', hw₀] at hT₂ hE₂
  have htr₂ := (MF163.trace_eq_of_conj hT₂).1
  simp [Matrix.trace_fin_three] at htr₂
  rw [← htr₂, one_smul] at hE₂
  set A := ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hA
  have e₁ := fun i j => congrFun (congrFun hE₁ i) j
  have e₂ := fun i j => congrFun (congrFun hE₂ i) j
  simp only [mul_diagonal, diagonal_mul] at e₁
  have hx1 : x - 1 ≠ 0 := fun h0 => hx2 (by rw [sub_eq_zero.mp h0]; norm_num)
  have hxx : x - x⁻¹ ≠ 0 := fun h0 => hx2 (by
    have := sub_eq_zero.mp h0
    field_simp at this
    linear_combination this)
  have hxi1 : x⁻¹ - 1 ≠ 0 := fun h0 => hx1 (by
    have := sub_eq_zero.mp h0
    rw [inv_eq_one] at this
    rw [this, sub_self])
  have hxx' : x⁻¹ - x ≠ 0 := fun h0 => hxx (by linear_combination -h0)
  have hx1' : 1 - x ≠ 0 := fun h0 => hx1 (by linear_combination -h0)
  have hxi1' : 1 - x⁻¹ ≠ 0 := fun h0 => hxi1 (by linear_combination -h0)
  have z00 : A 0 0 = 0 := by
    have := e₁ 0 0
    simp at this
    exact (mul_eq_zero.mp (by linear_combination this : A 0 0 * (x⁻¹ - x) = 0)).resolve_right
      hxx'
  have z02 : A 0 2 = 0 := by
    have := e₁ 0 2
    simp at this
    exact (mul_eq_zero.mp (by linear_combination this : A 0 2 * (1 - x) = 0)).resolve_right hx1'
  have z11 : A 1 1 = 0 := by
    have := e₁ 1 1
    simp at this
    exact (mul_eq_zero.mp (by linear_combination this : A 1 1 * (x - x⁻¹) = 0)).resolve_right hxx
  have z12 : A 1 2 = 0 := by
    have := e₁ 1 2
    simp at this
    exact (mul_eq_zero.mp (by linear_combination this : A 1 2 * (1 - x⁻¹) = 0)).resolve_right
      hxi1'
  have z20 : A 2 0 = 0 := by
    have := e₁ 2 0
    simp at this
    exact (mul_eq_zero.mp (by linear_combination this : A 2 0 * (x⁻¹ - 1) = 0)).resolve_right
      hxi1
  have z21 : A 2 1 = 0 := by
    have := e₁ 2 1
    simp at this
    exact (mul_eq_zero.mp (by linear_combination this : A 2 1 * (x - 1) = 0)).resolve_right hx1
  have h10 : A 1 0 = -A 0 1 := by
    have := e₂ 0 0
    simp [Matrix.mul_apply, Fin.sum_univ_three] at this
    linear_combination -this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [z00, z02, z11, z12, z20, z21, h10]

end CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
