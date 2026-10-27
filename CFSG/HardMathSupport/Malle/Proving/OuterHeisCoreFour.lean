module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.SL3Closure
public import CFSG.LieType.SeitzGeneration.OutdiagHeis

public section

namespace CFSG.HardMathSupport.Malle.Proving

open Matrix CFSG.LieType.SeitzGeneration

section Roots

variable {F : Type} [Field F]

def ee01 (c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, c, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

def ee02 (c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, c; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

def ee10 (c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; c, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

def ee12 (c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 1, c; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

def ee20 (c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 1, 0; c, 0, 1], by simp [Matrix.det_fin_three]⟩

def ee21 (c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, c, 1], by simp [Matrix.det_fin_three]⟩

theorem eq_top_of_ee01 {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K)
    (hshift : (shiftSL : SpecialLinearGroup (Fin 3) F) ∈ K) {c : F} (hc : c ≠ 0)
    (hx : ee01 c ∈ K) : K = ⊤ := by
  have hall01 : ∀ s : F, ee01 s ∈ K := by
    intro s
    by_cases hs : s = 0
    · subst hs
      have h1 : ee01 (0 : F) = 1 := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ee01]
      rw [h1]
      exact K.one_mem
    · have hD : diagSL (s / c) 1 (s / c)⁻¹ (by field_simp) ∈ K := hdiag _ _ _ _
      have hD' : diagSL (s / c)⁻¹ 1 (s / c) (by field_simp) ∈ K := hdiag _ _ _ _
      have key : diagSL (s / c) 1 (s / c)⁻¹ (by field_simp) * ee01 c *
          diagSL (s / c)⁻¹ 1 (s / c) (by field_simp) = ee01 s := by
        ext i j
        simp only [Matrix.SpecialLinearGroup.coe_mul]
        fin_cases i <;> fin_cases j <;>
          simp [diagSL, ee01, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
      rw [← key]
      exact K.mul_mem (K.mul_mem hD hx) hD'
  have hS2 : (shiftSL * shiftSL : SpecialLinearGroup (Fin 3) F) ∈ K := K.mul_mem hshift hshift
  have hconj1 : ∀ s : F, ee12 s ∈ K := by
    intro s
    have e : ee12 s = shiftSL * ee01 s * (shiftSL * shiftSL) := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      fin_cases i <;> fin_cases j <;>
        simp [ee01, ee12, shiftSL, Matrix.mul_apply, Fin.sum_univ_three]
    rw [e]
    exact K.mul_mem (K.mul_mem hshift (hall01 s)) hS2
  have hconj2 : ∀ s : F, ee20 s ∈ K := by
    intro s
    have e : ee20 s = shiftSL * ee12 s * (shiftSL * shiftSL) := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      fin_cases i <;> fin_cases j <;>
        simp [ee12, ee20, shiftSL, Matrix.mul_apply, Fin.sum_univ_three]
    rw [e]
    exact K.mul_mem (K.mul_mem hshift (hconj1 s)) hS2
  have hc02 : ∀ s : F, ee02 s ∈ K := by
    intro s
    have e : ee02 s = ee01 s * ee12 1 * ee01 (-s) * ee12 (-1) := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      fin_cases i <;> fin_cases j <;>
        simp [ee01, ee02, ee12, Matrix.mul_apply, Fin.sum_univ_three]
    rw [e]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hall01 s) (hconj1 1)) (hall01 (-s))) (hconj1 (-1))
  have hc10 : ∀ s : F, ee10 s ∈ K := by
    intro s
    have e : ee10 s = ee12 s * ee20 1 * ee12 (-s) * ee20 (-1) := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      fin_cases i <;> fin_cases j <;>
        simp [ee10, ee12, ee20, Matrix.mul_apply, Fin.sum_univ_three]
    rw [e]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hconj1 s) (hconj2 1)) (hconj1 (-s))) (hconj2 (-1))
  have hc21 : ∀ s : F, ee21 s ∈ K := by
    intro s
    have e : ee21 s = ee20 s * ee01 1 * ee20 (-s) * ee01 (-1) := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      fin_cases i <;> fin_cases j <;>
        simp [ee01, ee20, ee21, Matrix.mul_apply, Fin.sum_univ_three]
    rw [e]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hconj2 s) (hall01 1)) (hconj2 (-s))) (hall01 (-1))
  refine CFSG.HardMathSupport.Malle.Coordinator.CoverThree.eq_top_of_transvections K ?_
  intro a b hab c
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · have e : SpecialLinearGroup.transvection hab c = ee01 c := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.transvection_coe, ee01]
    rw [e]; exact hall01 c
  · have e : SpecialLinearGroup.transvection hab c = ee02 c := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.transvection_coe, ee02]
    rw [e]; exact hc02 c
  · have e : SpecialLinearGroup.transvection hab c = ee10 c := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.transvection_coe, ee10]
    rw [e]; exact hc10 c
  · exact absurd rfl hab
  · have e : SpecialLinearGroup.transvection hab c = ee12 c := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.transvection_coe, ee12]
    rw [e]; exact hconj1 c
  · have e : SpecialLinearGroup.transvection hab c = ee20 c := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.transvection_coe, ee20]
    rw [e]; exact hconj2 c
  · have e : SpecialLinearGroup.transvection hab c = ee21 c := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.transvection_coe, ee21]
    rw [e]; exact hc21 c
  · exact absurd rfl hab

end Roots

def fourY1 {F : Type} [Field F] (α : F) : Matrix (Fin 3) (Fin 3) F :=
  !![α, 1, 1; α ^ 2, α, 1; α ^ 2, α ^ 2, α]

def fourY2i {F : Type} [Field F] (α : F) : Matrix (Fin 3) (Fin 3) F :=
  !![α, α, α ^ 2; α, α, α; 1, α, α]

theorem fourWord_matrix {F : Type} [Field F] (α : F) (hα2 : α ^ 2 = α + 1) (h2 : (2 : F) = 0) :
    fourY1 α * fourY1 α * (!![0, 0, 1; 1, 0, 0; 0, 1, 0] * !![0, 0, 1; 1, 0, 0; 0, 1, 0]) *
      fourY1 α * (!![0, 0, 1; 1, 0, 0; 0, 1, 0] * !![0, 0, 1; 1, 0, 0; 0, 1, 0]) *
      fourY2i α * !![0, 0, 1; 1, 0, 0; 0, 1, 0] = !![1, α, 0; 0, 1, 0; 0, 0, 1] := by
  simp only [fourY1, fourY2i, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | ring1
    | linear_combination ((43 : F) + (25 : F) * α + (13 : F) * α ^ 2 + (5 : F) * α ^ 3) * hα2 + ((21 : F) + (35 : F) * α) * h2
    | linear_combination ((50 : F) + (28 : F) * α + (18 : F) * α ^ 2 + (6 : F) * α ^ 3) * hα2 + ((25 : F) + (39 : F) * α) * h2
    | linear_combination ((35 : F) + (24 : F) * α + (8 : F) * α ^ 2 + (4 : F) * α ^ 3) * hα2 + ((18 : F) + (31 : F) * α) * h2
    | linear_combination ((60 : F) + (36 : F) * α + (20 : F) * α ^ 2 + (11 : F) * α ^ 3 + (2 : F) * α ^ 4) * hα2 + ((30 : F) + (48 : F) * α) * h2
    | linear_combination ((67 : F) + (43 : F) * α + (22 : F) * α ^ 2 + (16 : F) * α ^ 3 + (2 : F) * α ^ 4) * hα2 + ((33 : F) + (55 : F) * α) * h2
    | linear_combination ((52 : F) + (30 : F) * α + (19 : F) * α ^ 2 + (6 : F) * α ^ 3 + (2 : F) * α ^ 4) * hα2 + ((26 : F) + (42 : F) * α) * h2
    | linear_combination ((82 : F) + (52 : F) * α + (30 : F) * α ^ 2 + (16 : F) * α ^ 3 + (8 : F) * α ^ 4 + (1 : F) * α ^ 5) * hα2 + ((41 : F) + (67 : F) * α) * h2
    | linear_combination ((94 : F) + (58 : F) * α + (36 : F) * α ^ 2 + (19 : F) * α ^ 3 + (11 : F) * α ^ 4 + (1 : F) * α ^ 5) * hα2 + ((47 : F) + (76 : F) * α) * h2
    | linear_combination ((73 : F) + (43 : F) * α + (27 : F) * α ^ 2 + (13 : F) * α ^ 3 + (5 : F) * α ^ 4 + (1 : F) * α ^ 5) * hα2 + ((36 : F) + (58 : F) * α) * h2

theorem outerHeisCoreFour {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) (ω α : F)
    (hω : ω ^ 2 + ω + 1 = 0) (_hω1 : ω ≠ 1) (hα : α ≠ 0) (hαc : ¬ ∃ μ : F, μ ^ 3 = α) :
    Subgroup.closure (outerHeisSet ω α) = ⊤ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  have hα3 : α ^ 3 = 1 := by
    have h4 : α ^ Fintype.card F = α := FiniteField.pow_card α
    rw [hcard] at h4
    have hm : α * (α ^ 3 - 1) = 0 := by linear_combination h4
    exact sub_eq_zero.1 ((mul_eq_zero.1 hm).resolve_left hα)
  have hq : α ^ 2 + α + 1 = 0 := by
    have hα1 : α - 1 ≠ 0 := fun h => hαc ⟨1, by linear_combination (-1 : F) * h⟩
    have hm : (α - 1) * (α ^ 2 + α + 1) = 0 := by linear_combination hα3
    exact (mul_eq_zero.1 hm).resolve_left hα1
  have h2 : (2 : F) = 0 := by
    obtain ⟨p, hchar, n, hpp, hpn⟩ := FiniteField.card' F
    have : CharP F p := hchar
    have hp4 : p ∣ 4 := by
      rw [← hcard, hpn]
      exact dvd_pow_self p n.ne_zero
    have hp2 : p ∣ 2 := hpp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hp4)
    have hp : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 hp2
    subst hp
    exact_mod_cast CharP.cast_eq_zero F 2
  have hα2 : α ^ 2 = α + 1 := by linear_combination hq + (-α - 1) * h2
  set K : Subgroup (SpecialLinearGroup (Fin 3) F) := Subgroup.closure (outerHeisSet ω α) with hKdef
  have hK : FixSL (heisC α) ⊆ K := fun k hk => Subgroup.subset_closure (Or.inl (Or.inl (Or.inl hk)))
  have hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K := by
    intro a b d h
    refine Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ?_)))
    apply mem_FixSL_of_mul_comm
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisD, diagSL, Matrix.mul_apply, Matrix.diagonal_apply] <;> ring
  have hshift : (shiftSL : SpecialLinearGroup (Fin 3) F) ∈ K := by
    have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
    have hD : heisD ω = !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [heisD]
    refine Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨ω, ?_⟩)))
    show heisD ω * !![0, 0, 1; 1, 0, 0; 0, 1, 0] = ω • (!![0, 0, 1; 1, 0, 0; 0, 1, 0] * heisD ω)
    rw [hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first | ring1 | linear_combination (-1 : F) * hω3
  have hS2 : (shiftSL * shiftSL : SpecialLinearGroup (Fin 3) F) ∈ K := K.mul_mem hshift hshift
  have hdet1 : (fourY1 α).det = 1 := by
    simp [fourY1, Matrix.det_fin_three]
    linear_combination (1 - α + α ^ 2) * hα2
  have hdet2 : (fourY2i α).det = 1 := by
    simp [fourY2i, Matrix.det_fin_three]
    linear_combination (1 - α + α ^ 2) * hα2
  obtain ⟨Y1, hY1def⟩ : ∃ Y : SpecialLinearGroup (Fin 3) F, (Y : Matrix (Fin 3) (Fin 3) F) =
      fourY1 α := ⟨⟨fourY1 α, hdet1⟩, rfl⟩
  obtain ⟨Y2, hY2def⟩ : ∃ Y : SpecialLinearGroup (Fin 3) F, (Y : Matrix (Fin 3) (Fin 3) F) =
      fourY2i α := ⟨⟨fourY2i α, hdet2⟩, rfl⟩
  have hc1 : heisC α * (Y1 : Matrix (Fin 3) (Fin 3) F) =
      (Y1 : Matrix (Fin 3) (Fin 3) F) * heisC α := by
    rw [hY1def]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisC, fourY1, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
      | ring1
      | linear_combination (1 + α) * hα2 + α * h2
      | linear_combination (-1 - α) * hα2 + (-α) * h2
  have hc2 : heisC α * (Y2 : Matrix (Fin 3) (Fin 3) F) =
      (Y2 : Matrix (Fin 3) (Fin 3) F) * heisC α := by
    rw [hY2def]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisC, fourY2i, Matrix.mul_apply, Fin.sum_univ_three] <;> ring1
  have hY1K : Y1 ∈ K := hK (mem_FixSL_of_mul_comm hc1)
  have hY2K : Y2 ∈ K := hK (mem_FixSL_of_mul_comm hc2)
  have hword : Y1 * Y1 * (shiftSL * shiftSL) * Y1 * (shiftSL * shiftSL) * Y2 * shiftSL =
      ee01 α := by
    ext i j
    have hM := congrFun (congrFun (fourWord_matrix α hα2 h2) i) j
    simp only [Matrix.SpecialLinearGroup.coe_mul, hY1def, hY2def]
    exact hM
  have hx : ee01 α ∈ K := by
    rw [← hword]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hY1K hY1K) hS2) hY1K)
      hS2) hY2K) hshift
  exact eq_top_of_ee01 hdiag hshift hα hx

end CFSG.HardMathSupport.Malle.Proving
