module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix CFSG.RankThree.PartOne.CTP

variable {K : Type} [Field K]

@[expose] def IsCocycle (κ : SpecialLinearGroup (Fin 2) K → Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ a b, κ (a * b) = κ a + (a : Matrix (Fin 2) (Fin 2) K) * κ b

@[expose] def torus2 (ν : K) (hν : ν ≠ 0) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![ν, 0; 0, ν⁻¹], by simp [Matrix.det_fin_two, hν]⟩

theorem torus2_mul_u2_mul_inv {ν : K} (hν : ν ≠ 0) (t : K) :
    torus2 ν hν * u2 t * (torus2 ν hν)⁻¹ = u2 (ν * ν * t) := by
  have hcoe : ((torus2 ν hν : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = !![ν, 0; 0, ν⁻¹] := rfl
  have hinv : (((torus2 ν hν)⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = !![ν⁻¹, 0; 0, ν] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hcoe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, hcoe]
  simp only [u2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hν] <;>
    (try field_simp) <;> (try ring)

variable {κ : SpecialLinearGroup (Fin 2) K → Matrix (Fin 2) (Fin 2) K}

theorem IsCocycle.map_one (hκ : IsCocycle κ) : κ 1 = 0 := by
  have h := hκ 1 1
  simp only [mul_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] at h
  simpa using h

theorem IsCocycle.map_inv (hκ : IsCocycle κ) (a : SpecialLinearGroup (Fin 2) K) :
    κ a⁻¹ = -(((a⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * κ a) := by
  have h := hκ a a⁻¹
  rw [mul_inv_cancel, hκ.map_one] at h
  have h2 : (a : Matrix (Fin 2) (Fin 2) K) * κ a⁻¹ = -κ a := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h.symm
  have hinv1 : ((a⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      * (a : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc κ a⁻¹
      = (((a⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * (a : Matrix (Fin 2) (Fin 2) K)) * κ a⁻¹ := by rw [hinv1, Matrix.one_mul]
    _ = ((a⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * ((a : Matrix (Fin 2) (Fin 2) K) * κ a⁻¹) := Matrix.mul_assoc _ _ _
    _ = -(((a⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * κ a) := by
        rw [h2, Matrix.mul_neg]

theorem IsCocycle.map_u2_add (hκ : IsCocycle κ) (t t' : K) :
    κ (u2 (t + t')) = κ (u2 t) + κ (u2 t') +
      !![t * κ (u2 t') 1 0, t * κ (u2 t') 1 1; 0, 0] := by
  rw [u2_add, hκ (u2 t) (u2 t'), u2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem IsCocycle.u2_second_row (hκ : IsCocycle κ) (h1 : κ (u2 1) = 0) (t : K) :
    κ (u2 t) 1 0 = 0 ∧ κ (u2 t) 1 1 = 0 := by
  have e1 := hκ.map_u2_add t 1
  have e2 := hκ.map_u2_add 1 t
  rw [add_comm t 1] at e1
  have key := e1.symm.trans e2
  rw [h1] at key
  have h00 := congrArg (fun X : Matrix (Fin 2) (Fin 2) K => X 0 0) key
  have h01 := congrArg (fun X : Matrix (Fin 2) (Fin 2) K => X 0 1) key
  simp at h00 h01
  constructor
  · first | exact h00 | exact h00.symm | linear_combination h00 | linear_combination -h00
  · first | exact h01 | exact h01.symm | linear_combination h01 | linear_combination -h01

private theorem twist_u2_mul_left (r : K) (X : Matrix (Fin 2) (Fin 2) K) :
    (u2 r : Matrix (Fin 2) (Fin 2) K) * X = X + !![r * X 1 0, r * X 1 1; 0, 0] := by
  rw [u2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

private theorem twist_torus_mul_row (ν : K) (hν : ν ≠ 0) (c : Matrix (Fin 2) (Fin 2) K)
    (h10 : c 1 0 = 0) (h11 : c 1 1 = 0) :
    ((torus2 ν hν : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * c = ν • c := by
  have hcoe : ((torus2 ν hν : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = !![ν, 0; 0, ν⁻¹] := rfl
  rw [hcoe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h10, h11]

private theorem twist_gen (hκ : IsCocycle κ) {ν : K} (hν : ν ≠ 0) (s : K) :
    κ (u2 (ν * ν * s)) = κ (torus2 ν hν)
      + ((torus2 ν hν : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * κ (u2 s)
      + -(((u2 (ν * ν * s) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * κ (torus2 ν hν)) := by
  have A1 := hκ (torus2 ν hν) (u2 s * (torus2 ν hν)⁻¹)
  have A2 := hκ (u2 s) (torus2 ν hν)⁻¹
  have A3 := hκ.map_inv (torus2 ν hν)
  have A4 : torus2 ν hν * (u2 s * (torus2 ν hν)⁻¹) = u2 (ν * ν * s) := by
    rw [← mul_assoc, torus2_mul_u2_mul_inv hν s]
  have A5 := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) A4
  simp only [Matrix.SpecialLinearGroup.coe_mul] at A5
  rw [A4, A2, A3] at A1
  rw [A1, ← A5]
  simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.mul_assoc]
  abel

theorem IsCocycle.torus_formula [CharP K 2] (hκ : IsCocycle κ) (h1 : κ (u2 1) = 0) {ν : K}
    (hν : ν ≠ 0) (t : K) :
    κ (u2 (ν * ν * t)) = ν • κ (u2 t) + t • κ (u2 (ν * ν)) := by
  have e_t := twist_gen hκ hν t
  have e_1 := twist_gen hκ hν 1
  rw [mul_one, h1, Matrix.mul_zero, add_zero] at e_1
  have hr := hκ.u2_second_row h1 t
  rw [e_t, twist_u2_mul_left (ν * ν * t) (κ (torus2 ν hν)),
    twist_torus_mul_row ν hν (κ (u2 t)) hr.1 hr.2, e_1,
    twist_u2_mul_left (ν * ν) (κ (torus2 ν hν))]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem IsCocycle.u2_eq_sqrt_form [Finite K] [CharP K 2] (hκ : IsCocycle κ) (h1 : κ (u2 1) = 0)
    {s₀ : K} (hs₀0 : s₀ ≠ 0) (hs₀1 : s₀ ≠ 1) :
    ∃ a : Matrix (Fin 2) (Fin 2) K, ∀ t r : K, r * r = t → κ (u2 t) = (t + r) • a := by
  obtain ⟨r₀, hr₀⟩ := isSquare_of_charTwo' s₀
  have hr₀0 : r₀ ≠ 0 := by
    rintro rfl
    exact hs₀0 (by rw [hr₀, mul_zero])
  have hsum : s₀ + r₀ ≠ 0 := by
    intro h
    have hsr : s₀ = r₀ := by linear_combination h - CharTwo.add_self_eq_zero r₀
    have hr1 : r₀ = 1 := mul_left_cancel₀ hr₀0 (by rw [mul_one, ← hr₀]; exact hsr)
    exact hs₀1 (hsr.trans hr1)
  refine ⟨(s₀ + r₀)⁻¹ • κ (u2 s₀), ?_⟩
  intro t r hrt
  subst hrt
  by_cases hr : r = 0
  · subst hr
    simp [u2_zero, hκ.map_one]
  · have E1 := torus_formula hκ h1 hr₀0 (r * r)
    have E2 := torus_formula hκ h1 hr s₀
    have hargs : r₀ * r₀ * (r * r) = r * r * s₀ := by rw [← hr₀]; ring
    rw [hargs, ← hr₀] at E1
    have key := E1.symm.trans E2
    have hz1 : (s₀ + s₀) • κ (u2 (r * r)) = 0 := by
      rw [CharTwo.add_self_eq_zero, zero_smul]
    have hz2 : (r * r + r * r) • κ (u2 s₀) = 0 := by
      rw [CharTwo.add_self_eq_zero, zero_smul]
    have hG : (s₀ + r₀) • κ (u2 (r * r)) = (r * r + r) • κ (u2 s₀) := by
      linear_combination (norm := module) key + hz1 - hz2
    calc κ (u2 (r * r))
        = (s₀ + r₀)⁻¹ • ((s₀ + r₀) • κ (u2 (r * r))) := by
          rw [smul_smul, inv_mul_cancel₀ hsum, one_smul]
      _ = (s₀ + r₀)⁻¹ • ((r * r + r) • κ (u2 s₀)) := by rw [hG]
      _ = (r * r + r) • ((s₀ + r₀)⁻¹ • κ (u2 s₀)) := by
          rw [smul_smul, smul_smul]
          congr 1
          ring

theorem no_cocycle [Finite K] [CharP K 2] (hs : ∃ s : K, s ≠ 0 ∧ s ≠ 1) (hκ : IsCocycle κ)
    (h1 : κ (u2 1) = 0) (α β : K) (hβ : κ (u2 β) = !![1, 0; 0, 0])
    (hα : κ (u2 α) = !![0, 1; 0, 0]) : False := by
  obtain ⟨s₀, hs₀0, hs₀1⟩ := hs
  obtain ⟨a, ha⟩ := hκ.u2_eq_sqrt_form h1 hs₀0 hs₀1
  obtain ⟨ρ, hρ⟩ := isSquare_of_charTwo' β
  obtain ⟨ρ', hρ'⟩ := isSquare_of_charTwo' α
  have hb := ha β ρ hρ.symm
  have hα' := ha α ρ' hρ'.symm
  rw [hβ] at hb
  rw [hα] at hα'
  have e00 : (β + ρ) * a 0 0 = 1 :=
    congrArg (fun X : Matrix (Fin 2) (Fin 2) K => X 0 0) hb.symm
  have f00 : (α + ρ') * a 0 0 = 0 :=
    congrArg (fun X : Matrix (Fin 2) (Fin 2) K => X 0 0) hα'.symm
  have f01 : (α + ρ') * a 0 1 = 1 :=
    congrArg (fun X : Matrix (Fin 2) (Fin 2) K => X 0 1) hα'.symm
  have hq : α + ρ' = 0 := by
    linear_combination (β + ρ) * f00 - (α + ρ') * e00
  have hfin : (1 : K) = 0 := by
    linear_combination -f01 + a 0 1 * hq
  exact one_ne_zero hfin

end CFSG.LieType.SeitzGeneration.OmegaF2
