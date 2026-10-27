module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Gen

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

open Matrix Matrix.SpecialLinearGroup

variable {k : Type} [Field k]

@[expose] def iotaMat (h : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 3) (Fin 3) k :=
  !![1, 0, 0; 0, h 0 0, h 0 1; 0, h 1 0, h 1 1]

theorem det_iotaMat (h : SpecialLinearGroup (Fin 2) k) :
    (iotaMat (h : Matrix (Fin 2) (Fin 2) k)).det = 1 := by
  have := h.2
  rw [det_fin_two] at this
  simp [iotaMat, det_fin_three]
  linear_combination this

@[expose] def iotaFun (h : SpecialLinearGroup (Fin 2) k) : SpecialLinearGroup (Fin 3) k :=
  ⟨iotaMat (h : Matrix (Fin 2) (Fin 2) k), det_iotaMat h⟩

theorem coe_iotaFun (h : SpecialLinearGroup (Fin 2) k) :
    ((iotaFun h : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      iotaMat (h : Matrix (Fin 2) (Fin 2) k) := rfl

@[expose] def iota : SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 3) k where
  toFun := iotaFun
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_iotaFun]
    fin_cases i <;> fin_cases j <;> simp [iotaMat]
  map_mul' h h' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_mul, coe_iotaFun, coe_iotaFun, coe_iotaFun]
    fin_cases i <;> fin_cases j <;>
      simp [iotaMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, coe_mul]

theorem coe_iota (h : SpecialLinearGroup (Fin 2) k) :
    ((iota h : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      iotaMat (h : Matrix (Fin 2) (Fin 2) k) := rfl

theorem iota_injective : Function.Injective (iota : SpecialLinearGroup (Fin 2) k →* _) := by
  intro h h' hh
  have := congrArg (fun g : SpecialLinearGroup (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k)) hh
  apply Subtype.ext
  ext i j
  have e := congrFun (congrFun this i.succ) j.succ
  fin_cases i <;> fin_cases j <;> simpa [coe_iota, iotaMat] using e

@[expose] def sl2x (c : k) : SpecialLinearGroup (Fin 2) k := ⟨!![1, c; 0, 1], by simp [det_fin_two]⟩

theorem iota_sl2x (c : k) : iota (sl2x c) = x12 c := by
  apply Subtype.ext
  rw [coe_iota, coe_x12]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [iotaMat, sl2x]

@[expose] def IsBlock (g : SpecialLinearGroup (Fin 3) k) : Prop :=
  (g : Matrix (Fin 3) (Fin 3) k) 0 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) k) 0 2 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) k) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) k) 2 0 = 0

theorem mem_range_iota_iff (g : SpecialLinearGroup (Fin 3) k) :
    g ∈ (iota : SpecialLinearGroup (Fin 2) k →* _).range ↔
      (g : Matrix (Fin 3) (Fin 3) k) 0 0 = 1 ∧ IsBlock g := by
  constructor
  · rintro ⟨h, rfl⟩
    simp [coe_iota, iotaMat, IsBlock]
  · rintro ⟨h00, h01, h02, h10, h20⟩
    have hdet := g.2
    rw [det_fin_three, h00, h01, h02, h10, h20] at hdet
    refine ⟨⟨!![(g : Matrix (Fin 3) (Fin 3) k) 1 1, (g : Matrix (Fin 3) (Fin 3) k) 1 2;
      (g : Matrix (Fin 3) (Fin 3) k) 2 1, (g : Matrix (Fin 3) (Fin 3) k) 2 2], ?_⟩, ?_⟩
    · rw [det_fin_two]
      simp
      linear_combination hdet
    · apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [iota, iotaFun, iotaMat, h00, h01, h02, h10, h20]

theorem isBlock_inv {g : SpecialLinearGroup (Fin 3) k} (hg : IsBlock g) : IsBlock g⁻¹ := by
  obtain ⟨h01, h02, h10, h20⟩ := hg
  rw [IsBlock, coe_inv, adjugate_fin_three]
  simp [h01, h02, h10, h20]

theorem conj_mem_range_iota {g : SpecialLinearGroup (Fin 3) k} (hg : IsBlock g)
    (h : SpecialLinearGroup (Fin 2) k) :
    g * iota h * g⁻¹ ∈ (iota : SpecialLinearGroup (Fin 2) k →* _).range := by
  rw [mem_range_iota_iff]
  have hi := isBlock_inv hg
  have hgg : g * g⁻¹ = 1 := mul_inv_cancel g
  generalize g⁻¹ = gi at hi hgg ⊢
  obtain ⟨h01, h02, h10, h20⟩ := hg
  obtain ⟨i01, i02, i10, i20⟩ := hi
  have hgg' : (g : Matrix (Fin 3) (Fin 3) k) * (gi : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← coe_mul, hgg, coe_one]
  have e00 := congrFun (congrFun hgg' 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, zero_mul, add_zero,
    Matrix.one_apply_eq] at e00
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [coe_mul, coe_mul] <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, coe_iota, iotaMat, h01, h02, h10, h20, i01, i02,
      i10, i20]
  linear_combination e00

@[expose] def Dm (ω : k) : Matrix (Fin 3) (Fin 3) k := !![ω, 0, 0; 0, 1, 0; 0, 0, 1]

theorem block_of_comm {ω : k} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) {g : SpecialLinearGroup (Fin 3) k}
    {c : k} (h : Dm ω * (g : Matrix (Fin 3) (Fin 3) k) = c • ((g : Matrix (Fin 3) (Fin 3) k) * Dm ω)) :
    c = 1 ∧ IsBlock g := by
  have e : ∀ i j, (Dm ω * (g : Matrix (Fin 3) (Fin 3) k)) i j =
      (c • ((g : Matrix (Fin 3) (Fin 3) k) * Dm ω)) i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e20 := e 2 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e21 := e 2 1
  have e22 := e 2 2
  simp [Dm, Matrix.mul_apply, Fin.sum_univ_three] at e00 e01 e02 e10 e20 e11 e12 e21 e22
  have hc : c = 1 := by
    by_contra hc
    have hc' : 1 - c ≠ 0 := fun h' => hc (by linear_combination -h')
    have g00 : (g : Matrix (Fin 3) (Fin 3) k) 0 0 = 0 := by
      have : (1 - c) * ω * (g : Matrix (Fin 3) (Fin 3) k) 0 0 = 0 := by linear_combination e00
      rcases mul_eq_zero.1 this with h1 | h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact absurd h2 hc'
        · exact absurd h2 hω0
      · exact h1
    have g11 : (g : Matrix (Fin 3) (Fin 3) k) 1 1 = 0 := by
      have : (1 - c) * (g : Matrix (Fin 3) (Fin 3) k) 1 1 = 0 := by linear_combination e11
      exact (mul_eq_zero.1 this).resolve_left hc'
    have g12 : (g : Matrix (Fin 3) (Fin 3) k) 1 2 = 0 := by
      have : (1 - c) * (g : Matrix (Fin 3) (Fin 3) k) 1 2 = 0 := by linear_combination e12
      exact (mul_eq_zero.1 this).resolve_left hc'
    have g21 : (g : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 := by
      have : (1 - c) * (g : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 := by linear_combination e21
      exact (mul_eq_zero.1 this).resolve_left hc'
    have g22 : (g : Matrix (Fin 3) (Fin 3) k) 2 2 = 0 := by
      have : (1 - c) * (g : Matrix (Fin 3) (Fin 3) k) 2 2 = 0 := by linear_combination e22
      exact (mul_eq_zero.1 this).resolve_left hc'
    have hd := g.2
    rw [det_fin_three, g00, g11, g12, g21, g22] at hd
    simp at hd
  subst hc
  have hω1' : ω - 1 ≠ 0 := fun h' => hω1 (by linear_combination h')
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · exact e01.resolve_left hω1
  · exact e02.resolve_left hω1
  · have : (1 - ω) * (g : Matrix (Fin 3) (Fin 3) k) 1 0 = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_left (fun h' => hω1' (by linear_combination -h'))
  · have : (1 - ω) * (g : Matrix (Fin 3) (Fin 3) k) 2 0 = 0 := by linear_combination e20
    exact (mul_eq_zero.1 this).resolve_left (fun h' => hω1' (by linear_combination -h'))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320
