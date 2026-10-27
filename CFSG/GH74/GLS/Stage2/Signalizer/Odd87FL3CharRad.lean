module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharInv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Elations

variable {F : Type} [Field F]

@[expose] def elP (a b : F) : SL(3, F) :=
  ⟨!![1, 0, 0; 0, 1, 0; a, b, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def elM (a b : F) : SL(3, F) :=
  ⟨!![1, 0, a; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_elP (a b : F) :
    ((elP a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 1, 0; a, b, 1] := rfl

theorem coe_elM (a b : F) :
    ((elM a b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, a; 0, 1, b; 0, 0, 1] := rfl

theorem elP_zero : (elP 0 0 : SL(3, F)) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_elP]

theorem elM_zero : (elM 0 0 : SL(3, F)) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_elM]

theorem elP_mul (a b a' b' : F) : elP a b * elP a' b' = elP (a + a') (b + b') := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_elP, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem elM_mul (a b a' b' : F) : elM a b * elM a' b' = elM (a + a') (b + b') := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_elM, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

@[expose] def elPHom (F : Type) [Field F] : Multiplicative (F × F) →* SL(3, F) where
  toFun w := elP (Multiplicative.toAdd w).1 (Multiplicative.toAdd w).2
  map_one' := elP_zero
  map_mul' w w' := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    exact (elP_mul _ _ _ _).symm

@[expose] def elMHom (F : Type) [Field F] : Multiplicative (F × F) →* SL(3, F) where
  toFun w := elM (Multiplicative.toAdd w).1 (Multiplicative.toAdd w).2
  map_one' := elM_zero
  map_mul' w w' := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    exact (elM_mul _ _ _ _).symm

@[expose] def radP (F : Type) [Field F] : Subgroup SL(3, F) := (elPHom F).range

@[expose] def radM (F : Type) [Field F] : Subgroup SL(3, F) := (elMHom F).range

theorem mem_radP {g : SL(3, F)} : g ∈ radP F ↔ ∃ a b : F, g = elP a b := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, _, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨Multiplicative.ofAdd (a, b), rfl⟩

theorem mem_radM {g : SL(3, F)} : g ∈ radM F ↔ ∃ a b : F, g = elM a b := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, _, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨Multiplicative.ofAdd (a, b), rfl⟩

theorem eq_elP_of_fixes {g : SL(3, F)}
    (h1 : ∀ v ∈ vPlus F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v)
    (h2 : ∀ v : Fin 3 → F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ vPlus F) :
    g = elP ((g : Matrix (Fin 3) (Fin 3) F) 2 0) ((g : Matrix (Fin 3) (Fin 3) F) 2 1) := by
  have e3 := h1 (Pi.single 2 1) (by simp [mem_vPlus])
  have e1 := (h2 (Pi.single 0 1))
  have e2 := (h2 (Pi.single 1 1))
  rw [mem_vPlus] at e1 e2
  have c02 := congrFun e3 0
  have c12 := congrFun e3 1
  have c22 := congrFun e3 2
  simp [Matrix.mulVec_single] at c02 c12 c22 e1 e2
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_elP]
  · linear_combination e1.1
  · exact e2.1
  · exact c02
  · exact e1.2
  · linear_combination e2.2
  · exact c12
  · exact c22

theorem eq_elM_of_fixes {g : SL(3, F)}
    (h1 : ∀ v ∈ vMinus F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v)
    (h2 : ∀ v : Fin 3 → F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ vMinus F) :
    g = elM ((g : Matrix (Fin 3) (Fin 3) F) 0 2) ((g : Matrix (Fin 3) (Fin 3) F) 1 2) := by
  have e1 := h1 (Pi.single 0 1) (by simp [mem_vMinus])
  have e2 := h1 (Pi.single 1 1) (by simp [mem_vMinus])
  have e3 := (h2 (Pi.single 2 1))
  rw [mem_vMinus] at e3
  have a0 := congrFun e1 0
  have a1 := congrFun e1 1
  have a2 := congrFun e1 2
  have b0 := congrFun e2 0
  have b1 := congrFun e2 1
  have b2 := congrFun e2 2
  simp [Matrix.mulVec_single] at a0 a1 a2 b0 b1 b2 e3
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_elM]
  · exact a0
  · exact b0
  · exact a1
  · exact b1
  · exact a2
  · exact b2
  · linear_combination e3

theorem elP_mul_bSL (A : SL(2, F)) (a b : F) :
    elP a b * bSL A = bSL A * elP (a * (A : Matrix (Fin 2) (Fin 2) F) 0 0 + b * (A : Matrix (Fin 2) (Fin 2) F) 1 0)
      (a * (A : Matrix (Fin 2) (Fin 2) F) 0 1 + b * (A : Matrix (Fin 2) (Fin 2) F) 1 1) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_elP, coe_bSL, Matrix.mul_apply, Fin.sum_univ_three]

theorem bSL_mul_elM (A : SL(2, F)) (a b : F) :
    bSL A * elM a b = elM ((A : Matrix (Fin 2) (Fin 2) F) 0 0 * a + (A : Matrix (Fin 2) (Fin 2) F) 0 1 * b)
      ((A : Matrix (Fin 2) (Fin 2) F) 1 0 * a + (A : Matrix (Fin 2) (Fin 2) F) 1 1 * b) * bSL A := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_elM, coe_bSL, Matrix.mul_apply, Fin.sum_univ_three]

theorem elP_mem_of_normalizer {R : Subgroup SL(3, F)} (hN : CenD F ≤ normalizer (R : Set SL(3, F)))
    {a b : F} (h : elP a b ∈ R) (A : SL(2, F)) :
    elP (a * (A : Matrix (Fin 2) (Fin 2) F) 0 0 + b * (A : Matrix (Fin 2) (Fin 2) F) 1 0)
      (a * (A : Matrix (Fin 2) (Fin 2) F) 0 1 + b * (A : Matrix (Fin 2) (Fin 2) F) 1 1) ∈ R := by
  have hc : (bSL A)⁻¹ ∈ normalizer (R : Set SL(3, F)) :=
    (normalizer (R : Set SL(3, F))).inv_mem (hN (bSL_mem_CenD A))
  have := (Subgroup.mem_normalizer_iff.mp hc (elP a b)).mp h
  rw [inv_inv] at this
  have e : (bSL A)⁻¹ * elP a b * bSL A = elP (a * (A : Matrix (Fin 2) (Fin 2) F) 0 0 + b * (A : Matrix (Fin 2) (Fin 2) F) 1 0)
      (a * (A : Matrix (Fin 2) (Fin 2) F) 0 1 + b * (A : Matrix (Fin 2) (Fin 2) F) 1 1) := by
    rw [mul_assoc, elP_mul_bSL, ← mul_assoc, inv_mul_cancel, one_mul]
  rwa [e] at this

theorem elM_mem_of_normalizer {R : Subgroup SL(3, F)} (hN : CenD F ≤ normalizer (R : Set SL(3, F)))
    {a b : F} (h : elM a b ∈ R) (A : SL(2, F)) :
    elM ((A : Matrix (Fin 2) (Fin 2) F) 0 0 * a + (A : Matrix (Fin 2) (Fin 2) F) 0 1 * b)
      ((A : Matrix (Fin 2) (Fin 2) F) 1 0 * a + (A : Matrix (Fin 2) (Fin 2) F) 1 1 * b) ∈ R := by
  have hc : bSL A ∈ normalizer (R : Set SL(3, F)) := hN (bSL_mem_CenD A)
  have := (Subgroup.mem_normalizer_iff.mp hc (elM a b)).mp h
  have e : bSL A * elM a b * (bSL A)⁻¹ = elM ((A : Matrix (Fin 2) (Fin 2) F) 0 0 * a + (A : Matrix (Fin 2) (Fin 2) F) 0 1 * b)
      ((A : Matrix (Fin 2) (Fin 2) F) 1 0 * a + (A : Matrix (Fin 2) (Fin 2) F) 1 1 * b) := by
    rw [bSL_mul_elM, mul_assoc, mul_inv_cancel, mul_one]
  rwa [e] at this

theorem eq_radP_of_le {R : Subgroup SL(3, F)} (hN : CenD F ≤ normalizer (R : Set SL(3, F)))
    (hne : R ≠ ⊥) (hle : R ≤ radP F) : R = radP F := by
  refine le_antisymm hle ?_
  obtain ⟨⟨g₀, hg₀⟩, hg₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨a₀, b₀, he⟩ := mem_radP.mp (hle hg₀)
  have hR0 : elP a₀ b₀ ∈ R := by rw [← he]; exact hg₀
  have hab : (![a₀, b₀] : Fin 2 → F) ≠ 0 := by
    intro h
    apply hg₀1
    apply Subtype.ext
    have ha : a₀ = 0 := by simpa using congrFun h 0
    have hb : b₀ = 0 := by simpa using congrFun h 1
    show g₀ = 1
    rw [he, ha, hb, elP_zero]
  intro g hg
  obtain ⟨a, b, rfl⟩ := mem_radP.mp hg
  by_cases hz : (![a, b] : Fin 2 → F) = 0
  · have ha : a = 0 := by simpa using congrFun hz 0
    have hb : b = 0 := by simpa using congrFun hz 1
    rw [ha, hb, elP_zero]
    exact one_mem _
  · obtain ⟨A, hA⟩ := exists_sl2_vecMul hab hz
    have := elP_mem_of_normalizer hN hR0 A
    have h0 := congrFun hA 0
    have h1 := congrFun hA 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h0 h1
    rw [h0, h1] at this
    exact this

theorem eq_radM_of_le {R : Subgroup SL(3, F)} (hN : CenD F ≤ normalizer (R : Set SL(3, F)))
    (hne : R ≠ ⊥) (hle : R ≤ radM F) : R = radM F := by
  refine le_antisymm hle ?_
  obtain ⟨⟨g₀, hg₀⟩, hg₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨a₀, b₀, he⟩ := mem_radM.mp (hle hg₀)
  have hR0 : elM a₀ b₀ ∈ R := by rw [← he]; exact hg₀
  have hab : (![a₀, b₀] : Fin 2 → F) ≠ 0 := by
    intro h
    apply hg₀1
    apply Subtype.ext
    have ha : a₀ = 0 := by simpa using congrFun h 0
    have hb : b₀ = 0 := by simpa using congrFun h 1
    show g₀ = 1
    rw [he, ha, hb, elM_zero]
  intro g hg
  obtain ⟨a, b, rfl⟩ := mem_radM.mp hg
  by_cases hz : (![a, b] : Fin 2 → F) = 0
  · have ha : a = 0 := by simpa using congrFun hz 0
    have hb : b = 0 := by simpa using congrFun hz 1
    rw [ha, hb, elM_zero]
    exact one_mem _
  · obtain ⟨A, hA⟩ := exists_sl2_mulVec hab hz
    have := elM_mem_of_normalizer hN hR0 A
    have h0 := congrFun hA 0
    have h1 := congrFun hA 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    rw [h0, h1] at this
    exact this

end Elations

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
