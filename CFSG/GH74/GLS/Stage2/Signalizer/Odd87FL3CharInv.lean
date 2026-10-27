module

public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.KGroups.L3EpsWreath

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps
open scoped MatrixGroups

section Spaces

variable (F : Type) [Field F]

@[expose] def vPlus : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 = 0 ∧ v 1 = 0}
  add_mem' := by
    rintro a b ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
    exact ⟨by simp [ha0, hb0], by simp [ha1, hb1]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := by
    rintro c a ⟨ha0, ha1⟩
    exact ⟨by simp [ha0], by simp [ha1]⟩

@[expose] def vMinus : Submodule F (Fin 3 → F) where
  carrier := {v | v 2 = 0}
  add_mem' := by
    rintro a b (ha : a 2 = 0) (hb : b 2 = 0)
    show (a + b) 2 = 0
    simp [ha, hb]
  zero_mem' := rfl
  smul_mem' := by
    rintro c a (ha : a 2 = 0)
    show (c • a) 2 = 0
    simp [ha]

variable {F}

theorem mem_vPlus {v : Fin 3 → F} : v ∈ vPlus F ↔ v 0 = 0 ∧ v 1 = 0 := Iff.rfl

theorem mem_vMinus {v : Fin 3 → F} : v ∈ vMinus F ↔ v 2 = 0 := Iff.rfl

end Spaces

section Cases

variable {F : Type} [Field F]

theorem dNeg_mulVec (v : Fin 3 → F) :
    ((dNeg : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![-v 0, -v 1, v 2] := by
  funext i
  fin_cases i <;> simp [coe_dNeg, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem exists_sl2_mulVec {u x : Fin 2 → F} (hu : u ≠ 0) (hx : x ≠ 0) :
    ∃ A : SL(2, F), (A : Matrix (Fin 2) (Fin 2) F) *ᵥ u = x := by
  have hcop : ∀ w : Fin 2 → F, w ≠ 0 → IsCoprime (w 0) (w 1) := by
    intro w hw
    by_cases h0 : w 0 = 0
    · have h1 : w 1 ≠ 0 := fun h1 => hw (by ext i; fin_cases i <;> simp [h0, h1])
      exact ⟨0, (w 1)⁻¹, by simp [h1]⟩
    · exact ⟨(w 0)⁻¹, 0, by simp [h0]⟩
  obtain ⟨gu, hgu0, hgu1⟩ := (hcop u hu).exists_SL2_col 0
  obtain ⟨gx, hgx0, hgx1⟩ := (hcop x hx).exists_SL2_col 0
  have hu' : (gu : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = u := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hgu0, hgu1]
  have hx' : (gx : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = x := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hgx0, hgx1]
  have h1 : ((gu⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ u = ![1, 0] := by
    rw [← hu', Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  refine ⟨gx * gu⁻¹, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hx']

theorem exists_sl2_vecMul {u x : Fin 2 → F} (hu : u ≠ 0) (hx : x ≠ 0) :
    ∃ A : SL(2, F), u ᵥ* (A : Matrix (Fin 2) (Fin 2) F) = x := by
  obtain ⟨B, hB⟩ := exists_sl2_mulVec hu hx
  exact ⟨B.transpose, by rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.vecMul_transpose, hB]⟩

theorem invariant_subspace_cases (h2 : (2 : F) ≠ 0) (W : Submodule F (Fin 3 → F))
    (hW : ∀ g ∈ CenD F, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = vPlus F ∨ W = vMinus F ∨ W = ⊤ := by
  have hsplit : ∀ v ∈ W, (Pi.single 2 (v 2) : Fin 3 → F) ∈ W := by
    intro v hv
    have hd := hW dNeg (mem_CenD.2 rfl) v hv
    rw [dNeg_mulVec] at hd
    have h1 : (2 : F)⁻¹ • (v + ![-v 0, -v 1, v 2]) = Pi.single 2 (v 2) := by
      funext i
      fin_cases i
      · simp [Matrix.vecHead]
      · simp [Matrix.vecHead, Matrix.vecTail]
      · simp only [Fin.reduceFinMk, Pi.smul_apply, Pi.add_apply, Matrix.cons_val, smul_eq_mul,
          Pi.single_eq_same]
        rw [← two_mul, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
    rw [← h1]
    exact W.smul_mem _ (W.add_mem hv hd)
  have hplus : (∃ v ∈ W, v 2 ≠ 0) → vPlus F ≤ W := by
    rintro ⟨v, hv, hv2⟩ x ⟨hx0, hx1⟩
    have h3 : x = (x 2 * (v 2)⁻¹) • (Pi.single 2 (v 2) : Fin 3 → F) := by
      funext i
      fin_cases i
      · simpa using hx0
      · simpa using hx1
      · simpa using (inv_mul_cancel_right₀ hv2 (x 2)).symm
    rw [h3]
    exact W.smul_mem _ (hsplit v hv)
  have hminus : (∃ v ∈ W, v 0 ≠ 0 ∨ v 1 ≠ 0) → vMinus F ≤ W := by
    rintro ⟨v, hv, hv01⟩ x (hx : x 2 = 0)
    by_cases hx0 : x = 0
    · rw [hx0]
      exact W.zero_mem
    have huW : v - Pi.single 2 (v 2) ∈ W := W.sub_mem hv (hsplit v hv)
    set u : Fin 3 → F := v - Pi.single 2 (v 2) with hu
    have hu2 : u 2 = 0 := by simp [hu]
    have hu0 : u 0 = v 0 := by simp [hu]
    have hu1 : u 1 = v 1 := by simp [hu]
    have hu' : (![u 0, u 1] : Fin 2 → F) ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      rcases hv01 with h | h
      · exact h (by rw [← hu0]; exact h0)
      · exact h (by rw [← hu1]; exact h1)
    have hx' : (![x 0, x 1] : Fin 2 → F) ≠ 0 := by
      intro h
      apply hx0
      funext i
      fin_cases i
      · simpa using congrFun h 0
      · simpa using congrFun h 1
      · simpa using hx
    obtain ⟨A, hA⟩ := exists_sl2_mulVec hu' hx'
    have hbu : ((bSL A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = x := by
      have h0 := congrFun hA 0
      have h1 := congrFun hA 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
      funext i
      fin_cases i
      · simp [coe_bSL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        exact h0
      · simp [coe_bSL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        exact h1
      · simp [coe_bSL, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hu2, hx]
    rw [← hbu]
    exact hW (bSL A) (bSL_mem_CenD A) u huW
  by_cases hP : ∃ v ∈ W, v 2 ≠ 0 <;> by_cases hM : ∃ v ∈ W, v 0 ≠ 0 ∨ v 1 ≠ 0
  · refine Or.inr (Or.inr (Or.inr (eq_top_iff.2 fun v _ => ?_)))
    have h1 : (Pi.single 2 (v 2) : Fin 3 → F) ∈ vPlus F := ⟨by simp, by simp⟩
    have h2' : v - Pi.single 2 (v 2) ∈ vMinus F := by
      show (v - (Pi.single 2 (v 2) : Fin 3 → F)) 2 = 0
      simp
    have := W.add_mem (hplus hP h1) (hminus hM h2')
    simpa using this
  · refine Or.inr (Or.inl (le_antisymm (fun v hv => ?_) (hplus hP)))
    exact ⟨by_contra fun h => hM ⟨v, hv, Or.inl h⟩, by_contra fun h => hM ⟨v, hv, Or.inr h⟩⟩
  · refine Or.inr (Or.inr (Or.inl (le_antisymm (fun v hv => ?_) (hminus hM))))
    exact by_contra fun h => hP ⟨v, hv, h⟩
  · refine Or.inl (eq_bot_iff.2 fun v hv => ?_)
    have h0 : v 0 = 0 := by_contra fun h => hM ⟨v, hv, Or.inl h⟩
    have h1 : v 1 = 0 := by_contra fun h => hM ⟨v, hv, Or.inr h⟩
    have h2' : v 2 = 0 := by_contra fun h => hP ⟨v, hv, h⟩
    rw [Submodule.mem_bot]
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2'

end Cases

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
