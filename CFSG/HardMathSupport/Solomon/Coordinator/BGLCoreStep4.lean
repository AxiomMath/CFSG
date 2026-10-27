module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreAxis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.LargeExtraspecial.A2Mod
open scoped commutatorElement

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem isRat_single (i : Fin 3) : IsRat σ (Pi.single i (1 : F) : Fin 3 → F) := fun j => by
  by_cases hj : j = i <;> simp [hj]

theorem exists_rat_orth {b : Fin 3 → F} (hb : IsRat σ b) :
    ∃ a : Fin 3 → F, IsRat σ a ∧ a ≠ 0 ∧ b ⬝ᵥ a = 0 := by
  by_cases h01 : b 0 = 0 ∧ b 1 = 0
  · refine ⟨![1, 0, 0], ?_, ?_, ?_⟩
    · intro j; fin_cases j <;> simp
    · intro h; have := congrFun h 0; simp at this
    · simp [dotProduct, Fin.sum_univ_three, h01.1]
  · refine ⟨![b 1, -b 0, 0], ?_, ?_, ?_⟩
    · intro j; fin_cases j <;> simp [hb _]
    · intro h
      apply h01
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      simp at e0 e1
      exact ⟨e1, e0⟩
    · simp [dotProduct, Fin.sum_univ_three]; ring

theorem top_le_joinH_of_line [Finite F] (hr : (orderOf σ).Prime) {h : GL (Fin 3) F} {b : Fin 3 → F}
    (hb : IsRat σ b) (hb0 : b ≠ 0)
    (hbu : b ⬝ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) = 0)
    (hu : ¬ ∃ c : F, c ≠ 0 ∧ IsRat σ (c • ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1))) :
    ⊤ ≤ joinH σ h := by
  have hA := fixSL3_le_joinH (σ := σ) h
  set u := (h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 with hu_def
  set hi := ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hhi
  obtain ⟨a, ha, ha0, hba⟩ := exists_rat_orth hb
  have hw : ∃ i : Fin 3, i ≠ 0 ∧ (Pi.single i (1 : F) ᵥ* hi) ⬝ᵥ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu
    have hcoord : ∀ i : Fin 3, i ≠ 0 → (hi *ᵥ a) i = 0 := fun i hi0 => by
      have := hcon i hi0
      rw [← Matrix.dotProduct_mulVec] at this
      simpa [dotProduct, Pi.single_apply] using this
    obtain ⟨c, hc⟩ : ∃ c : F, (hi *ᵥ a) 0 = c := ⟨_, rfl⟩
    have hia : hi *ᵥ a = c • Pi.single 0 1 := by
      funext i
      by_cases hi0 : i = 0
      · subst hi0; simp [hc]
      · rw [hcoord i hi0]; simp [hi0]
    have haeq : a = c • u := by
      calc a = (h : Matrix (Fin 3) (Fin 3) F) *ᵥ (hi *ᵥ a) := by
            rw [Matrix.mulVec_mulVec, hhi, coe_mul_inv, Matrix.one_mulVec]
        _ = c • u := by rw [hia, Matrix.mulVec_smul]
    have hc0 : c ≠ 0 := by
      intro h0
      apply ha0
      rw [haeq, h0, zero_smul]
    exact ⟨c, hc0, haeq ▸ ha⟩
  obtain ⟨i, hi0, hwa⟩ := hw
  set w := Pi.single i (1 : F) ᵥ* hi
  have hwu : w ⬝ᵥ u = 0 := by
    rw [hu_def, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hhi, coe_inv_mul,
      Matrix.one_mulVec]
    simp [dotProduct, Pi.single_apply]
    fin_cases i <;> simp_all
  have hT1 : tv u w ∈ joinH σ h := by
    have hd : (Pi.single i (1 : F) : Fin 3 → F) ⬝ᵥ Pi.single 0 1 = 0 := by
      simp [dotProduct, Pi.single_apply, Ne.symm hi0]
    exact conj_tv_mem_joinH h hd (isRat_single 0) (isRat_single i)
  have hT2 : tv a b ∈ joinH σ h := hA (tv_mem_fixSL3 hba ha hb)
  have hcomm := commutator_tv hwu hba hbu
  have hmem : tv ((w ⬝ᵥ a) • u) b ∈ joinH σ h := by
    rw [← hcomm, commutatorElement_def]
    exact (joinH σ h).mul_mem ((joinH σ h).mul_mem ((joinH σ h).mul_mem hT1 hT2)
      ((joinH σ h).inv_mem hT1)) ((joinH σ h).inv_mem hT2)
  refine top_le_of_tv_rat_axis hr hA hb hb0 ?_ ?_ hmem
  · rw [dotProduct_smul, hbu, smul_zero]
  · intro hcu
    exact hu ⟨w ⬝ᵥ a, hwa, hcu⟩

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
