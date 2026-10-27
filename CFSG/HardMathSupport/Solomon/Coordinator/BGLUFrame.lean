module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix Module CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

theorem frame_span_eq_top (hσ : ∀ c, σ (σ c) = c) {a b w : Fin 3 → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1) (haw : herm σ a w = 0)
    (hbw : herm σ b w = 0) (hw : herm σ w w ≠ 0) :
    Submodule.span K (Set.range ![a, b, w]) = ⊤ := by
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ, hab, map_one]
  have hwa : herm σ w a = 0 := herm_eq_zero_comm σ hσ haw
  have hwb : herm σ w b = 0 := herm_eq_zero_comm σ hσ hbw
  have hli : LinearIndependent K ![a, b, w] := by
    rw [Fintype.linearIndependent_iff]
    intro f hf
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      add_zero] at hf
    have h1 := congrArg (herm σ a) hf
    have h2 := congrArg (herm σ b) hf
    have h3 := congrArg (herm σ w) hf
    simp only [herm_add_right, herm_smul_right, herm_zero_right, ha, hb, hab, hba, haw, hbw, hwa,
      hwb, mul_zero, mul_one, zero_add, add_zero] at h1 h2 h3
    intro i
    fin_cases i
    · exact h2
    · exact h1
    · exact (mul_eq_zero.mp h3).resolve_right hw
  exact hli.span_eq_top_of_card_eq_finrank' (by simp)

theorem frame_decomp (hσ : ∀ c, σ (σ c) = c) {a b w : Fin 3 → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1) (haw : herm σ a w = 0)
    (hbw : herm σ b w = 0) (hw : herm σ w w ≠ 0) (x : Fin 3 → K) :
    x = herm σ b x • a + herm σ a x • b + (herm σ w x / herm σ w w) • w := by
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ, hab, map_one]
  have hwa : herm σ w a = 0 := herm_eq_zero_comm σ hσ haw
  have hwb : herm σ w b = 0 := herm_eq_zero_comm σ hσ hbw
  have hspan := frame_span_eq_top hσ ha hb hab haw hbw hw
  set u := x - (herm σ b x • a + herm σ a x • b + (herm σ w x / herm σ w w) • w) with hu
  have hzero : ∀ v ∈ Submodule.span K (Set.range ![a, b, w]), herm σ v u = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      fin_cases i
      · simp [hu, herm_sub_right, herm_add_right, herm_smul_right, ha, hab, haw]
      · simp [hu, herm_sub_right, herm_add_right, herm_smul_right, hba, hb, hbw]
      · simp [hu, herm_sub_right, herm_add_right, herm_smul_right, hwa, hwb, hw]
    | zero => simp
    | add v v' _ _ h h' => rw [herm_add_left, h, h', add_zero]
    | smul c v _ h => rw [herm_smul_left, h, mul_zero]
  rw [hspan] at hzero
  have hu0 : u = 0 := eq_zero_of_herm σ fun y =>
    herm_eq_zero_comm σ hσ (hzero y Submodule.mem_top)
  exact sub_eq_zero.mp hu0

theorem eq_add_of_herm_left_eq_zero (hσ : ∀ c, σ (σ c) = c) {a b w : Fin 3 → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1) (haw : herm σ a w = 0)
    (hbw : herm σ b w = 0) (hw : herm σ w w ≠ 0) {y : Fin 3 → K} (hy : herm σ a y = 0) :
    y = herm σ b y • a + (herm σ w y / herm σ w w) • w := by
  have := frame_decomp hσ ha hb hab haw hbw hw y
  rwa [hy, zero_smul, add_zero] at this

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
