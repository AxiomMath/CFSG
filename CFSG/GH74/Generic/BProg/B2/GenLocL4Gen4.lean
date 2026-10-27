module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4Core
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.LocalAnalysis.ComponentInitial Subgroup

namespace GenLocL4Gen4

variable {F : Type} [Field F] [Finite F]

theorem exists_sqrt_neg_one (hF : Nat.card F % 8 = 5) : ∃ i : F, i * i = -1 := by
  have := Fintype.ofFinite F
  have h4 : Fintype.card F % 4 ≠ 3 := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.2 h4
  exact ⟨r, hr.symm⟩

theorem ringChar_ne_two (hF : Nat.card F % 8 = 5) : ringChar F ≠ 2 := by
  have := Fintype.ofFinite F
  intro h
  have h2 := FiniteField.even_card_iff_char_two.1 h
  rw [← Nat.card_eq_fintype_card] at h2
  omega

theorem pow_four_ne_neg_one_of_card (hF : Nat.card F % 8 = 5) (c : Fˣ) : (c : F) ^ 4 ≠ -1 := by
  have := Fintype.ofFinite F
  have hc := FiniteField.pow_card_sub_one_eq_one (c : F) c.ne_zero
  refine pow_four_ne_neg_one (m := Fintype.card F - 1) ?_ (Ring.neg_one_ne_one_of_char_ne_two
    (ringChar_ne_two hF)) hc
  rw [← Nat.card_eq_fintype_card]
  omega

variable (i : F) (hi : i * i = -1)

omit [Finite F] in
theorem conjAut_mem_of_det {A t : GL (Fin 4) F} (hdet : (A : Matrix (Fin 4) (Fin 4) F).det = 1 ∨
    (A : Matrix (Fin 4) (Fin 4) F).det = -1) (ht : (t : Matrix (Fin 4) (Fin 4) F).det = -1) :
    LinearFlag.conjAut 4 F A ∈ (MulAut.conj : LinearFlag.projectiveSL 4 F →* MulAut _).range ⊔
      zpowers (LinearFlag.conjAut 4 F t) := by
  have hinner : ∀ B : GL (Fin 4) F, (B : Matrix (Fin 4) (Fin 4) F).det = 1 →
      LinearFlag.conjAut 4 F B ∈ (MulAut.conj : LinearFlag.projectiveSL 4 F →* MulAut _).range := by
    intro B hB
    let s : Matrix.SpecialLinearGroup (Fin 4) F := ⟨(B : Matrix (Fin 4) (Fin 4) F), hB⟩
    have : B = Matrix.SpecialLinearGroup.toGL s := Units.ext rfl
    rw [this, LinearFlag.conjAut_toGL]
    exact ⟨_, rfl⟩
  rcases hdet with h | h
  · exact Subgroup.mem_sup_left (hinner A h)
  · have h1 : ((A * t⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
      have hu : IsUnit ((t : Matrix (Fin 4) (Fin 4) F).det) := by
        rw [ht]; exact isUnit_one.neg
      have h2 : ((t⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det * (t : Matrix (Fin 4) (Fin 4) F).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
      rw [Units.val_mul, Matrix.det_mul, h]
      rw [ht] at h2
      linear_combination h2
    have h3 : LinearFlag.conjAut 4 F A =
        LinearFlag.conjAut 4 F (A * t⁻¹) * LinearFlag.conjAut 4 F t := by
      rw [← map_mul, inv_mul_cancel_right]
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hinner _ h1))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

end GenLocL4Gen4

open GenLocL4Gen4 in
theorem not_sectional_l4_t1 {F : Type} [Field F] [Finite F] (hF : Nat.card F % 8 = 5) (t : GL (Fin 4) F)
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![-1, 1, 1, 1]) :
    ¬ SectionalTwoRankLE ↥((MulAut.conj : LinearFlag.projectiveSL 4 F →* MulAut _).range ⊔
      zpowers (LinearFlag.conjAut 4 F t)) 4 := by
  obtain ⟨i, hi⟩ := exists_sqrt_neg_one hF
  have hF2 := ringChar_ne_two hF
  have hne : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hF2
  have hdt : (t : Matrix (Fin 4) (Fin 4) F).det = -1 := by
    rw [ht, Matrix.det_diagonal]
    simp [Fin.prod_univ_four]
  have : Finite (MulAut (LinearFlag.projectiveSL 4 F)) :=
    Finite.of_injective (fun α : MulAut (LinearFlag.projectiveSL 4 F) => (α : _ → _))
      fun _ _ h => MulEquiv.ext (congrFun h)
  refine not_sectionalTwoRankLE_of_char _
    ((LinearFlag.conjAut 4 F).comp (Θ.comp (K₀ i hi).subtype))
    (fun k => conjAut_mem_of_det (det_Θ_eq i hi k) hdt) (psi i hi) (psi_sq i hi) ?_
    (r := 4) (by have := card_range_psi i hi hne; omega)
  intro k hk
  have h1 : LinearFlag.conjAut 4 F (Θ (k : GL (Fin 2) F × GL (Fin 2) F)) = 1 := hk
  obtain ⟨-, c, hc⟩ := LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num : 3 ≤ 4)
    (Θ (k : GL (Fin 2) F × GL (Fin 2) F)) 1 (by rw [map_one, mul_one]; exact h1)
  exact psi_eq_one_of_scalar i hi k c hc.symm (pow_four_ne_neg_one_of_card hF c)

end CFSG.GH74.Generic.BProg.B2
