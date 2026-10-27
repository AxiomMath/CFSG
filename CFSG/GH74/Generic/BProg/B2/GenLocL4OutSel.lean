module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutNF
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutGraph

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

variable {F : Type} [Field F]

theorem not_mem_range_conj_of_not_innerDiag {φ : MulAut (Matrix.SpecialLinearGroup (Fin 4) F)}
    (h : ¬ IsInnerDiag4 φ) :
    φ ∉ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 4) F →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)).range := by
  rintro ⟨s, rfl⟩
  apply h
  refine ⟨Matrix.SpecialLinearGroup.toGL s, fun g => ?_⟩
  have h1 : (((Matrix.SpecialLinearGroup.toGL s)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    rw [← map_inv]; rfl
  rw [h1, MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rfl

theorem hN_one : ∀ i : Fin 4, (1 : Matrix (Fin 4) (Fin 4) F) * mm i = mm i * 1 ∨
    (1 : Matrix (Fin 4) (Fin 4) F) * mm i = -(mm i * 1) := fun i => Or.inl (by simp)

theorem hN_m1 : ∀ i : Fin 4, (m1 : Matrix (Fin 4) (Fin 4) F) * mm i = mm i * m1 ∨
    (m1 : Matrix (Fin 4) (Fin 4) F) * mm i = -(mm i * m1) := by
  intro i
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr m12
  · exact Or.inl m13
  · exact Or.inl m14

theorem graph_minus_of_sectional [Finite F] (hF4 : Nat.card F % 4 = 3) {A : Type} [Group A] [Finite A]
    (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (a : A)
    (hout : ¬ IsInnerDiag4 (α a)) (hsect : SectionalTwoRankLE ↥(innJoin α) 4) :
    ∃ B : GL (Fin 4) F, (∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
        ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          (B : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).transpose *
            ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) ∧
      (B : Matrix (Fin 4) (Fin 4) F).transpose = B ∧ ¬ IsSquare (B : Matrix (Fin 4) (Fin 4) F).det := by
  have hu : α a * α a = 1 := by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a, map_one]
  obtain ⟨B, hB, hsymm⟩ := exists_graph_form hF4 (α a) hu hout
  have hdet : (B : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_mod hF4)
  have hnin := not_mem_range_conj_of_not_innerDiag hout
  rcases hsymm with hs | hs
  · refine ⟨B, hB, hs, fun hsq => ?_⟩
    obtain ⟨P, hP⟩ := exists_cong_plus hF4 B hs hdet hsq
    exact not_sectional_of_graph_form h2 hA α a hnin B P 1 (by rw [Matrix.mul_one]; exact hP) hB hN_one hsect
  · exfalso
    obtain ⟨P, hP⟩ := exists_cong_skew hF4 B hs hdet
    exact not_sectional_of_graph_form h2 hA α a hnin B P m1 hP hB hN_m1 hsect

end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
