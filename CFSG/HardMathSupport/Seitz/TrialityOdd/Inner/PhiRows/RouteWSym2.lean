module

public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Matrix
open scoped MatrixGroups

section Ring

variable {F : Type*} [CommRing F]

@[expose] def sym2Mat (g : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![g 0 0 ^ 2, g 0 0 * g 0 1, g 0 1 ^ 2;
     2 * g 0 0 * g 1 0, g 0 0 * g 1 1 + g 0 1 * g 1 0, 2 * g 0 1 * g 1 1;
     g 1 0 ^ 2, g 1 0 * g 1 1, g 1 1 ^ 2]

variable (F) in
@[expose] def sym2Form : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, -2, 0; 1, 0, 0]

theorem sym2Mat_mul (g h : Matrix (Fin 2) (Fin 2) F) :
    sym2Mat (g * h) = sym2Mat g * sym2Mat h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sym2Mat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

theorem sym2Mat_one : sym2Mat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sym2Mat]

theorem det_sym2Mat (g : Matrix (Fin 2) (Fin 2) F) : (sym2Mat g).det = g.det ^ 3 := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [sym2Mat]
  ring

theorem sym2Mat_form_det (g : Matrix (Fin 2) (Fin 2) F) :
    sym2Mat g * sym2Form F * (sym2Mat g)ᵀ = g.det ^ 2 • sym2Form F := by
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sym2Mat, sym2Form, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> ring

theorem sym2Mat_form (g : Matrix (Fin 2) (Fin 2) F) (hg : g.det = 1) :
    sym2Mat g * sym2Form F * (sym2Mat g)ᵀ = sym2Form F := by
  rw [sym2Mat_form_det, hg, one_pow, one_smul]

variable (F) in
@[expose] def sym2Hom : SL(2, F) →* SL(3, F) where
  toFun g := ⟨sym2Mat (g : Matrix (Fin 2) (Fin 2) F), by rw [det_sym2Mat, g.det_coe, one_pow]⟩
  map_one' := Subtype.ext (by simp only [Matrix.SpecialLinearGroup.coe_one]; exact sym2Mat_one)
  map_mul' a b := Subtype.ext (by simp only [Matrix.SpecialLinearGroup.coe_mul]; exact sym2Mat_mul _ _)

theorem coe_sym2Hom (g : SL(2, F)) :
    ((sym2Hom F g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      sym2Mat (g : Matrix (Fin 2) (Fin 2) F) :=
  rfl

end Ring

section Field

variable {F : Type*} [Field F]

theorem sym2Hom_eq_one_iff (g : SL(2, F)) :
    sym2Hom F g = 1 ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro h
    have hm : ∀ i j, sym2Mat (g : Matrix (Fin 2) (Fin 2) F) i j =
        (1 : Matrix (Fin 3) (Fin 3) F) i j := fun i j => by
      have h' := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F) i j) h
      simpa [coe_sym2Hom] using h'
    have e00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 = 1 := by
      have := hm 0 0
      rwa [show sym2Mat (g : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 from rfl, Matrix.one_apply_eq] at this
    have e02 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 ^ 2 = 0 := by
      have := hm 0 2
      rwa [show sym2Mat (g : Matrix (Fin 2) (Fin 2) F) 0 2 =
        (g : Matrix (Fin 2) (Fin 2) F) 0 1 ^ 2 from rfl,
        Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 2)] at this
    have e20 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2 = 0 := by
      have := hm 2 0
      rwa [show sym2Mat (g : Matrix (Fin 2) (Fin 2) F) 2 0 =
        (g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2 from rfl,
        Matrix.one_apply_ne (by decide : (2 : Fin 3) ≠ 0)] at this
    have e11 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 +
        (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
      have := hm 1 1
      rwa [show sym2Mat (g : Matrix (Fin 2) (Fin 2) F) 1 1 =
        (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 +
          (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 from rfl,
        Matrix.one_apply_eq] at this
    have h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := pow_eq_zero_iff two_ne_zero |>.1 e02
    have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 e20
    rw [h01, h10, mul_zero, add_zero] at e11
    have hsq : ((g : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) *
        ((g : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) = 0 := by
      linear_combination e00
    have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      have hu : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
        rw [← sq]; exact e00
      calc (g : Matrix (Fin 2) (Fin 2) F) 1 1 =
            (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 *
              (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by rw [hu, one_mul]
        _ = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by rw [mul_assoc, e11, mul_one]
    rcases mul_eq_zero.1 hsq with h | h
    · left
      have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := sub_eq_zero.1 h
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
    · right
      have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = -1 := eq_neg_of_add_eq_zero_left h
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  · rintro (rfl | rfl)
    · exact map_one _
    · refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [coe_sym2Hom, sym2Mat]

theorem sym2Hom_ker : ((sym2Hom F).ker : Set SL(2, F)) = {1, -1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact sym2Hom_eq_one_iff g

theorem one_ne_neg_one_SL2 (h2 : (2 : F) ≠ 0) : (1 : SL(2, F)) ≠ -1 := by
  intro h
  have h' := congrArg (fun g : SL(2, F) => g 0 0) h
  simp at h'
  apply h2
  linear_combination h'

theorem nat_card_range_sym2Hom [Finite F] (h2 : (2 : F) ≠ 0) :
    2 * Nat.card (sym2Hom F).range = Nat.card SL(2, F) := by
  have hker : Nat.card (sym2Hom F).ker = 2 := by
    rw [← SetLike.coe_sort_coe, sym2Hom_ker, Nat.card_coe_set_eq,
      Set.ncard_pair (one_ne_neg_one_SL2 h2)]
  have := Subgroup.card_ker_mul_card_range (sym2Hom F)
  rw [hker] at this
  exact this

theorem commutator_range_sym2Hom [Finite F] (h4 : 4 ≤ Nat.card F) :
    ⁅(sym2Hom F).range, (sym2Hom F).range⁆ = (sym2Hom F).range := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hK : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F))
      (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  have hperf : ⁅(⊤ : Subgroup SL(2, F)), ⊤⁆ = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_two_perfect hK).commutator_eq_top
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]

end Field

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
