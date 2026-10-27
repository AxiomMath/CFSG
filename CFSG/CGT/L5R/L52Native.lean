module

public import CFSG.CGT.L5R.RelData
public import CFSG.GroupTheory.GL52.Simple

public section

namespace CFSG.CGT.L5R

open CFSG.CGT.M24R CFSG.GroupTheory.GL52 Matrix

@[expose] def l52MInv : Fin 11 → M5 :=
  ![!![0, 1, 0, 1, 0; 0, 1, 1, 0, 0; 0, 1, 0, 0, 0; 1, 0, 1, 1, 0; 0, 0, 0, 0, 1],
    !![0, 1, 1, 1, 0; 1, 0, 0, 1, 0; 1, 1, 0, 0, 0; 1, 0, 1, 0, 0; 0, 0, 0, 0, 1],
    !![1, 1, 1, 1, 0; 0, 0, 1, 0, 0; 0, 1, 1, 0, 0; 1, 1, 0, 0, 0; 0, 0, 0, 0, 1],
    !![1, 1, 0, 1, 0; 1, 1, 1, 1, 0; 1, 1, 1, 0, 0; 0, 1, 1, 1, 0; 0, 0, 0, 0, 1],
    !![0, 0, 1, 0, 0; 1, 1, 0, 1, 0; 1, 0, 1, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 1, 0, 0; 1, 0, 1, 1, 0; 1, 0, 0, 0, 0; 1, 1, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 1, 1],
    !![1, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]]

theorem l52M_mul_l52MInv : ∀ i, l52M i * l52MInv i = 1 := by
  decide +kernel

@[expose] def l52Mat (i : Fin 11) : G52 :=
  mk5 (l52M i) (l52MInv i) (l52M_mul_l52MInv i)

@[simp] theorem coe_l52Mat (i : Fin 11) : ((l52Mat i : G52) : M5) = l52M i :=
  rfl

theorem coe_l52Mat_inv (i : Fin 11) : (((l52Mat i)⁻¹ : G52) : M5) = l52MInv i :=
  rfl

@[expose] def matW : M24Word → M5
  | [] => 1
  | (i, b) :: w => (if b then l52M i else l52MInv i) * matW w

theorem coe_evalW_l52Mat (w : M24Word) : ((evalW l52Mat w : G52) : M5) = matW w := by
  induction w with
  | nil => simp [matW]
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    cases b
    · rw [evalW_cons_false, Units.val_mul, coe_l52Mat_inv, ih]
      rfl
    · rw [evalW_cons_true, Units.val_mul, coe_l52Mat, ih]
      rfl

theorem matW_l52Rels : ∀ r ∈ l52Rels, matW r = 1 := by
  decide +kernel

theorem evalW_l52Mat_eq_one {r : M24Word} (hr : r ∈ l52Rels) : evalW l52Mat r = 1 :=
  Units.ext (by rw [coe_evalW_l52Mat, matW_l52Rels r hr, Units.val_one])

theorem matW_transvWordL :
    ∀ k : Fin 20, matW (transvWordL k) = transvection (transvPairL k).1 (transvPairL k).2 1 := by
  decide +kernel

theorem coe_evalW_l52Mat_transvWordL (k : Fin 20) :
    ((evalW l52Mat (transvWordL k) : G52) : M5) =
      transvection (transvPairL k).1 (transvPairL k).2 1 := by
  rw [coe_evalW_l52Mat, matW_transvWordL]

theorem exists_transvPairL_eq : ∀ i j : Fin 5, i ≠ j → ∃ k, transvPairL k = (i, j) := by
  decide

private theorem evalW_mem_closure {H : Type*} [Group H] (e : Fin 11 → H) (w : M24Word) :
    evalW e w ∈ Subgroup.closure (Set.range e) := by
  rw [← FreeGroup.range_lift_eq_closure]
  exact ⟨_, rfl⟩

private theorem zmod_two_eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
  decide

theorem closure_range_l52Mat : Subgroup.closure (Set.range l52Mat) = ⊤ := by
  set S := Subgroup.closure (Set.range l52Mat)
  have key : ∀ M : M5, M.det ≠ 0 → ∃ g ∈ S, (g : M5) = M := by
    intro M hM
    refine diagonal_transvection_induction_of_det_ne_zero (fun M => ∃ g ∈ S, (g : M5) = M) M hM
      ?_ ?_ ?_
    · intro D hD
      have h1 : D = fun _ => 1 := funext fun i => zmod_two_eq_one_of_ne_zero _
        (Finset.prod_ne_zero_iff.1 (by rwa [det_diagonal] at hD) i (Finset.mem_univ i))
      exact ⟨1, S.one_mem, by rw [Units.val_one, h1, diagonal_one]⟩
    · rintro ⟨i, j, hij, c⟩
      have hc : c = 0 ∨ c = 1 := by
        revert c
        decide
      rcases hc with rfl | rfl
      · exact ⟨1, S.one_mem, by simp⟩
      · obtain ⟨k, hk⟩ := exists_transvPairL_eq i j hij
        refine ⟨evalW l52Mat (transvWordL k), evalW_mem_closure _ _, ?_⟩
        rw [coe_evalW_l52Mat_transvWordL, hk]
        rfl
    · rintro A B - - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a * b, S.mul_mem ha hb, Units.val_mul a b⟩
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨g', hg', he⟩ := key g (by rw [det_G52]; exact one_ne_zero)
  rwa [← Units.ext he]

end CFSG.CGT.L5R
