module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7CF24Check
public import CFSG.Sporadic.Recognition.SuzMultiplier

public section

namespace CFSG.ComponentClassification.GSThmB.CF24

open CFSG.F3.Native CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.SuzMultiplier
  CFSG.Sporadic.Presentation.Suz

section Eval

variable (E Ei : ℕ → Array V)

theorem cf24_mul_size (d : ℕ) (X Y : Array V) : (mul d X Y).size = X.size := by
  unfold mul
  exact Array.size_map

theorem cf24EvalM_facts (hE : ∀ i : Fin gcS, (E i).size = 12 ∧ RowsWF (E i))
    (hEi : ∀ i : Fin gcS, (Ei i).size = 12 ∧ RowsWF (Ei i)) (w : List (Fin gcS × Bool)) :
    (cf24EvalM E Ei w).size = 12 ∧ RowsWF (cf24EvalM E Ei w) := by
  induction w with
  | nil => exact ⟨idM_size' 12, RowsWF.idM 12⟩
  | cons l w ih =>
    have hl : (if l.2 then E l.1.val else Ei l.1.val).size = 12 ∧
        RowsWF (if l.2 then E l.1.val else Ei l.1.val) := by
      split_ifs
      · exact hE l.1
      · exact hEi l.1
    exact ⟨(cf24_mul_size 12 _ _).trans hl.1, RowsWF.mul _ 12 hl.2 ih.2⟩

theorem toMat_cf24EvalM (g : Fin gcS → GL (Fin 12) (ZMod 3))
    (hE : ∀ i : Fin gcS, (E i).size = 12 ∧ RowsWF (E i))
    (hEi : ∀ i : Fin gcS, (Ei i).size = 12 ∧ RowsWF (Ei i))
    (hg : ∀ i : Fin gcS, toMat 12 (E i.val) = ((g i : GL (Fin 12) (ZMod 3)) :
      Matrix (Fin 12) (Fin 12) (ZMod 3)))
    (hgi : ∀ i : Fin gcS, toMat 12 (Ei i.val) = (((g i)⁻¹ : GL (Fin 12) (ZMod 3)) :
      Matrix (Fin 12) (Fin 12) (ZMod 3)))
    (w : List (Fin gcS × Bool)) :
    toMat 12 (cf24EvalM E Ei w) = ((FreeGroup.lift g (FreeGroup.mk w) : GL (Fin 12) (ZMod 3)) :
      Matrix (Fin 12) (Fin 12) (ZMod 3)) := by
  induction w with
  | nil =>
    have : FreeGroup.mk ([] : List (Fin gcS × Bool)) = 1 := rfl
    rw [this, map_one, Units.val_one]
    exact toMat_idM 12
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have hl : (if b then E i.val else Ei i.val).size = 12 ∧
        RowsWF (if b then E i.val else Ei i.val) := by
      split_ifs
      · exact hE i
      · exact hEi i
    have hw := cf24EvalM_facts E Ei hE hEi w
    have hlet : toMat 12 (if b then E i.val else Ei i.val) =
        ((FreeGroup.lift g (FreeGroup.mk [(i, b)]) : GL (Fin 12) (ZMod 3)) :
          Matrix (Fin 12) (Fin 12) (ZMod 3)) := by
      cases b
      · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
          FreeGroup.lift_apply_of]
        exact hgi i
      · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
        exact hg i
    have e : FreeGroup.mk ((i, b) :: w) = FreeGroup.mk [(i, b)] * FreeGroup.mk w := rfl
    have hmul : toMat 12 (cf24EvalM E Ei ((i, b) :: w)) =
        toMat 12 (if b then E i.val else Ei i.val) * toMat 12 (cf24EvalM E Ei w) :=
      toMat_mul hl.1 hl.2 hw.2
    rw [hmul, ih, hlet, e, map_mul, Units.val_mul]

end Eval

theorem cf24_toMat_ne {d : ℕ} {X Y : Array V} (hX : X.size = d) (h : eqM d X Y = false) :
    canonM d X = true → canonM d Y = true → toMat d X ≠ toMat d Y := by
  intro hXc hYc he
  have := eq_of_canonM hXc hYc he
  subst this
  unfold eqM at h
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
  rcases h with (h | h) | h
  · exact h hX
  · exact h hX
  · rw [Nat.all_eq_finRange_all, List.all_eq_false] at h
    obtain ⟨i, -, hi⟩ := h
    simp [V.beq] at hi

theorem exists_hom_of_cf24MatCheckOf (E Ei : ℕ → Array V) (h : cf24MatCheckOf E Ei = true) :
    ∃ φ : SuzCover →* GL (Fin 12) (ZMod 3),
      φ suzZ = 1 ∧ φ (PresentedGroup.mk _ (FreeGroup.mk (suzW [6, 6]))) ≠ 1 ∧
        φ (PresentedGroup.mk _ (FreeGroup.mk cf24C)) ≠ 1 := by
  unfold cf24MatCheckOf at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hmats, hcov⟩, hZ⟩, hDc⟩, hDne⟩, hCc⟩, hCne⟩ := h
  have hE : ∀ i : Fin gcS, (E i.val).size = 12 ∧ RowsWF (E i.val) := fun i => by
    have := (hmats i.val i.isLt).1.1.1
    exact ⟨(canonM_spec this).1, RowsWF.of_canonM this⟩
  have hEi : ∀ i : Fin gcS, (Ei i.val).size = 12 ∧ RowsWF (Ei i.val) := fun i => by
    have := (hmats i.val i.isLt).1.1.2
    exact ⟨(canonM_spec this).1, RowsWF.of_canonM this⟩
  have hinv1 : ∀ i : Fin gcS, toMat 12 (E i.val) * toMat 12 (Ei i.val) = 1 := fun i => by
    rw [← toMat_mul (hE i).1 (hE i).2 (hEi i).2,
      toMat_eq_of_eqM (hmats i.val i.isLt).1.2, toMat_idM]
  have hinv2 : ∀ i : Fin gcS, toMat 12 (Ei i.val) * toMat 12 (E i.val) = 1 := fun i => by
    rw [← toMat_mul (hEi i).1 (hEi i).2 (hE i).2,
      toMat_eq_of_eqM (hmats i.val i.isLt).2, toMat_idM]
  let g : Fin gcS → GL (Fin 12) (ZMod 3) := fun i =>
    ⟨toMat 12 (E i.val), toMat 12 (Ei i.val), hinv1 i, hinv2 i⟩
  have hval := toMat_cf24EvalM E Ei g hE hEi (fun i => rfl) (fun i => rfl)
  have hrel : ∀ r ∈ coverRelators (wordSet R0) suzCommW, FreeGroup.lift g r = 1 := by
    intro r hr
    rw [coverRelators_suzCommW] at hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    apply Units.ext
    rw [← hval w, toMat_eq_of_eqM (hcov w hw), toMat_idM, Units.val_one]
  have hmk : ∀ w : List (Fin gcS × Bool), (PresentedGroup.toGroup hrel)
      (PresentedGroup.mk _ (FreeGroup.mk w)) = FreeGroup.lift g (FreeGroup.mk w) := fun w => rfl
  have hne : ∀ w : List (Fin gcS × Bool), canonM 12 (cf24EvalM E Ei w) = true →
      eqM 12 (cf24EvalM E Ei w) (idM 12) = false →
        (PresentedGroup.toGroup hrel) (PresentedGroup.mk _ (FreeGroup.mk w)) ≠ 1 := by
    intro w hc hn h1
    rw [hmk] at h1
    have h3 := congrArg (fun x : GL (Fin 12) (ZMod 3) =>
      (x : Matrix (Fin 12) (Fin 12) (ZMod 3))) h1
    simp only [Units.val_one] at h3
    exact cf24_toMat_ne (cf24EvalM_facts E Ei hE hEi w).1 hn hc (canonM_idM 12)
      (((hval w).trans h3).trans (toMat_idM 12).symm)
  refine ⟨PresentedGroup.toGroup hrel, ?_, hne _ hDc hDne, hne _ hCc hCne⟩
  rw [suzZ, hmk]
  apply Units.ext
  rw [← hval suzR3, toMat_eq_of_eqM hZ, toMat_idM, Units.val_one]

theorem exists_hom_of_cf24MatCheck :
    ∃ φ : SuzCover →* GL (Fin 12) (ZMod 3),
      φ suzZ = 1 ∧ φ (PresentedGroup.mk _ (FreeGroup.mk (suzW [6, 6]))) ≠ 1 ∧
        φ (PresentedGroup.mk _ (FreeGroup.mk cf24C)) ≠ 1 :=
  exists_hom_of_cf24MatCheckOf (fun i => cf24Es[i]!) (fun i => cf24Eis[i]!) cf24_mat_check

end CFSG.ComponentClassification.GSThmB.CF24
