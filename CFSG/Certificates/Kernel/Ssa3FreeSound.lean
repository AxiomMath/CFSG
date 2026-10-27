module

public import Certificates.Data.Kernel.Ssa3Free
public import CFSG.Certificates.Kernel.Ssa3Sound

public section

namespace CFSG.KC.Ssa3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

variable {d : Nat}

@[expose] noncomputable def atomsM (M : Nat → Matrix (Fin d) (Fin d) (ZMod 3))
    (l : List (Nat × Nat)) : Matrix (Fin d) (Fin d) (ZMod 3) :=
  (l.map fun p => M p.1 ^ p.2).prod

theorem atomsM_nil (M : Nat → Matrix (Fin d) (Fin d) (ZMod 3)) : atomsM M [] = 1 := rfl

theorem atomsM_cons (M : Nat → Matrix (Fin d) (Fin d) (ZMod 3)) (z e : Nat)
    (l : List (Nat × Nat)) : atomsM M ((z, e) :: l) = M z ^ e * atomsM M l := rfl

theorem atomsM_append (M : Nat → Matrix (Fin d) (Fin d) (ZMod 3)) (l m : List (Nat × Nat)) :
    atomsM M (l ++ m) = atomsM M l * atomsM M m := by
  simp [atomsM, List.map_append, List.prod_append]

theorem atomsM_powL (M : Nat → Matrix (Fin d) (Fin d) (ZMod 3)) (e : Nat)
    (l : List (Nat × Nat)) : atomsM M (powL e l) = atomsM M l ^ e := by
  have hrep : ∀ m : List (Nat × Nat), atomsM M (List.replicate e m).flatten = atomsM M m ^ e := by
    intro m
    induction e with
    | zero => rfl
    | succ e ih => rw [List.replicate_succ, List.flatten_cons, atomsM_append, ih, pow_succ']
  match l with
  | [(z, k)] =>
    simp only [powL, atomsM_cons, atomsM_nil, mul_one]
    rw [pow_mul]
  | [] => exact hrep []
  | a :: b :: r => exact hrep (a :: b :: r)

theorem exS_sound (A B : Matrix (Fin d) (Fin d) (ZMod 3)) (D : SData) (C : List Nat) :
    ∀ f x, atomsM (val A B D) (exS D C f x) = val A B D x := by
  intro f
  induction f with
  | zero => intro x; simp [exS, atomsM]
  | succ f ih =>
    intro x
    simp only [exS]
    by_cases hc : (Nat.blt x 2 || memS x C) = true
    · rw [hc]
      simp [atomsM]
    rw [Bool.not_eq_true] at hc
    rw [hc, cond_false]
    simp only [Bool.or_eq_false_iff] at hc
    have hx2 : ¬ x < 2 := fun h => by
      have h' : Nat.blt x 2 = true := by rw [Nat.blt_eq]; exact h
      rw [hc.1] at h'
      exact Bool.false_ne_true h'
    by_cases h2 : x = 2
    · subst h2
      simp [atomsM, val]
    have h2' : Nat.beq x 2 = false := Bool.eq_false_iff.2 fun h => h2 (Nat.eq_of_beq_eq_true h)
    rw [h2', cond_false]
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 3 := ⟨x - 3, by omega⟩
    have hy : y + 3 - 3 = y := by omega
    rw [hy, val.eq_4]
    by_cases hg : D.na.getD y 0 < y + 3 ∧ D.nb.getD y 0 < y + 3
    · have ha : Nat.blt (D.na.getD y 0) (y + 3) = true := by rw [Nat.blt_eq]; exact hg.1
      have hb : Nat.blt (D.nb.getD y 0) (y + 3) = true := by rw [Nat.blt_eq]; exact hg.2
      rw [ha, hb, Bool.and_true, cond_true, dif_pos hg]
      by_cases hk : D.nk.getD y 1 = 0
      · have hk' : Nat.beq (D.nk.getD y 1) 0 = true := by rw [hk]; rfl
        rw [hk', if_pos hk, cond_true]
        simp only [atomsM_append, ih]
      · have hk' : Nat.beq (D.nk.getD y 1) 0 = false :=
          Bool.eq_false_iff.2 fun h => hk (Nat.eq_of_beq_eq_true h)
        rw [hk', if_neg hk, cond_false, atomsM_powL, ih]
    · have hg' : (Nat.blt (D.na.getD y 0) (y + 3) && Nat.blt (D.nb.getD y 0) (y + 3)) = false :=
        Bool.eq_false_iff.2 fun h => by
          rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h
          exact hg h
      rw [hg', cond_false, dif_neg hg]
      rfl

theorem atomsM_consM (M : Nat → Matrix (Fin d) (Fin d) (ZMod 3)) (z e : Nat)
    (l : List (Nat × Nat)) : atomsM M (consM z e l) = M z ^ e * atomsM M l := by
  match l with
  | [] => rfl
  | (y, k) :: r =>
    simp only [consM]
    by_cases h : z = y
    · subst h
      simp only [Nat.beq_refl, cond_true, atomsM_cons]
      rw [pow_add, mul_assoc]
    · have h' : Nat.beq z y = false := Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)
      rw [h']
      rfl

theorem atomsM_mergeS (M : Nat → Matrix (Fin d) (Fin d) (ZMod 3)) :
    ∀ l : List (Nat × Nat), atomsM M (mergeS l) = atomsM M l
  | [] => rfl
  | (z, e) :: l => by
    simp only [mergeS]
    by_cases h : e = 0
    · subst h
      simp only [Nat.beq_refl, cond_true, atomsM_cons, pow_zero, one_mul]
      exact atomsM_mergeS M l
    · have h' : Nat.beq e 0 = false := Bool.eq_false_iff.2 fun e' => h (Nat.eq_of_beq_eq_true e')
      rw [h', cond_false, atomsM_consM, atomsM_mergeS M l, atomsM_cons]

theorem atomsM_wexS (A B : Matrix (Fin d) (Fin d) (ZMod 3)) (D : SData) (C : List Nat)
    (f : Nat) : ∀ w : Word, atomsM (val A B D) (wexS D C f w) = evalM (val A B D) D w
  | [] => rfl
  | (r, e) :: w => by
    simp only [wexS]
    rw [atomsM_append, atomsM_powL, exS_sound, atomsM_wexS A B D C f w]
    simp [evalM]

theorem eqL_true : ∀ {l m : List (Nat × Nat)}, eqL l m = true → l = m
  | [], [], _ => rfl
  | (a, b) :: l, (c, e) :: m, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, eqL_true h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

theorem evalM_of_freeS {A B : Matrix (Fin d) (Fin d) (ZMod 3)} {D : SData} {f : Nat}
    {w₁ w₂ : Word} (h : freeS D f w₁ w₂ = true) :
    evalM (val A B D) D w₁ = evalM (val A B D) D w₂ := by
  unfold freeS at h
  have e := congrArg (atomsM (val A B D)) (eqL_true h)
  rwa [atomsM_mergeS, atomsM_mergeS, atomsM_wexS, atomsM_wexS] at e

theorem factM_of_freeF {A B : Matrix (Fin d) (Fin d) (ZMod 3)} {D : SData} {n f : Nat}
    {q : MFact} (h : freeF D n f q = true) : factM (val A B D) D n q := by
  match q, h with
  | .eq w₁ w₂, h =>
    simp only [freeF, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, evalM_of_freeS h.2⟩

theorem factM_of_cover {A B : Matrix (Fin d) (Fin d) (ZMod 3)} {D : SData} {n f : Nat}
    {facts : List MFact} (hs : structS D = true) (hq : cmpsS D n facts = true)
    (hm : ∀ q < D.qk.length, cmpM (val A B D) D q) (hc : coverS D n f facts = true) :
    ∀ g ∈ facts, factM (val A B D) D n g := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hgi : facts.getD i (.eq [] []) = facts[i] := by
    rw [List.getD_eq_getElem _ _ hi]
  unfold coverS at hc
  have hci := List.all_eq_true.1 hc i (List.mem_range.2 hi)
  rw [Bool.or_eq_true, hgi] at hci
  rcases hci with hci | hci
  swap
  · exact factM_of_freeF hci
  obtain ⟨q, hqm, hqi⟩ := List.any_eq_true.1 hci
  have hql := List.mem_range.1 hqm
  have hqi' := Nat.eq_of_beq_eq_true hqi
  unfold cmpsS at hq
  have hqq := List.all_eq_true.1 hq q (List.mem_range.2 hql)
  rw [Bool.and_eq_true, hqi', hgi] at hqq
  exact factM_of_cmp hs hqq.2 (hm q hql)

end CFSG.KC.Ssa3

end
