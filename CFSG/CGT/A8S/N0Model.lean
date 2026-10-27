module

public import CFSG.CGT.A8S.N0Distinct
public import Certificates.Certificate21198

public section

namespace CFSG.CGT.A8S

open CFSG.CosetTable

namespace N0

@[expose] def n0Gen (i : Fin 5) : Equiv.Perm (Fin 8) := a8Perm (Fin.castSucc i)

theorem lift_mk_cons {α H : Type*} [Group H] (f : α → H) (a : α × Bool) (w : List (α × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (a :: w)) =
      cond a.2 (f a.1) (f a.1)⁻¹ * FreeGroup.lift f (FreeGroup.mk w) := by
  simp only [FreeGroup.lift_mk, List.map_cons, List.prod_cons]

theorem n0Gen_lin : ∀ (i : Fin 5) (b : Bool) (y : Fin 8), i.val < 2 →
    ((cond b (n0Gen i) (n0Gen i)⁻¹) y).val =
      applyC3 (if b then modelCols3 i.val else modelInv3 i.val) y.val := by
  decide +kernel

theorem n0Gen_tr : ∀ (i : Fin 5) (b : Bool) (y : Fin 8), ¬ i.val < 2 →
    ((cond b (n0Gen i) (n0Gen i)⁻¹) y).val = 1 <<< (i.val - 2) ^^^ y.val := by
  decide +kernel

theorem lift_n0Gen_apply (w : List (Fin 5 × Bool)) (x : Fin 8) :
    ((FreeGroup.lift n0Gen (FreeGroup.mk w)) x).val =
      (affEval w).1 ^^^ applyC3 (affEval w).2 x.val := by
  induction w with
  | nil =>
    rw [show FreeGroup.mk ([] : List (Fin 5 × Bool)) = 1 from rfl, map_one, affEval_nil,
      applyC3_idC3 x.isLt, Nat.zero_xor]
    rfl
  | cons a w ih =>
    rw [lift_mk_cons, Equiv.Perm.mul_apply, affEval_cons]
    obtain ⟨i, b⟩ := a
    by_cases h : i.val < 2
    · rw [n0Gen_lin i b _ h, ih]
      simp only [affStep, h, ite_true]
      rw [applyC3_xor, applyC3_compC3]
    · rw [n0Gen_tr i b _ h, ih]
      simp only [affStep, h, ite_false]
      rw [Nat.xor_assoc]

theorem lift_n0Gen_relsN0A8 : ∀ r ∈ {r : FreeGroup (Fin 5) | r ∈ relsN0A8.map FreeGroup.mk},
    FreeGroup.lift n0Gen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  refine Equiv.ext fun x => Fin.ext ?_
  rw [lift_n0Gen_apply, affEval_relsN0A8 w hw]
  exact (Nat.zero_xor _).trans (applyC3_idC3 x.isLt)

end N0

@[expose] def n0Perm : PG 5 relsN0A8 →* Equiv.Perm (Fin 8) :=
  PresentedGroup.toGroup N0.lift_n0Gen_relsN0A8

namespace N0

theorem n0Perm_mk (w : List (Fin 5 × Bool)) :
    n0Perm (PresentedGroup.mk _ (FreeGroup.mk w)) = FreeGroup.lift n0Gen (FreeGroup.mk w) := by
  have hcomp : (n0Perm : PG 5 relsN0A8 →* Equiv.Perm (Fin 8)).comp (PresentedGroup.mk _) =
      FreeGroup.lift n0Gen := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact PresentedGroup.toGroup.of _
  exact congrArg (fun f => f (FreeGroup.mk w)) hcomp

theorem n0Perm_mk_apply (w : List (Fin 5 × Bool)) (x : Fin 8) :
    (n0Perm (PresentedGroup.mk _ (FreeGroup.mk w)) x).val =
      (affEval w).1 ^^^ applyC3 (affEval w).2 x.val := by
  rw [n0Perm_mk, lift_n0Gen_apply]

theorem affEval_eq_of_n0Perm_eq {w w' : List (Fin 5 × Bool)}
    (h : n0Perm (PresentedGroup.mk _ (FreeGroup.mk w)) =
      n0Perm (PresentedGroup.mk _ (FreeGroup.mk w'))) :
    affEval w = affEval w' := by
  have hx : ∀ x : Fin 8, (affEval w).1 ^^^ applyC3 (affEval w).2 x.val =
      (affEval w').1 ^^^ applyC3 (affEval w').2 x.val := fun x => by
    rw [← n0Perm_mk_apply, ← n0Perm_mk_apply, h]
  have h0 := hx 0
  simp only [Fin.val_zero, applyC3_zero, Nat.xor_zero] at h0
  refine Prod.ext h0 (cols3_ext fun j => ?_)
  have hj := hx ⟨2 ^ j.val, by fin_cases j <;> decide⟩
  rw [h0] at hj
  exact Nat.xor_right_inj.1 hj

theorem mk_n0Word_injective :
    Function.Injective fun k : Fin 1344 =>
      (PresentedGroup.mk _ (FreeGroup.mk (n0Word k)) : PG 5 relsN0A8) := fun _ _ h =>
  affEval_n0Word_injective (affEval_eq_of_n0Perm_eq (congrArg n0Perm h))

theorem mk_n0Word_bijective [Finite (PG 5 relsN0A8)] (h : Nat.card (PG 5 relsN0A8) ≤ 1344) :
    Function.Bijective fun k : Fin 1344 =>
      (PresentedGroup.mk _ (FreeGroup.mk (n0Word k)) : PG 5 relsN0A8) :=
  mk_n0Word_injective.bijective_of_nat_card_le (by rw [Nat.card_fin]; exact h)

theorem n0_forall_of_card_le [Finite (PG 5 relsN0A8)] (h : Nat.card (PG 5 relsN0A8) ≤ 1344)
    (x : PG 5 relsN0A8) : ∃ k, x = PresentedGroup.mk _ (FreeGroup.mk (n0Word k)) := by
  obtain ⟨k, hk⟩ := (mk_n0Word_bijective h).2 x
  exact ⟨k, hk.symm⟩

end N0

theorem finite_pg_relsN0A8 : Finite (PG 5 relsN0A8) :=
  Certificates.certificate21198.1

theorem card_pg_relsN0A8 : Nat.card (PG 5 relsN0A8) = 1344 := by
  have := finite_pg_relsN0A8
  have hle := Certificates.certificate21198.2
  exact (Nat.card_congr (Equiv.ofBijective _ (N0.mk_n0Word_bijective hle))).symm.trans
    (Nat.card_fin 1344)

theorem n0_forall (x : PG 5 relsN0A8) :
    ∃ k, x = PresentedGroup.mk _ (FreeGroup.mk (n0Word k)) := by
  have := finite_pg_relsN0A8
  exact N0.n0_forall_of_card_le card_pg_relsN0A8.le x

theorem n0Perm_injective : Function.Injective n0Perm := by
  intro x y h
  obtain ⟨i, rfl⟩ := n0_forall x
  obtain ⟨j, rfl⟩ := n0_forall y
  rw [N0.affEval_n0Word_injective (N0.affEval_eq_of_n0Perm_eq h)]

end CFSG.CGT.A8S
