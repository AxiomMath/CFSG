module

public import CFSG.CGT.A8S.R3Check
public import CFSG.CGT.A8S.N0Model

public section

namespace CFSG.CGT.A8S.R3

open CFSG.CosetTable N0

@[expose] def n0v (w : List (Fin 5 × Bool)) : PG 5 relsN0A8 :=
  PresentedGroup.mk _ (FreeGroup.mk w)

theorem n0v_nil : n0v [] = 1 := rfl

theorem n0v_append (w w' : List (Fin 5 × Bool)) : n0v (w ++ w') = n0v w * n0v w' := by
  rw [n0v, n0v, n0v, ← FreeGroup.mul_mk, map_mul]

theorem n0v_invRev (w : List (Fin 5 × Bool)) : n0v (FreeGroup.invRev w) = (n0v w)⁻¹ := by
  rw [n0v, n0v, ← FreeGroup.inv_mk, map_inv]

@[expose] def AffRep (x : PG 5 relsN0A8) (p : ℕ × Cols3) : Prop :=
  ∀ y : Fin 8, (n0Perm x y).val = p.1 ^^^ applyC3 p.2 y.val

theorem affRep_n0v (w : List (Fin 5 × Bool)) : AffRep (n0v w) (affEval w) := n0Perm_mk_apply w

theorem AffRep.mul {x x' : PG 5 relsN0A8} {p p' : ℕ × Cols3} (h : AffRep x p) (h' : AffRep x' p') :
    AffRep (x * x') (affMul p p') := by
  intro y
  rw [map_mul, Equiv.Perm.mul_apply, h, h', affMul, applyC3_xor, applyC3_compC3, Nat.xor_assoc]

theorem AffRep.unique {x : PG 5 relsN0A8} {p q : ℕ × Cols3} (h : AffRep x p) (h' : AffRep x q) :
    p = q := by
  have hx : ∀ y : Fin 8, p.1 ^^^ applyC3 p.2 y.val = q.1 ^^^ applyC3 q.2 y.val := fun y => by
    rw [← h, ← h']
  have h0 := hx 0
  simp only [Fin.val_zero, applyC3_zero, Nat.xor_zero] at h0
  refine Prod.ext h0 (cols3_ext fun j => ?_)
  have hj := hx ⟨2 ^ j.val, by fin_cases j <;> decide⟩
  rw [h0] at hj
  exact Nat.xor_right_inj.1 hj

theorem AffRep.eq {x x' : PG 5 relsN0A8} {p : ℕ × Cols3}
    (h : AffRep x p) (h' : AffRep x' p) : x = x' :=
  n0Perm_injective (Equiv.ext fun y => Fin.ext ((h y).trans (h' y).symm))

theorem n0v_eq_of_affBEq {w w' : List (Fin 5 × Bool)}
    (h : affBEq (affEval w) (affEval w') = true) : n0v w = n0v w' :=
  (affRep_n0v w).eq (eq_of_affBEq h ▸ affRep_n0v w')

theorem n0v_ne_of_affBEq {w w' : List (Fin 5 × Bool)}
    (h : affBEq (affEval w) (affEval w') = false) : n0v w ≠ n0v w' := by
  intro e
  have hr : AffRep (n0v w) (affEval w') := e ▸ affRep_n0v w'
  rw [(affRep_n0v w).unique hr, affBEq_self] at h
  exact Bool.noConfusion h

theorem eq_of_conj_eq (x : PG 5 relsN0A8)
    (hx : ∀ j, x⁻¹ * n0v (yW j) * x = n0v (fW j)) :
    x = n0v wW ∨ ∃ k, x = n0v (wrongW k) := by
  obtain ⟨k, rfl⟩ := n0_forall x
  change n0v (n0Word k) = n0v wW ∨ ∃ k', n0v (n0Word k) = n0v (wrongW k')
  change ∀ j, (n0v (n0Word k))⁻¹ * n0v (yW j) * n0v (n0Word k) = n0v (fW j) at hx
  have hrep := affRep_n0v (n0Word k)
  have hin : inWAff (affEval (n0Word k)) = true := by
    refine List.all_eq_true.2 fun j _ => ?_
    have hc : n0v (yW j) * n0v (n0Word k) = n0v (n0Word k) * n0v (fW j) := by
      rw [← hx j]
      group
    have hr : AffRep (n0v (yW j) * n0v (n0Word k)) (affMul (affEval (n0Word k)) (affEval (fW j))) :=
      hc ▸ hrep.mul (affRep_n0v (fW j))
    rw [((affRep_n0v (yW j)).mul hrep).unique hr]
    exact affBEq_self _
  have hk : k.val < wordCodes.length := by rw [length_wordCodes]; exact k.isLt
  have hall := List.all_eq_true.1 wCheck_eq_true _ (List.getElem_mem hk)
  rw [← n0Word_eq k, hin, Bool.not_true, Bool.false_or] at hall
  simp only [candAff, Bool.or_eq_true, List.any_eq_true] at hall
  rcases hall with h | ⟨k', -, h'⟩
  · exact Or.inl (hrep.eq (eq_of_affBEq h ▸ affRep_n0v wW))
  · exact Or.inr ⟨k', hrep.eq (eq_of_affBEq h' ▸ affRep_n0v (wrongW k'))⟩

end CFSG.CGT.A8S.R3
