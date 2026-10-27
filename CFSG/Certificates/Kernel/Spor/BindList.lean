module

public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def bindFromK (w P : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => bAnd(Nat.beq x (pg w (mask w) P i), ih (Nat.succ i))) l

@[expose] noncomputable def lenK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def bindListK (n w P : Nat) (l : List Nat) : Bool :=
  bAnd(Nat.beq (lenK l) n, bindFromK w P l (nat_lit 0))

theorem lenK_eq (l : List Nat) : lenK l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Nat.succ (lenK l) = (x :: l).length
    rw [ih, List.length_cons]

theorem bindFromK_spec {w P : Nat} : ∀ {l : List Nat} {i : Nat}, bindFromK w P l i = true →
    ∀ j (h : j < l.length), l[j] = pg w (mask w) P (i + j)
  | [], _, _, j, h => absurd h (Nat.not_lt_zero j)
  | x :: l, i, hb, j, h => by
    have hb' : Bool.rec (motive := fun _ => Bool) false (bindFromK w P l (Nat.succ i))
        (Nat.beq x (pg w (mask w) P i)) = true := hb
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hb'
    rcases j with _ | j
    · rw [Nat.add_zero]
      exact Nat.eq_of_beq_eq_true h1
    · have := bindFromK_spec h2 j (by simpa using h)
      rw [List.getElem_cons_succ, this, Nat.succ_add, Nat.add_succ]

theorem toArray_eq_of_bindListK {n w P : Nat} {l : List Nat} (h : bindListK n w P l = true) :
    l.toArray = unpack n w P := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hl : l.length = n := by rw [← lenK_eq]; exact Nat.eq_of_beq_eq_true h1
  apply Array.ext
  · simp [unpack, hl]
  · intro i hi1 _
    rw [List.getElem_toArray, bindFromK_spec h2 i (by simpa using hi1), Nat.zero_add]
    simp [unpack]

end CFSG.KS.Raw

end
