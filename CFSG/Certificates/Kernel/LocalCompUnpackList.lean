module

public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def bindListFromK (l : List Nat) (w P : Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => bAnd(Nat.beq x (pg w (mask w) P i), ih (Nat.succ i))) l

theorem bindListFromK_get {w P : Nat} : ∀ (l : List Nat) (i : Nat), bindListFromK l w P i = true →
    ∀ j (hj : j < l.length), l[j] = pg w (mask w) P (i + j)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | x :: l, i, h, j, hj => by
    have hc : bindListFromK (x :: l) w P i =
        bAnd(Nat.beq x (pg w (mask w) P i), bindListFromK l w P (Nat.succ i)) := rfl
    rw [hc, bAnd_iff] at h
    match j, hj with
    | 0, _ => exact Nat.eq_of_beq_eq_true h.1
    | j + 1, hj =>
      rw [List.getElem_cons_succ, bindListFromK_get l (Nat.succ i) h.2 j (by simpa using hj)]
      congr 1
      omega

theorem toArray_eq_of_bindListFromK {l : List Nat} {w P : Nat} (h : bindListFromK l w P 0 = true) :
    l.toArray = unpack l.length w P := by
  unfold unpack
  refine Array.ext (by simp) fun j hj _ => ?_
  rw [Array.getElem_ofFn, List.getElem_toArray, bindListFromK_get l 0 h j (by simpa using hj),
    Nat.zero_add]

end CFSG.KS.Raw

end
