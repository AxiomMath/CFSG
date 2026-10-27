module

public import Certificates.Data.Kernel.PermPinK
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KC.PermPinK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin

theorem memK_spec {N : Nat} {T : Nat → Nat} {x : Nat} (h : memK N T x = true) :
    ∃ j < N, x = T j := by
  unfold memK at h
  by_contra hne
  have hall : allN N (fun j => Bool.rec (motive := fun _ => Bool) true false (Nat.beq x (T j))) =
      true := allN_intro fun j hj => by
    cases e : Nat.beq x (T j)
    · rfl
    · exact absurd ⟨j, hj, Nat.eq_of_beq_eq_true e⟩ hne
  rw [hall] at h
  exact Bool.false_ne_true h

theorem fixK_eq {n w : Nat} {ps : List Nat} (hps : ∀ p ∈ ps, p < n) (P : Nat) :
    fixK w ps P = ps.all (fun p => (unpack n w P)[p]! == p) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.all_cons, ← ih fun q hq => hps q (List.mem_cons_of_mem p hq),
      unpack_get' (hps p List.mem_cons_self)]
    change Bool.rec (motive := fun _ => Bool) false (fixK w ps P) (Nat.beq (pg w (mask w) P p) p) =
      ((pg w (mask w) P p == p) && fixK w ps P)
    by_cases hp : pg w (mask w) P p = p
    · rw [hp, Nat.beq_refl, beq_self_eq_true, Bool.true_and]
    · have e1 : Nat.beq (pg w (mask w) P p) p = false := by
        cases e : Nat.beq (pg w (mask w) P p) p
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hp
      rw [e1, beq_false_of_ne hp, Bool.false_and]

theorem stabK_spec {n w : Nat} {ps : List Nat} {N : Nat} {T : Nat → Nat} {t : Nat}
    (h : stabK n w ps N T t = true) :
    ∀ k < N, fixK w ps (T k) = false ∨ T k = pidn n w ∨ T k = t := by
  intro k hk
  unfold stabK at h
  rw [strictB_app] at h
  have h1 := allN_spec h k hk
  rw [strictB_app] at h1
  cases e1 : fixK w ps (T k)
  · exact Or.inl rfl
  · rw [e1] at h1
    cases e2 : Nat.beq (T k) (pidn n w)
    · rw [e2] at h1
      exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h1))
    · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true e2))

theorem centCnt_eq (n w N : Nat) (T : Nat → Nat) (t : Nat) :
    centCnt n w N T t = ((List.range N).filter fun j =>
      Nat.beq (pcomp n w (mask w) (T j) t) (pcomp n w (mask w) t (T j))).length := by
  unfold centCnt
  rw [CFSG.KC.Pack.foldN_eq]
  generalize List.range N = L
  induction L with
  | nil => rfl
  | cons j L ih =>
    rw [List.foldr_cons, ih, strictN_app, List.filter_cons]
    cases Nat.beq (pcomp n w (mask w) (T j) t) (pcomp n w (mask w) t (T j)) <;> rfl

end CFSG.KC.PermPinK

end
