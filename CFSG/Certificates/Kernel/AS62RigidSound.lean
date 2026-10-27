module

public import Certificates.Data.Kernel.AS62RigidK
public import CFSG.LargeExtraspecial.AS62C36RigidInputs
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

namespace CFSG.KC.AS62

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.LargeExtraspecial.AS62.Rigid

abbrev Cn (p : Nat) : Prop := canonK 45 6 (mask 6) (45 * 6) p = true

theorem unpack_size45 (P : Nat) : (unpack 45 6 P).size = 45 := by
  simp [unpack]

theorem getD_eq_get! (a : Array Nat) (j : Nat) : a.getD j 0 = a[j]! := by
  by_cases h : j < a.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, getElem!_pos a j h]
    rfl
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simp [getElem!_def, Array.getElem?_eq_none (show a.size ≤ j by omega)]

theorem cmpA_eq (a b : Array Nat) (hb : b.size = 45) :
    cmpA a b = CFSG.Monster.B.Co2.Native.compA 45 a b := by
  apply Array.ext
  · simp [cmpA, CFSG.Monster.B.Co2.Native.compA, hb]
  · intro i h1 h2
    simp only [cmpA, Array.getElem_map, CFSG.Monster.B.Co2.Native.compA, Array.getElem_ofFn]
    rw [getD_eq_get!, getElem!_pos b i (by simp [cmpA] at h1; exact h1)]

theorem cmpA_unpack {p q : Nat} (hp : Cn p) (hq : Cn q) :
    cmpA (unpack 45 6 p) (unpack 45 6 q) = unpack 45 6 (pc p q) := by
  rw [cmpA_eq _ _ (unpack_size45 q)]
  exact compA_unpack hp hq

theorem cn_pc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) := canonK_pcomp hp hq

theorem idA_unpack (h : idK 45 6 (mask 6) = true) : idA = unpack 45 6 PID := by
  unfold PID
  rw [idK_sound h]
  apply Array.ext
  · simp [idA, CFSG.Monster.B.Co2.Native.idA]
  · intro i h1 h2
    simp [idA, CFSG.Monster.B.Co2.Native.idA]

theorem eqA_self' (t : Array Nat) : CFSG.Monster.B.Co2.Native.eqA 45 t t = true := by
  unfold CFSG.Monster.B.Co2.Native.eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  simp

theorem beq_unpack {p q : Nat} (hp : Cn p) (hq : Cn q) :
    (unpack 45 6 p == unpack 45 6 q) = Nat.beq p q := by
  cases h : Nat.beq p q
  · cases hb : (unpack 45 6 p == unpack 45 6 q)
    · rfl
    · exfalso
      have e : unpack 45 6 p = unpack 45 6 q := eq_of_beq hb
      have h1 := eqA_unpack hp hq
      rw [e, eqA_self', h] at h1
      exact Bool.false_ne_true h1.symm
  · rw [Nat.eq_of_beq_eq_true h]
    exact beq_self_eq_true _

theorem cn_codeW {k : Nat} {E EI : Nat → Nat} {code : Fin k → Nat} (hid : Cn PID)
    (hE : ∀ l, Cn (E (code l)) ∧ Cn (EI (code l))) :
    ∀ w : List (Fin k × Bool), Cn (codeW E EI code w)
  | [] => hid
  | l :: w => by
    change Cn (pc (Bool.rec (motive := fun _ => Nat) (EI (code l.1)) (E (code l.1)) l.2)
      (codeW E EI code w))
    refine cn_pc ?_ (cn_codeW hid hE w)
    cases l.2
    · exact (hE l.1).2
    · exact (hE l.1).1

theorem evalA_eq {k : Nat} {L : Fin k × Bool → Array Nat} {E EI : Nat → Nat} {code : Fin k → Nat}
    (hid : idK 45 6 (mask 6) = true) (hidc : Cn PID)
    (hE : ∀ l, Cn (E (code l)) ∧ Cn (EI (code l)))
    (hL : ∀ a, L a = unpack 45 6 (Bool.rec (motive := fun _ => Nat) (EI (code a.1)) (E (code a.1))
      a.2)) :
    ∀ w : List (Fin k × Bool), evalA L w = unpack 45 6 (codeW E EI code w)
  | [] => idA_unpack hid
  | a :: w => by
    change cmpA (L a) (evalA L w) = unpack 45 6 (pc (Bool.rec (motive := fun _ => Nat)
      (EI (code a.1)) (E (code a.1)) a.2) (codeW E EI code w))
    have ha : Cn (Bool.rec (motive := fun _ => Nat) (EI (code a.1)) (E (code a.1)) a.2) := by
      cases a.2
      · exact (hE a.1).2
      · exact (hE a.1).1
    rw [hL a, evalA_eq hid hidc hE hL w]
    exact cmpA_unpack ha (cn_codeW hidc hE w)

theorem relOK_eq {k : Nat} {g : Fin k → Array Nat × Array Nat} {E EI : Nat → Nat}
    (hid : idK 45 6 (mask 6) = true) (hidc : Cn PID)
    (hE : ∀ l, Cn (E l) ∧ Cn (EI l))
    (hg : ∀ i, g i = (unpack 45 6 (E i.val), unpack 45 6 (EI i.val)))
    (w : List (Fin k × Bool)) :
    (evalA (fun a => if a.2 then (g a.1).1 else (g a.1).2) w == idA) = relK E EI w := by
  have hL : ∀ a : Fin k × Bool, (if a.2 then (g a.1).1 else (g a.1).2) =
      unpack 45 6 (Bool.rec (motive := fun _ => Nat) (EI (a.1.val)) (E (a.1.val)) a.2) := by
    intro a
    rw [hg a.1]
    cases a.2 <;> rfl
  rw [evalA_eq (code := fun i => i.val) hid hidc (fun l => hE l.val) hL w, idA_unpack hid,
    beq_unpack (cn_codeW hidc (fun l => hE l.val) w) hidc]
  rfl

theorem relK_congr {k : Nat} {E EI E' EI' : Nat → Nat} :
    ∀ w : List (Fin k × Bool), (∀ l ∈ w, E l.1.val = E' l.1.val ∧ EI l.1.val = EI' l.1.val) →
      evalK E EI w = evalK E' EI' w
  | [], _ => rfl
  | l :: w, h => by
    have ih := relK_congr w fun l' hl' => h l' (List.mem_cons_of_mem l hl')
    have hl := h l List.mem_cons_self
    change pc (Bool.rec (motive := fun _ => Nat) (EI l.1.val) (E l.1.val) l.2) (evalK E EI w) =
      pc (Bool.rec (motive := fun _ => Nat) (EI' l.1.val) (E' l.1.val) l.2) (evalK E' EI' w)
    rw [ih, hl.1, hl.2]

theorem cn_tup5 {a b c d e : Nat} (ha : Cn a) (hb : Cn b) (hc : Cn c) (hd : Cn d) (he : Cn e) :
    ∀ l, Cn (tup5 a b c d e l) := by
  intro l
  unfold tup5
  cases Nat.beq l 0
  · cases Nat.beq l 1
    · cases Nat.beq l 2
      · cases Nat.beq l 3
        · exact he
        · exact hd
      · exact hc
    · exact hb
  · exact ha

theorem notMemK_sound {x : Nat} : ∀ {L : List Nat}, notMemK x L = true → x ∉ L
  | [], _ => by simp
  | y :: L, h => by
    change bIf(Nat.beq y x, false, notMemK x L) = true at h
    cases hb : Nat.beq y x
    · rw [hb] at h
      intro hm
      rcases List.mem_cons.1 hm with rfl | hm
      · rw [Nat.beq_refl] at hb
        exact Bool.false_ne_true hb.symm
      · exact notMemK_sound h hm
    · rw [hb] at h
      exact absurd h Bool.false_ne_true

theorem nodupK_sound : ∀ {L : List Nat}, nodupK L = true → L.Nodup
  | [], _ => List.nodup_nil
  | x :: L, h => by
    change bAnd(notMemK x L, nodupK L) = true at h
    cases hb : notMemK x L
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    · rw [hb] at h
      exact List.nodup_cons.2 ⟨notMemK_sound hb, nodupK_sound h⟩

theorem bitK_beqB {x y : Bool} (h : beqB x y = true) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h Bool.false_ne_true

end CFSG.KC.AS62

end
