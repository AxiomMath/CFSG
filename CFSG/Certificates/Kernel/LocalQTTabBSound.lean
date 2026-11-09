module

public import Certificates.Data.Kernel.LocalQT.LatE
public import CFSG.Certificates.Kernel.LocalQTLatKSound
public import CFSG.Certificates.Kernel.LocalQTCovEqns

public section

namespace CFSG.KC.LQT.L

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.S
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

@[expose] noncomputable def blkW (BT : List (List Nat)) (ix : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun j _ ih => List.append (CFSG.KC.LQT.Syl.getK BT j []) ih) ix

@[expose] noncomputable def evalBL (n : Nat) (BV : List Nat) (ix : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (one n)
    (fun j _ ih => mul n (CFSG.KC.LQT.Syl.getK BV j (one n)) ih) ix

@[expose] noncomputable def tabV (n : Nat) (D : List Lvl) (T : List (List Nat)) (V : List Nat)
    (L : Nat) : Bool :=
  andB (allA T fun w => Nat.ble (lenA w) L)
    (Nat.beq (List.rec (motive := fun _ => Nat) 0
        (fun v _ acc => Nat.lor (Nat.shiftLeft 1 (idxM n D (chainF D) v)) acc) V)
      (Nat.sub (Nat.shiftLeft 1 (chainF D)) 1))

@[expose] noncomputable def wordsTF (n : Nat) (C : List Lvl) (G : List Nat)
    (W : List (List (List Nat))) (k : Nat) (tab : List Lvl → Bool) (L d : Nat) : Bool :=
  List.rec (motive := fun _ => List (List (List Nat)) → Nat → Nat → Bool) (fun _ _ _ => true)
    (fun lv C' ih W budget k => Bool.rec (motive := fun _ => Bool)
      (List.rec (motive := fun _ => Bool) false
        (fun ws W' _ => andB
          (allN n fun j => impB (notB (Nat.beq (getK lv.2.1 j) 0))
            (Nat.beq (evalWK n G (CFSG.KC.LQT.M.getW ws j)) (getK lv.2.1 j)))
          (letB (Nat.rec (motive := fun _ => Nat) 0 (fun j m => Bool.rec (motive := fun _ => Nat) m
              (lenA (CFSG.KC.LQT.M.getW ws j)) (Nat.blt m (lenA (CFSG.KC.LQT.M.getW ws j)))) n)
            fun len => andB (Nat.ble len budget) (ih W' (Nat.sub budget len) (Nat.sub k 1))))
        W)
      (andB (Nat.ble L budget) (tab (List.cons lv C')))
      (Nat.beq k 0))
    C W d k

theorem wordsT_eq_F (n : Nat) (C : List Lvl) (G : List Nat) (W : List (List (List Nat))) (k : Nat)
    (T : List (List Nat)) (L d : Nat) :
    wordsT n C G W k T L d = wordsTF n C G W k (fun D => tabOK n D G T L) L d := rfl

theorem recLor_map {α β : Type} (g : β → Nat) (e : α → β) (T : List α) :
    List.rec (motive := fun _ => Nat) 0 (fun w _ acc => Nat.lor (g (e w)) acc) T =
      List.rec (motive := fun _ => Nat) 0 (fun v _ acc => Nat.lor (g v) acc) (T.map e) := by
  induction T with
  | nil => rfl
  | cons w T ih => exact congrArg (Nat.lor (g (e w))) ih

theorem tabOK_eq_tabV (n : Nat) (D : List Lvl) (G : List Nat) (T : List (List Nat)) (L : Nat) :
    tabOK n D G T L = tabV n D T (T.map (evalWK n G)) L :=
  congrArg (fun x => andB (allA T fun w => Nat.ble (lenA w) L)
      (Nat.beq x (Nat.sub (Nat.shiftLeft 1 (chainF D)) 1)))
    (recLor_map (fun v => Nat.shiftLeft 1 (idxM n D (chainF D) v)) (evalWK n G) T)

theorem evalW_app {n : ℕ} (A : List (Perm (Fin n))) (a b : List ℕ) :
    evalW A (a ++ b) = evalW A a * evalW A b := by
  induction a with
  | nil => simp only [List.nil_append, evalW, one_mul]
  | cons i a ih => simp only [List.cons_append, evalW, ih, mul_assoc]

theorem evalWK_app {n : ℕ} (hn : n ≤ 32) (A : List (Perm (Fin n))) (a b : List ℕ) :
    evalWK n (A.map P.code) (a ++ b) =
      mul n (evalWK n (A.map P.code) a) (evalWK n (A.map P.code) b) := by
  rw [LK.evalWK_code hn, LK.evalWK_code hn, LK.evalWK_code hn, evalW_app, P.code_mul hn]

theorem getK_map {α β : Type} (f : α → β) (l : List α) (j : ℕ) (d : α) :
    CFSG.KC.LQT.Syl.getK (l.map f) j (f d) = f (CFSG.KC.LQT.Syl.getK l j d) := by
  induction l generalizing j with
  | nil => rfl
  | cons x l ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

theorem evalBL_eq {n : ℕ} (hn : n ≤ 32) (A : List (Perm (Fin n))) (BT : List (List ℕ))
    (ix : List ℕ) :
    evalWK n (A.map P.code) (blkW BT ix) = evalBL n (BT.map (evalWK n (A.map P.code))) ix := by
  induction ix with
  | nil => rfl
  | cons j ix ih =>
    change evalWK n (A.map P.code) (CFSG.KC.LQT.Syl.getK BT j [] ++ blkW BT ix) =
      mul n (CFSG.KC.LQT.Syl.getK (BT.map (evalWK n (A.map P.code))) j
        (evalWK n (A.map P.code) [])) (evalBL n (BT.map (evalWK n (A.map P.code))) ix)
    rw [evalWK_app hn, ih, getK_map]

theorem tabOK_blk {n : ℕ} (hn : n ≤ 32) (A : List (Perm (Fin n))) {D : List Lvl} {L : ℕ}
    {BT : List (List ℕ)} {IX : List (List ℕ)} {BV : List ℕ} {T : List (List ℕ)}
    (hT : T = IX.map (blkW BT))
    (hV : CFSG.KC.LQT.Syl.eqL BV (BT.map (evalWK n (A.map P.code))) = true) :
    tabOK n D (A.map P.code) T L = tabV n D T (IX.map (evalBL n BV)) L := by
  rw [tabOK_eq_tabV, (CFSG.KC.LQT.Cov.Eqns.eqL_iff _ _).1 hV]
  congr 1
  rw [hT, List.map_map]
  exact List.map_congr_left fun ix _ => evalBL_eq hn A BT ix

end CFSG.KC.LQT.L

end
