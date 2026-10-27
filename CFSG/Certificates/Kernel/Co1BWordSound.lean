module

public import Certificates.Data.Kernel.Co1BW
public import CFSG.Certificates.Kernel.Co1BMulSound

public section

namespace CFSG.KC.Co1B

open CFSG.KC.Loop CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.Sporadic.SmallF2.Native

theorem mulWK_unpack (A B : Nat) : mulRows 24 (unpackR 24 A) (unpackR 24 B) = unpackR 24 (mulWK A B) :=
  mulRows_unpackW 24 A B

theorem foldl_wordAB {XA XB : Array Nat} {A B : Nat} (hA : XA = unpackR 24 A) (hB : XB = unpackR 24 B) :
    ∀ (w : List Bool) (acc : Nat),
      w.foldl (fun acc b => mulRows 24 acc (if b then XA else XB)) (unpackR 24 acc) =
        unpackR 24 (wordABFrom A B w acc)
  | [], _ => rfl
  | b :: w, acc => by
    rw [List.foldl_cons]
    have : mulRows 24 (unpackR 24 acc) (if b then XA else XB) =
        unpackR 24 (mulWK acc (Bool.rec (motive := fun _ => Nat) B A b)) := by
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hB, mulWK_unpack]
      · simp only [↓reduceIte]
        rw [hA, mulWK_unpack]
    rw [this, foldl_wordAB hA hB w]
    change _ = unpackR 24 (strictN (mulWK acc (Bool.rec (motive := fun _ => Nat) B A b)) _)
    rw [strictN_eq]
    rfl

theorem foldl_gword {G : Array (Array Nat)} {Gk : List Nat}
    (hG : ∀ l < Gk.length, G[l]! = unpackR 24 (getL 0 Gk l)) :
    ∀ (w : List Nat), (∀ l ∈ w, l < Gk.length) → ∀ acc : Nat,
      w.foldl (fun acc l => mulRows 24 acc G[l]!) (unpackR 24 acc) = unpackR 24 (gwordFrom Gk w acc)
  | [], _, _ => rfl
  | l :: w, hw, acc => by
    rw [List.foldl_cons, hG l (hw l List.mem_cons_self), mulWK_unpack,
      foldl_gword hG w (fun l hl => hw l (List.mem_cons_of_mem _ hl))]
    change _ = unpackR 24 (strictN (mulWK acc (getL 0 Gk l)) _)
    rw [strictN_eq]
    rfl

theorem genWordRows_eq {G : Array (Array Nat)} {Gk : List Nat}
    (hG : ∀ l < Gk.length, G[l]! = unpackR 24 (getL 0 Gk l)) {w : List Nat}
    (hw : ∀ l ∈ w, l < Gk.length) (hone : idRows 24 = unpackR 24 oneK) :
    CFSG.Sporadic.Co1.InvNative.genWordRows G w = unpackR 24 (gwordFrom Gk w oneK) := by
  rw [CFSG.Sporadic.Co1.InvNative.genWordRows, hone]
  exact foldl_gword hG w hw oneK

theorem powRows_eq (M : Nat) (hone : idRows 24 = unpackR 24 oneK) :
    ∀ e : Nat, powRows 24 (unpackR 24 M) e = unpackR 24 (powWK M e)
  | 0 => hone
  | e + 1 => by
    rw [powRows, powRows_eq M hone e, mulWK_unpack]
    change _ = unpackR 24 (strictN (powWK M e) fun a => mulWK a M)
    rw [strictN_eq]

end CFSG.KC.Co1B

end
