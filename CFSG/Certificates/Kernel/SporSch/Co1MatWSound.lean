module

public import Certificates.Data.Kernel.SporSch.Co1MatW
public import CFSG.Certificates.Kernel.SporSch.Co1MatSound
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2
open MatL

theorem invOKW_sound {X Y : Nat} (h : invOKW X Y = true) :
    mul (unpack 24 24 X) (unpack 24 24 Y) = one () ∧
      CFSG.Sporadic.Co1Schreier.Native.inv (unpack 24 24 X) = unpack 24 24 Y := by
  have e : CFSG.KC.Co1B.mulWK X Y = idM := Nat.eq_of_beq_eq_true h
  have hm : mul (unpack 24 24 X) (unpack 24 24 Y) = one () := by
    rw [mul_unpackW, e, unpack_idM]
  refine ⟨hm, inv_eq_of_mul ?_ (unpack_size Y) (fun i hi => by rw [unpack_getD Y i hi]; exact rowV_lt Y i)⟩
  rw [← rowsMatrix_mulRows]
  change rowsMatrix 24 (mul (unpack 24 24 X) (unpack 24 24 Y)) = 1
  rw [hm]
  exact rowsMatrix_idRows 24

theorem wordWK_eq (M MI : Nat → Nat) (w : List Nat) :
    wordWK M MI w = w.foldl (fun acc c => CFSG.KC.Co1B.mulWK acc (letterK M MI c)) idM := by
  unfold wordWK
  generalize idM = a
  induction w generalizing a with
  | nil => rfl
  | cons c w ih => exact (strictN_eq _ _).trans (ih _)

theorem wordW_unpack {M MI : Nat → Nat} {k : Nat} (w : List Nat) (a : Nat)
    (hl : ∀ c ∈ w, 2 ≤ c ∧ c / 2 - 1 < k) :
    w.foldl (fun A c => mul A (letter (rowsL M k) (rowsL MI k) (decLetter c))) (unpack 24 24 a) =
      unpack 24 24 (w.foldl (fun acc c => CFSG.KC.Co1B.mulWK acc (letterK M MI c)) a) := by
  induction w generalizing a with
  | nil => rfl
  | cons c w ih =>
    rw [List.foldl_cons, List.foldl_cons, MatS.letterS_eq (hl c (by simp)).1 (hl c (by simp)).2,
      mul_unpackW]
    exact ih _ (fun c' hc' => hl c' (List.mem_cons_of_mem c hc'))

theorem word_eq_wordWK {M MI : Nat → Nat} {k : Nat} {w : List Nat} (h : lettersK k w = true) :
    word (rowsL M k) (rowsL MI k) (decWord w) = unpack 24 24 (wordWK M MI w) := by
  unfold word decWord
  rw [List.foldl_map, ← unpack_idM, wordWK_eq]
  exact wordW_unpack w idM (MatS.lettersK_spec h)

theorem dagW_fold {M MI : Nat → Nat} {N : Nat} (hinv : ∀ i < N, invOKW (M i) (MI i) = true) :
    ∀ (ws : List (List Nat)) (k : Nat), k + ws.length ≤ N →
      List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun w _ ih k => bAnd(lettersK k w, bAnd(Nat.beq (wordWK M MI w) (M k), ih (Nat.succ k))))
          ws k = true →
      (ws.map decWord).foldl step (rowsL M k, rowsL MI k, true) =
        (rowsL M (k + ws.length), rowsL MI (k + ws.length), true) := by
  intro ws
  induction ws with
  | nil => intro k _ _; rfl
  | cons w ws ih =>
    intro k hk hrec
    simp only [bAnd_eq, Bool.and_eq_true] at hrec
    obtain ⟨h1, h2, h3⟩ := hrec
    simp only [List.length_cons] at hk
    obtain ⟨hm, hi⟩ := invOKW_sound (hinv k (by omega))
    have hs : step (rowsL M k, rowsL MI k, true) (decWord w) =
        (rowsL M (k + 1), rowsL MI (k + 1), true) := by
      unfold step
      simp only
      rw [word_eq_wordWK h1, Nat.eq_of_beq_eq_true h2, hi, hm, rowsL_succ, rowsL_succ,
        beq_self_eq_true, Bool.and_true]
    have e : k + 1 + ws.length = k + (ws.length + 1) := by omega
    rw [List.map_cons, List.foldl_cons, hs,
      ih (k + 1) (by omega) (by simpa only [bAnd_eq, Nat.succ_eq_add_one] using h3),
      List.length_cons, e]

theorem dagWK_inv {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Nat)}
    (h : dagWK M MI nb N ws = true) : ∀ i < N, invOKW (M i) (MI i) = true := by
  obtain ⟨-, h⟩ := MatS.bAnd_split h
  exact allN_iff.1 (MatS.bAnd_split h).1

theorem dagWK_sound {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Nat)} {base : List Rows}
    (hb : base = (List.range nb).map fun i => unpack 24 24 (M i))
    (h : dagWK M MI nb N ws = true) :
    dag base (ws.map decWord) = ((List.range N).map fun i => unpack 24 24 (M i),
      (List.range N).map fun i => unpack 24 24 (MI i), true) := by
  have hinv := dagWK_inv h
  obtain ⟨hN, h⟩ := MatS.bAnd_split h
  obtain ⟨-, hrec⟩ := MatS.bAnd_split h
  have hN' : nb + ws.length = N := by
    rw [← MatS.lenLL_eq]
    exact Nat.eq_of_beq_eq_true hN
  have hmap : base.map CFSG.Sporadic.Co1Schreier.Native.inv = rowsL MI nb := by
    rw [hb, rowsL, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (invOKW_sound (hinv i (by rw [List.mem_range] at hi; omega))).2
  have hall : (base.all fun b => mul b (CFSG.Sporadic.Co1Schreier.Native.inv b) == one ()) =
      true := by
    rw [List.all_eq_true]
    intro b hbm
    rw [hb, List.mem_map] at hbm
    obtain ⟨i, hi, rfl⟩ := hbm
    obtain ⟨hm, hinv'⟩ := invOKW_sound (hinv i (by rw [List.mem_range] at hi; omega))
    rw [hinv', hm]
    exact beq_self_eq_true _
  have hb' : base = rowsL M nb := hb
  unfold dag
  rw [hmap, hall, hb', dagW_fold hinv ws nb (by omega) hrec, hN']
  rfl

end CFSG.KS.SporSch.M24

end
