module

public import Certificates.Data.Kernel.SporSch.Co1StabW
public import CFSG.Certificates.Kernel.SporSch.Co1StabSound
public import CFSG.Certificates.Kernel.SporSch.Co1MatWSound
public import CFSG.Certificates.Kernel.SporSch.Co1ElemWSound

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.KS.Mathieu
open MatL

theorem wordIWK_eq (M MI : Nat → Nat) (w : List Int) :
    wordIWK M MI w = w.foldl (fun acc z => CFSG.KC.Co1B.mulWK acc (letterK M MI (icode z))) idM := by
  unfold wordIWK
  generalize idM = a
  induction w generalizing a with
  | nil => rfl
  | cons z w ih => exact (strictN_eq _ _).trans (ih _)

theorem word_eq_wordIWK {M MI : Nat → Nat} {k : Nat} {w : List Int} (h : lettersIK k w = true) :
    word (rowsL M k) (rowsL MI k) w = unpack 24 24 (wordIWK M MI w) := by
  unfold word
  rw [← unpack_idM, wordIWK_eq]
  generalize idM = a
  have hl := lettersIK_spec h
  clear h
  induction w generalizing a with
  | nil => rfl
  | cons z w ih =>
    rw [List.foldl_cons, List.foldl_cons, letter_eq (hl z (by simp)).1 (hl z (by simp)).2,
      mul_unpackW]
    exact ih _ (fun z' hz' => hl z' (List.mem_cons_of_mem z hz'))

theorem dagIW_fold {M MI : Nat → Nat} {N : Nat} (hinv : ∀ i < N, invOKW (M i) (MI i) = true) :
    ∀ (ws : List (List Int)) (k : Nat), k + ws.length ≤ N →
      List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun w _ ih k => bAnd(lettersIK k w, bAnd(Nat.beq (wordIWK M MI w) (M k), ih (Nat.succ k))))
          ws k = true →
      ws.foldl step (rowsL M k, rowsL MI k, true) =
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
    have hs : step (rowsL M k, rowsL MI k, true) w =
        (rowsL M (k + 1), rowsL MI (k + 1), true) := by
      unfold step
      simp only
      rw [word_eq_wordIWK h1, Nat.eq_of_beq_eq_true h2, hi, hm, rowsL_succ, rowsL_succ,
        beq_self_eq_true, Bool.and_true]
    have e : k + 1 + ws.length = k + (ws.length + 1) := by omega
    rw [List.foldl_cons, hs,
      ih (k + 1) (by omega) (by simpa only [bAnd_eq, Nat.succ_eq_add_one] using h3),
      List.length_cons, e]

theorem dagIWK_sound {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Int)} {base : List Rows}
    (hb : base = (List.range nb).map fun i => unpack 24 24 (M i))
    (h : dagIWK M MI nb N ws = true) :
    dag base ws = ((List.range N).map fun i => unpack 24 24 (M i),
      (List.range N).map fun i => unpack 24 24 (MI i), true) := by
  obtain ⟨hN, h⟩ := MatS.bAnd_split h
  obtain ⟨hall, hrec⟩ := MatS.bAnd_split h
  have hinv := allN_iff.1 hall
  have hN' : nb + ws.length = N := by
    rw [← lenWI_eq]
    exact Nat.eq_of_beq_eq_true hN
  have hmap : base.map CFSG.Sporadic.Co1Schreier.Native.inv = rowsL MI nb := by
    rw [hb, rowsL, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (invOKW_sound (hinv i (by rw [List.mem_range] at hi; omega))).2
  have hall' : (base.all fun b => mul b (CFSG.Sporadic.Co1Schreier.Native.inv b) == one ()) =
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
  rw [hmap, hall', hb', dagIW_fold hinv ws nb (by omega) hrec, hN']
  rfl

theorem dagIWK_eq_dagIK : dagIWK = dagIK := by
  funext M MI nb N ws
  unfold dagIWK dagIK wordIWK wordIK invOKW invOKK
  rw [mulWK_eq_mulK]

end CFSG.KS.SporSch.M24

end
