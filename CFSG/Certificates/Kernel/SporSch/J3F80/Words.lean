module

public import Certificates.Data.Kernel.SporSch.J3F80
public import CFSG.Certificates.Kernel.SporSch.HexLe70Sound
public import CFSG.Certificates.Kernel.SporSch.PairJ3FaithSound
public import CFSG.Sporadic.Schreier.PairJ3FaithfulCheckInputs
import CFSG.Certificates.Kernel.Spor.HexText
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.SporSch.J3F.WordsPf

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KS.SporSch.J3F CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairJ3

private noncomputable def numL (L : List Char) (o : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => numL L o c * 16 + hexV (L[o + c]!).toNat

private theorem numL_append_right (A B : List Char) (o : Nat) :
    ∀ c, numL (A ++ B) (A.length + o) c = numL B o c
  | 0 => rfl
  | c + 1 => by
    simp only [numL, numL_append_right A B o c]
    congr 3
    rw [Nat.add_assoc, getElem!_def, getElem!_def, List.getElem?_append_right (by omega)]
    simp

private theorem numL_append_left (A B : List Char) (o : Nat) :
    ∀ c, o + c ≤ A.length → numL (A ++ B) o c = numL A o c
  | 0, _ => rfl
  | c + 1, h => by
    simp only [numL, numL_append_left A B o c (by omega)]
    congr 3
    rw [getElem!_def, getElem!_def, List.getElem?_append_left (by omega)]

private theorem hexVal_ofNat {x : Nat} (hx : x < 128) : hexVal (UInt8.ofNat x) = hexV x := by
  have e : (UInt8.ofNat x).toNat = x := by
    rw [UInt8.toNat_ofNat']; omega
  unfold hexVal hexV
  rw [e]
  by_cases h : x < 58
  · have hb : Nat.blt x 58 = true := Nat.blt_eq.mpr h
    simp only [h, ↓reduceIte, hb]
    rfl
  · have hb : Nat.blt x 58 = false := by
      cases hq : Nat.blt x 58
      · rfl
      · exact absurd (Nat.blt_eq.mp hq) h
    simp only [h, ↓reduceIte, hb]
    rfl

private theorem hexAt_numL {L : List Char} (hasc : ∀ ch ∈ L, ch.toNat ≤ 70) (o : Nat) :
    ∀ c, o + c ≤ L.length → hexAt (String.ofList L).toUTF8 o c = numL L o c
  | 0, _ => rfl
  | c + 1, h => by
    have hk : o + c < L.length := by omega
    have hD : ∀ k < L.length, k < L.length ∧ (L[k]!).toNat < 128 := fun k hk' => by
      refine ⟨hk', ?_⟩
      have := hasc _ (List.getElem_mem hk')
      rw [getElem!_pos L k hk']
      omega
    have hb : (String.ofList L).toUTF8.get! (o + c) = UInt8.ofNat (L[o + c]!).toNat := by
      rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
      exact HexText.utf8_get L L.length hD (o + c) hk
    simp only [hexAt, numL, hexAt_numL hasc o c (by omega), hb, hexVal_ofNat (hD _ hk).2]

private theorem strictB_w (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

private theorem bAnd_w {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

private noncomputable def runW (F : Nat → Nat) (k b : Nat) (cs : List Char) :
    Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun cnt _ idx => bAnd(Nat.beq cnt (nat_lit 0), Nat.beq idx k))
    (fun ch _ ih cnt acc idx =>
      CFSG.KC.Enum.strictB (Nat.add (Nat.mul acc (nat_lit 16)) (hexV ch.toNat)) fun a =>
      CFSG.KC.Enum.strictB (Nat.succ cnt) fun cnt' =>
      bIf(Nat.beq cnt' (nat_lit 810),
        bAnd(Nat.beq a (F (Nat.add b idx)), CFSG.KC.Enum.strictB (Nat.succ idx) fun idx' =>
          ih (nat_lit 0) (nat_lit 0) idx'),
        ih cnt' a idx))
    cs

private theorem runW_sound {F : Nat → Nat} {k b : Nat} (ch : List Char) :
    ∀ (l pre : List Char) (cnt acc idx : Nat), ch = pre ++ l → pre.length = 810 * idx + cnt →
      cnt < 810 → acc = numL ch (810 * idx) cnt → runW F k b l cnt acc idx = true →
      ch.length = 810 * k ∧ ∀ i, idx ≤ i → i < k → numL ch (810 * i) 810 = F (b + i) := by
  intro l
  induction l with
  | nil =>
    intro pre cnt acc idx hch hpre _ _ h
    obtain ⟨h1, h2⟩ := bAnd_w h
    have hc : cnt = 0 := Nat.eq_of_beq_eq_true h1
    have hi : idx = k := Nat.eq_of_beq_eq_true h2
    subst hc hi
    refine ⟨by rw [hch, List.append_nil, hpre]; rfl, fun i h1 h2 => absurd h2 (by omega)⟩
  | cons x l ih =>
    intro pre cnt acc idx hch hpre hcnt hacc h
    change CFSG.KC.Enum.strictB (Nat.add (Nat.mul acc 16) (hexV x.toNat)) (fun a =>
      CFSG.KC.Enum.strictB (Nat.succ cnt) fun cnt' =>
      bIf(Nat.beq cnt' 810, bAnd(Nat.beq a (F (Nat.add b idx)),
        CFSG.KC.Enum.strictB (Nat.succ idx) fun idx' => runW F k b l 0 0 idx'),
        runW F k b l cnt' a idx)) = true at h
    rw [strictB_w, strictB_w] at h
    have hx : ch[810 * idx + cnt]! = x := by
      rw [hch, getElem!_def, List.getElem?_append_right (by omega)]
      simp [hpre]
    have ha : acc * 16 + hexV x.toNat = numL ch (810 * idx) (cnt + 1) := by
      rw [numL, ← hacc, hx]
    have hch' : ch = (pre ++ [x]) ++ l := by rw [hch, List.append_assoc]; rfl
    by_cases hc : cnt + 1 = 810
    · have hb : Nat.beq (Nat.succ cnt) 810 = true := Nat.beq_eq_true_eq _ _ ▸ hc
      rw [hb] at h
      change Bool.rec (motive := fun _ => Bool) false _ _ = true at h
      obtain ⟨h1, h2⟩ := bAnd_w h
      rw [strictB_w] at h2
      have hF : numL ch (810 * idx) 810 = F (b + idx) := by
        have e : numL ch (810 * idx) 810 = numL ch (810 * idx) (cnt + 1) := by rw [hc]
        rw [e, ← ha]; exact Nat.eq_of_beq_eq_true h1
      obtain ⟨hl, hr⟩ := ih (pre ++ [x]) 0 0 (idx + 1) hch'
        (by rw [List.length_append, hpre]; simp; omega) (by omega) rfl h2
      refine ⟨hl, fun i hi1 hi2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hi1 with rfl | hi
      · exact hF
      · exact hr i hi hi2
    · have hb : Nat.beq (Nat.succ cnt) 810 = false := by
        cases hq : Nat.beq (Nat.succ cnt) 810
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hq) hc
      rw [hb] at h
      exact ih (pre ++ [x]) (cnt + 1) _ idx hch' (by rw [List.length_append, hpre]; simp; omega)
        (by omega) ha h

private theorem wordsK_sound {F : Nat → Nat} {k b : Nat} {ch : List Char}
    (h : wordsK F k b ch = true) :
    ch.length = 810 * k ∧ ∀ i < k, numL ch (810 * i) 810 = F (b + i) := by
  obtain ⟨hl, hr⟩ := runW_sound (F := F) (k := k) (b := b) ch ch [] 0 0 0 rfl rfl (by omega) rfl h
  exact ⟨hl, fun i hi => hr i (Nat.zero_le _) hi⟩

theorem words_sound' {cs : List (List Char)} {k : Nat} {F : Nat → Nat}
    (hasc : ∀ c ∈ cs, le70K c = true)
    (h : ∀ j < cs.length, wordsK F k (k * j) (cs.getD j []) = true) :
    ∀ r < k * cs.length, hexAt (String.ofList cs.flatten).toUTF8 (810 * r) 810 = F r := by
  intro r hr
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp at hr
    · exact h0
  have hlen : ∀ j < cs.length, (cs.getD j []).length = 810 * k := fun j hj =>
    (wordsK_sound (h j hj)).1
  have hpre : ∀ j ≤ cs.length, (cs.take j).flatten.length = 810 * k * j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [List.take_succ, List.flatten_append, List.length_append, ih (by omega),
        List.getElem?_eq_getElem (by omega)]
      have := hlen j (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at this
      simp [this]
      ring
  have hasc' : ∀ ch ∈ cs.flatten, ch.toNat ≤ 70 := by
    intro ch hc
    obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc
    exact le70K_mem (hasc l hl) ch hcl
  set j := r / k
  set i := r % k
  have hj : j < cs.length := by
    rw [Nat.div_lt_iff_lt_mul hk]; rw [Nat.mul_comm] at hr; exact hr
  have hi : i < k := Nat.mod_lt _ hk
  have hr' : r = k * j + i := (Nat.div_add_mod r k).symm
  have hsplit : cs.flatten = (cs.take j).flatten ++ (cs.getD j [] ++ (cs.drop (j + 1)).flatten) := by
    conv_lhs => rw [← List.take_append_drop j cs]
    rw [List.flatten_append, List.drop_eq_getElem_cons hj, List.flatten_cons,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [hexAt_numL hasc' _ _ (by
    rw [hsplit, List.length_append, List.length_append, hpre j hj.le, hlen j hj]
    rw [hr']; nlinarith)]
  rw [hsplit, show 810 * r = (cs.take j).flatten.length + 810 * i by
    rw [hpre j hj.le, hr']; ring, numL_append_right,
    numL_append_left _ _ _ _ (by rw [hlen j hj]; nlinarith), (wordsK_sound (h j hj)).2 i hi, ← hr']

theorem sort_sound' {bytes : ByteArray} {F SG SGI : Nat → Nat}
    (hF : ∀ r < 6156, hexAt bytes (810 * r) 810 = F r) (h : sortK F SG SGI 6156 = true) :
    PairNative.strictInc (sortedWords bytes) = true := by
  obtain ⟨h1, h2⟩ := bAnd_w h
  have hs := allN_spec h1
  have hp := allN_spec h2
  refine PF2.sorted_strictInc (g := fun r => hexAt bytes (810 * r) 810) (F := F) (σ := SG)
    (τ := SGI) hF (fun i hi => ?_) (fun i hi => ?_)
  · exact Nat.blt_eq.mp (hs i (by change i < 6156 - 1; omega))
  · have := hp i hi
    rw [strictB_w] at this
    obtain ⟨a, b⟩ := bAnd_w this
    exact ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b⟩

end CFSG.KS.SporSch.J3F.WordsPf

end
