module

public import Certificates.Data.Kernel.F2Dag
public import CFSG.Certificates.Kernel.Co1BMulSound
import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas

public section

namespace CFSG.KC.F2Dag

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.Sporadic.Co1Schreier.Native
open CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def unpackF (d M : Nat) : Array Nat := Array.ofFn (n := d) fun i => rowF d M i.val

theorem unpackF_eq (d M : Nat) : unpackF d M = CFSG.KC.Co1F2.unpackR d M := by
  unfold unpackF CFSG.KC.Co1F2.unpackR
  congr 1
  funext i
  exact CFSG.KC.F2W.rowF_eq d M i.val

theorem mul_unpack (X Y : Nat) : mul (unpackF 24 X) (unpackF 24 Y) = unpackF 24 (mulF 24 X Y) := by
  rw [unpackF_eq, unpackF_eq, unpackF_eq]
  exact CFSG.KC.F2W.mulRows_unpackR 24 X Y

theorem one_unpack : one = unpackF 24 (idF 24) := by
  unfold one idRows unpackF
  congr 1
  funext i
  revert i
  decide +kernel

theorem inv_unpack {X Y : Nat} (hX : X < 2 ^ 576) (hY : Y < 2 ^ 576)
    (h : Nat.beq (mulF 24 X Y) (idF 24) = true) : inv (unpackF 24 X) = unpackF 24 Y := by
  have hm : mul (unpackF 24 X) (unpackF 24 Y) = one () := by
    rw [mul_unpack, Nat.eq_of_beq_eq_true h, one_unpack]
  refine CFSG.KS.SporSch.M24.MatL.inv_eq_of_mul ?_ (by simp [unpackF]) fun i hi => ?_
  · rw [← CFSG.Sporadic.SmallF2.rowsMatrix_mulRows]
    change CFSG.Sporadic.SmallF2.rowsMatrix 24 (mul (unpackF 24 X) (unpackF 24 Y)) = 1
    rw [hm]
    exact CFSG.Sporadic.SmallF2.rowsMatrix_idRows 24
  · simp only [unpackF, Array.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
    exact CFSG.KC.F2W.rowF_lt 24 Y i

set_option exponentiation.threshold 600 in
theorem unpackF_inj {X Y : Nat} (hX : X < 2 ^ 576) (hY : Y < 2 ^ 576)
    (h : unpackF 24 X = unpackF 24 Y) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 576
  · have hi : p / 24 < 24 := by omega
    have hr : rowF 24 X (p / 24) = rowF 24 Y (p / 24) := by
      have e := congrArg (fun a : Array Nat => a[p / 24]?) h
      simpa [unpackF, hi] using e
    have e : p = p / 24 * 24 + p % 24 := by omega
    rw [e, ← CFSG.KC.F2W.testBit_rowF 24 X (p / 24) (p % 24) (Nat.mod_lt _ (by norm_num)),
      ← CFSG.KC.F2W.testBit_rowF 24 Y (p / 24) (p % 24) (Nat.mod_lt _ (by norm_num)), hr]
  · have h2 : 2 ^ 576 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX h2),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hY h2)]

theorem beq_unpack {X Y : Nat} (hX : X < 2 ^ 576) (hY : Y < 2 ^ 576) :
    (unpackF 24 X == unpackF 24 Y) = Nat.beq X Y := by
  apply Bool.eq_iff_iff.2
  constructor
  · intro h
    rw [unpackF_inj hX hY (beq_iff_eq.1 h)]
    exact Nat.beq_refl Y
  · intro h
    rw [Nat.eq_of_beq_eq_true h]
    exact beq_self_eq_true _

theorem rowsOfPayload_unpack {cs : List Char} {d M : Nat} (h : m1Bind cs d M = true) :
    rowsOfPayload d (String.ofList cs) = unpackF d M := by
  rw [unpackF_eq]
  exact CFSG.KC.Co1F2.bind_sound h

theorem strictN_eqD (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem getB_eq (T : List Nat) {L : Nat} (hT : T.length = L) (k : Nat) :
    getB 24 T L k = T.getD k (idF 24) := by
  unfold getB
  by_cases hk : k < L
  · have e : Nat.blt k L = true := by simpa [Nat.blt_eq] using hk
    rw [e]
  · have e : Nat.blt k L = false := by
      cases h : Nat.blt k L
      · rfl
      · exact absurd (by simpa [Nat.blt_eq] using h) hk
    rw [e, List.getD_eq_default _ _ (by omega)]

theorem letter_unpack (E EI : List Nat) (hl : EI.length = E.length) (j : Int) :
    letter (E.map (unpackF 24)) (EI.map (unpackF 24)) j =
      unpackF 24 (letterK 24 E EI E.length j) := by
  unfold letter letterK
  rw [one_unpack]
  rcases j with k | k
  · rcases k with _ | k
    · rw [if_neg (by decide), show (-Int.ofNat 0).toNat - 1 = 0 from rfl, List.getD_map]
      exact congrArg (unpackF 24) (getB_eq EI hl 0).symm
    · have hpos : (0 : Int) < Int.ofNat (k + 1) := Int.natCast_pos.mpr (Nat.succ_pos k)
      rw [if_pos hpos, show (Int.ofNat (k + 1)).toNat - 1 = k from Nat.add_sub_cancel k 1,
        List.getD_map]
      exact congrArg (unpackF 24) (getB_eq E rfl k).symm
  · have hneg : ¬ (0 : Int) < Int.negSucc k := fun h =>
      absurd (Int.lt_trans h (Int.negSucc_lt_zero k)) (Int.lt_irrefl 0)
    rw [if_neg hneg, show (-Int.negSucc k).toNat - 1 = k from Nat.add_sub_cancel k 1, List.getD_map]
    exact congrArg (unpackF 24) (getB_eq EI hl k).symm

theorem word_go (E EI : List Nat) (hl : EI.length = E.length) : ∀ (w : List Int) (acc : Nat),
    w.foldl (fun a j => mul a (letter (E.map (unpackF 24)) (EI.map (unpackF 24)) j))
        (unpackF 24 acc) =
      unpackF 24 (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
        (fun j _ ih acc => strictN (mulF 24 acc (letterK 24 E EI E.length j)) ih) w acc)
  | [], _ => rfl
  | j :: w, acc => by
    rw [List.foldl_cons, letter_unpack E EI hl j, mul_unpack, word_go E EI hl w]
    exact congrArg (unpackF 24) (strictN_eqD _ _).symm

theorem word_unpack (E EI : List Nat) (hl : EI.length = E.length) (w : List Int) :
    word (E.map (unpackF 24)) (EI.map (unpackF 24)) w = unpackF 24 (wordK 24 E EI E.length w) := by
  unfold word
  rw [one_unpack]
  exact word_go E EI hl w (idF 24)

private theorem andB_true' {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem allN_true' (f : Nat → Bool) :
    ∀ n, allN n f = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := andB_true' (show andB (f n) (allN n f) = true from h)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact allN_true' f n h2 i hi
    · exact h1

set_option exponentiation.threshold 600 in
private theorem canonF_lt {X : Nat} (h : canonF 24 X = true) : X < 2 ^ 576 := by
  unfold canonF pw2 at h
  rw [Nat.blt_eq] at h
  exact h

private theorem getB_take (T : List Nat) (k i : Nat) : getB 24 (T.take k) k i = getB 24 T k i := by
  unfold getB
  by_cases hi : i < k
  · have e : Nat.blt i k = true := by simpa [Nat.blt_eq] using hi
    rw [e]
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]
  · have e : Nat.blt i k = false := by
      cases h : Nat.blt i k
      · rfl
      · exact absurd (by simpa [Nat.blt_eq] using h) hi
    rw [e]

private theorem letterK_take (E EI : List Nat) (k : Nat) (j : Int) :
    letterK 24 (E.take k) (EI.take k) k j = letterK 24 E EI k j := by
  unfold letterK
  simp only [getB_take]

private theorem wordK_take (E EI : List Nat) (k : Nat) (w : List Int) :
    wordK 24 (E.take k) (EI.take k) k w = wordK 24 E EI k w := by
  unfold wordK
  simp only [letterK_take]

private theorem take_succ_getD (E : List Nat) {k : Nat} (hk : k < E.length) :
    E.take (k + 1) = E.take k ++ [E.getD k 0] := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  rfl

private theorem stepsK_cons (nb : Nat) (E EI : List Nat) (w : List Int) (ws : List (List Int))
    (s : Nat) :
    stepsK 24 nb E EI (w :: ws) s =
      andB (Nat.beq (E.getD (Nat.add nb s) (nat_lit 0)) (wordK 24 E EI (Nat.add nb s) w))
        (stepsK 24 nb E EI ws (Nat.succ s)) := rfl

private def Canon (E EI : List Nat) : Prop :=
  ∀ k < E.length, E.getD k 0 < 2 ^ 576 ∧ EI.getD k 0 < 2 ^ 576 ∧
    Nat.beq (mulF 24 (E.getD k 0) (EI.getD k 0)) (idF 24) = true

private theorem inv_entry {E EI : List Nat} (hc : Canon E EI) {k : Nat} (hk : k < E.length) :
    inv (unpackF 24 (E.getD k 0)) = unpackF 24 (EI.getD k 0) ∧
      (mul (unpackF 24 (E.getD k 0)) (unpackF 24 (EI.getD k 0)) == one ()) = true := by
  obtain ⟨h1, h2, h3⟩ := hc k hk
  refine ⟨inv_unpack h1 h2 h3, ?_⟩
  rw [mul_unpack, Nat.eq_of_beq_eq_true h3, one_unpack]
  exact beq_self_eq_true _

private theorem step_unpack {E EI : List Nat} (hl : EI.length = E.length) (hc : Canon E EI)
    {k : Nat} (hk : k < E.length) {w : List Int} (hw : E.getD k 0 = wordK 24 E EI k w) :
    step ((E.take k).map (unpackF 24), (EI.take k).map (unpackF 24), true) w =
      ((E.take (k + 1)).map (unpackF 24), (EI.take (k + 1)).map (unpackF 24), true) := by
  have hlen : (E.take k).length = k := by simp [List.length_take]; omega
  have hw' : word ((E.take k).map (unpackF 24)) ((EI.take k).map (unpackF 24)) w =
      unpackF 24 (E.getD k 0) := by
    rw [word_unpack (E.take k) (EI.take k) (by simp [List.length_take, hl]) w, hlen, wordK_take, hw]
  obtain ⟨hi, hm⟩ := inv_entry hc hk
  unfold step
  simp only []
  rw [hw', hi, hm, take_succ_getD E hk, take_succ_getD EI (by omega), List.map_append, List.map_append,
    List.map_singleton, List.map_singleton]
  rfl

private theorem steps_fold {nb : Nat} {E EI : List Nat} (hl : EI.length = E.length)
    (hc : Canon E EI) :
    ∀ (ws : List (List Int)) (s : Nat), nb + s + ws.length = E.length →
      stepsK 24 nb E EI ws s = true →
      ws.foldl step ((E.take (nb + s)).map (unpackF 24), (EI.take (nb + s)).map (unpackF 24), true) =
        (E.map (unpackF 24), EI.map (unpackF 24), true)
  | [], s, hlen, _ => by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero] at hlen ⊢
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  | w :: ws, s, hlen, h => by
    rw [stepsK_cons] at h
    obtain ⟨h1, h2⟩ := andB_true' h
    simp only [List.length_cons] at hlen
    have hk : nb + s < E.length := by omega
    rw [List.foldl_cons, step_unpack hl hc hk (Nat.eq_of_beq_eq_true h1)]
    exact steps_fold hl hc ws (s + 1) (by omega) h2

private theorem init_dag {E EI : List Nat} (hl : EI.length = E.length) (hc : Canon E EI) :
    ∀ nb, nb ≤ E.length →
      ((E.take nb).map (unpackF 24)).map inv = (EI.take nb).map (unpackF 24) ∧
        ((E.take nb).map (unpackF 24)).all (fun b => mul b (inv b) == one ()) = true
  | 0, _ => ⟨rfl, rfl⟩
  | nb + 1, h => by
    obtain ⟨ih1, ih2⟩ := init_dag hl hc nb (by omega)
    obtain ⟨hi, hm⟩ := inv_entry hc (show nb < E.length by omega)
    rw [take_succ_getD E h, take_succ_getD EI (by omega), List.map_append, List.map_append,
      List.map_append, List.map_singleton, List.map_singleton, List.map_singleton, ih1, hi]
    refine ⟨rfl, ?_⟩
    rw [List.all_append, ih2, Bool.true_and, List.all_cons, List.all_nil, Bool.and_true, hi]
    exact hm

theorem dagK_sound {nb : Nat} {ws : List (List Int)} {E EI : List Nat}
    (h : dagK 24 nb ws E EI = true) :
    dag ((E.take nb).map (unpackF 24)) ws =
      (E.map (unpackF 24), EI.map (unpackF 24), true) := by
  unfold dagK at h
  obtain ⟨hE, h⟩ := andB_true' h
  obtain ⟨hEI, h⟩ := andB_true' h
  obtain ⟨hall, hsteps⟩ := andB_true' h
  have hE' : E.length = nb + ws.length := Nat.eq_of_beq_eq_true hE
  have hEI' : EI.length = nb + ws.length := Nat.eq_of_beq_eq_true hEI
  have hc : Canon E EI := fun k hk => by
    obtain ⟨h1, h2⟩ := andB_true' (allN_true' _ _ hall k hk)
    obtain ⟨h2, h3⟩ := andB_true' h2
    exact ⟨canonF_lt h1, canonF_lt h2, h3⟩
  have hl : EI.length = E.length := by omega
  obtain ⟨hmap, hall'⟩ := init_dag hl hc nb (by omega)
  unfold dag
  rw [hmap, hall']
  exact steps_fold hl hc ws 0 (by omega) hsteps

theorem validRows_unpack (X : Nat) : CFSG.Sporadic.Co1.InvNative.validRows (unpackF 24 X) = true := by
  unfold CFSG.Sporadic.Co1.InvNative.validRows unpackF
  rw [Bool.and_eq_true, Array.all_eq_true]
  refine ⟨by rw [Array.size_ofFn]; rfl, fun i hi => ?_⟩
  rw [Array.getElem_ofFn, decide_eq_true_eq]
  unfold rowF fget maskN pw2
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem pow_unpack (X : Nat) : ∀ e, pow (unpackF 24 X) e = unpackF 24 (powL 24 X e)
  | 0 => one_unpack
  | e + 1 => by
    rw [pow, pow_unpack X e, mul_unpack]
    rfl

end CFSG.KC.F2Dag

end
