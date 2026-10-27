module

public import Certificates.Data.Kernel.Griess13.Packed
public import CFSG.Monster.GMS.Griess13.DataPacked
public import CFSG.Certificates.Kernel.Co1BWordSound
public import CFSG.Certificates.Kernel.Co1BSound
import CFSG.Certificates.Kernel.Co1BInvSound

public section

namespace CFSG.KC.G13

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.Monster.GMS.Griess13.Co1Data
  CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def toPR (a : Nat) : PR := ⟨unpackR 24 a, unpackR 24 (sP a)⟩

theorem strictT_eq {α : Type} (y : Nat) (k : Nat → α) : strictT y k = k y := by
  cases y <;> rfl

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

set_option exponentiation.threshold 2048

theorem m576_eq : m576 = 2 ^ 576 := by
  change 1 <<< 576 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem pk_mod (x y : Nat) : pk x y % 2 ^ 576 = x % 2 ^ 576 := by
  change (x % m576 + (y % m576) <<< 576) % 2 ^ 576 = _
  rw [m576_eq, Nat.shiftLeft_eq, Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem sP_pk (x y : Nat) : sP (pk x y) = y % 2 ^ 576 := by
  change (x % m576 + (y % m576) <<< 576) >>> 576 = y % 2 ^ 576
  rw [m576_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity)), Nat.zero_add]

theorem unpackR_congr {x y : Nat} (h : x % 2 ^ 576 = y % 2 ^ 576) : unpackR 24 x = unpackR 24 y := by
  unfold unpackR
  congr 1
  funext i
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_field, testBit_field]
  by_cases hb : b < 24
  · have hlt : 24 * i.val + b < 576 := by have := i.isLt; omega
    have h1 := congrArg (fun z => z.testBit (24 * i.val + b)) h
    simp only [Nat.testBit_mod_two_pow, hlt, decide_true, Bool.true_and] at h1
    rw [h1]
  · simp [hb]

theorem unpackR_pk (x y : Nat) : unpackR 24 (pk x y) = unpackR 24 x := unpackR_congr (pk_mod x y)

theorem unpackR_sP_pk (x y : Nat) : unpackR 24 (sP (pk x y)) = unpackR 24 y := by
  rw [sP_pk]
  exact unpackR_congr (Nat.mod_mod _ _)

theorem toPR_mul (a b : Nat) : (toPR a).mul (toPR b) = toPR (mulP a b) := by
  simp only [toPR, PR.mul, mulP, strictN_eq', unpackR_pk, unpackR_sP_pk, mulWK_unpack]

theorem toPR_inv (a : Nat) : (toPR a).inv = toPR (invP a) := by
  simp only [toPR, PR.inv, invP, strictN_eq', unpackR_pk, unpackR_sP_pk]

theorem toPR_one : PR.one = toPR oneP := by
  have h : idRows 24 = unpackR 24 oneK := CFSG.KC.F2W.unpackR_idF.symm
  simp only [toPR, PR.one, oneP, unpackR_pk, unpackR_sP_pk, h]

theorem toPR_pow (a : Nat) : ∀ n : Nat, (toPR a).pow n = toPR (powP a n)
  | 0 => toPR_one
  | n + 1 => by
    change ((toPR a).pow n).mul (toPR a) = toPR (mulP (powP a n) a)
    rw [toPR_pow a n, toPR_mul]

theorem toPR_zpow (a : Nat) (e : Int) : (toPR a).zpow e = toPR (zpowP a e) := by
  unfold PR.zpow zpowP
  split_ifs
  · exact toPR_pow a _
  · rw [toPR_inv, toPR_pow]

theorem toPR_conj (a b : Nat) : (toPR a).conj (toPR b) = toPR (conjP a b) := by
  rw [PR.conj, toPR_mul, toPR_inv, toPR_mul, conjP, strictN_eq']

theorem toPR_eq (a b : Nat) : PR.eq (toPR a) (toPR b) = eqP a b := by
  have h576 : Nat.shiftLeft 1 576 = 2 ^ (24 * 24) := by
    change 1 <<< 576 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  apply Bool.eq_iff_iff.2
  change eqRows (unpackR 24 a) (unpackR 24 b) = true ↔
    Nat.beq (a % Nat.shiftLeft 1 576) (b % Nat.shiftLeft 1 576) = true
  rw [h576, Nat.beq_eq, ← fields_eq_iff (by decide) 24 a b, eqRows, List.all_eq_true]
  constructor
  · intro h i hi
    have := h i (List.mem_range.2 hi)
    simpa [unpackR, hi] using this
  · intro h i hi
    have hi' := List.mem_range.1 hi
    simpa [unpackR, hi'] using h i hi'

theorem getD_toPR (l : List Nat) (i : Nat) : (l.map toPR).getD i PR.one = toPR (l.getD i oneP) := by
  rw [toPR_one, List.getD_map]

theorem toPR_letter (gens : List Nat) (l : Int) :
    letterPR (gens.map toPR) l = toPR (letterP gens l) := by
  unfold letterPR letterP
  split_ifs
  · exact getD_toPR _ _
  · rw [getD_toPR, toPR_inv]

theorem foldl_word (gens : List Nat) :
    ∀ (w : List Int) (acc : Nat),
      w.foldl (fun a l => a.mul (letterPR (gens.map toPR) l)) (toPR acc) = toPR (wordFrom gens w acc)
  | [], _ => rfl
  | l :: w, acc => by
    rw [List.foldl_cons, toPR_letter, toPR_mul, foldl_word gens w]
    change _ = toPR (strictN (mulP acc (letterP gens l)) (wordFrom gens w))
    rw [strictN_eq']

theorem toPR_word (gens : List Nat) (w : List Int) :
    wordPR (gens.map toPR) w = toPR (wordP gens w) := by
  rw [wordPR, toPR_one]
  exact foldl_word gens w oneP

@[expose] noncomputable def regMap (R : List (Nat × Nat)) : List (Nat × PR) := R.map fun kv => (kv.1, toPR kv.2)

theorem lookup_toPR : ∀ (R : List (Nat × Nat)) (i : Nat),
    SLP.lookupPR (regMap R) i = toPR (lookupP R i)
  | [], _ => toPR_one
  | (k, v) :: R, i => by
    change (if i = k then toPR v else SLP.lookupPR (regMap R) i) =
      toPR (if i = k then v else lookupP R i)
    split_ifs
    · rfl
    · exact lookup_toPR R i

theorem init_toPR : ∀ (l : List Nat) (j : Nat), SLP.initRegsAux (l.map toPR) j = regMap (initP l j)
  | [], _ => rfl
  | x :: l, j => by
    change (j, toPR x) :: SLP.initRegsAux (l.map toPR) (j + 1) = (j, toPR x) :: regMap (initP l (j + 1))
    rw [init_toPR l (j + 1)]

theorem line_toPR (R : List (Nat × Nat)) (l : Nat × List (Nat × Int)) :
    SLP.stepPR (regMap R) l = regMap ((l.1, lineP R l) :: R) := by
  have key : ∀ (fs : List (Nat × Int)) (acc : Nat),
      fs.foldl (fun acc f => acc.mul ((SLP.lookupPR (regMap R) f.1).zpow f.2)) (toPR acc) =
        toPR (fs.foldl (fun acc f => mulP acc (zpowP (lookupP R f.1) f.2)) acc) := by
    intro fs
    induction fs with
    | nil => intro acc; rfl
    | cons f fs ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, lookup_toPR, toPR_zpow, toPR_mul, ih]
  unfold SLP.stepPR lineP
  rw [toPR_one, key]
  rfl

theorem runP_eq : ∀ (ls : List (Nat × List (Nat × Int))) (R : List (Nat × Nat)),
    runP ls R = ls.foldl (fun R l => (l.1, lineP R l) :: R) R
  | [], _ => rfl
  | l :: ls, R => by
    change strictT (lineP R l) (fun v => runP ls ((l.1, v) :: R)) = _
    rw [strictT_eq, runP_eq ls, List.foldl_cons]

theorem evalPR_toPR (p : SLP) (ins : List Nat) :
    p.evalPR (ins.map toPR) = (evalP p ins).map toPR := by
  have key : ∀ (ls : List (Nat × List (Nat × Int))) (R : List (Nat × Nat)),
      ls.foldl SLP.stepPR (regMap R) = regMap (ls.foldl (fun R l => (l.1, lineP R l) :: R) R) := by
    intro ls
    induction ls with
    | nil => intro R; rfl
    | cons l ls ih =>
      intro R
      rw [List.foldl_cons, List.foldl_cons, line_toPR, ih]
  unfold SLP.evalPR SLP.regsPR evalP
  rw [init_toPR, key, ← runP_eq, List.map_map]
  refine List.map_congr_left fun f _ => ?_
  rw [Function.comp_apply, lookup_toPR, toPR_zpow]

theorem foldr_toPR {n : Nat} (f : Fin n → Nat) :
    (List.ofFn fun i => toPR (f i)).foldr PR.mul PR.one = toPR ((List.ofFn f).foldr mulP oneP) := by
  have h : (List.ofFn fun i => toPR (f i)) = (List.ofFn f).map toPR := by
    rw [List.map_ofFn]
    rfl
  rw [h, toPR_one]
  induction List.ofFn f with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.foldr_cons, ih, toPR_mul, List.foldr_cons]

theorem prIota_toPR {E : Fin 6 → Nat} (hE : ∀ i, prE i = toPR (E i)) (v : Fin 6 → ZMod 3) :
    prIota v = toPR (iotaP E fun i => (v i).val) := by
  unfold prIota
  simp only [hE, toPR_pow]
  exact foldr_toPR _

theorem allN_spec {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    change Bool.rec (motive := fun _ => Bool) false (allN n f) (f n) = true at h
    cases hf : f n
    · rw [hf] at h
      exact absurd h Bool.false_ne_true
    · rw [hf] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact ih h i hi
      · exact hf

theorem iotaNe_sound {E : Fin 6 → Nat} (hE : ∀ i, prE i = toPR (E i)) (h : iotaNeK E = true) :
    ∀ v : Fin 6 → ZMod 3, v ≠ 0 → PR.eq (prIota v) PR.one = false := by
  intro v hv
  rw [prIota_toPR hE, toPR_one, toPR_eq]
  have ha : ∀ i, (v i).val < 3 := fun i => ZMod.val_lt (v i)
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have h4 := ha 4
  have h5 := ha 5
  obtain ⟨c, hcd⟩ : ∃ c, c = (v 0).val + 3 * (v 1).val + 9 * (v 2).val + 27 * (v 3).val +
    81 * (v 4).val + 243 * (v 5).val := ⟨_, rfl⟩
  have hc : c < 729 := by omega
  have hdig : (fun i : Fin 6 => c / 3 ^ i.val % 3) = fun i => (v i).val := by
    funext i
    fin_cases i
    · change c / 1 % 3 = (v 0).val
      omega
    · change c / 3 % 3 = (v 1).val
      omega
    · change c / 9 % 3 = (v 2).val
      omega
    · change c / 27 % 3 = (v 3).val
      omega
    · change c / 81 % 3 = (v 4).val
      omega
    · change c / 243 % 3 = (v 5).val
      omega
  have hc0 : c ≠ 0 := by
    intro hz
    apply hv
    have hz' : (v 0).val = 0 ∧ (v 1).val = 0 ∧ (v 2).val = 0 ∧ (v 3).val = 0 ∧ (v 4).val = 0 ∧
        (v 5).val = 0 := by omega
    funext i
    rw [Pi.zero_apply, ← ZMod.val_eq_zero]
    fin_cases i
    exacts [hz'.1, hz'.2.1, hz'.2.2.1, hz'.2.2.2.1, hz'.2.2.2.2.1, hz'.2.2.2.2.2]
  have h27 : c / 27 < 27 := by omega
  have hh := allN_spec (allN_spec h (c / 27) h27) (c % 27) (Nat.mod_lt _ (by omega))
  have he : Nat.add (Nat.mul 27 (c / 27)) (c % 27) = c := Nat.div_add_mod c 27
  simp only [he] at hh
  have hb : Nat.beq c 0 = false := by
    cases h' : Nat.beq c 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h') hc0
  rw [hb] at hh
  change Bool.not (eqP (iotaP E fun i => c / 3 ^ i.val % 3) oneP) = true at hh
  rw [hdig] at hh
  simpa using hh

end CFSG.KC.G13

end
