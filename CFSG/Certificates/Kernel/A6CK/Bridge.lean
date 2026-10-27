module

public import Certificates.Data.Kernel.A6CK.Defs
public import Certificates.Data.A6CMat
public import CFSG.Certificates.Kernel.Fi22LH.Lanes
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.A6CK

open CFSG.KS.Fi22LH

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem testBit_byte {v i : Nat} (hv : v < 256) (hi : 8 ≤ i) : v.testBit i = false := by
  have h : (256 : Nat) ≤ 2 ^ i :=
    Nat.le_trans (by decide : (256 : Nat) ≤ 2 ^ 8) (Nat.pow_le_pow_right (by decide) hi)
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv h)

theorem testBit_255 (i : Nat) : (255 : Nat).testBit i = decide (i < 8) := by
  have : (255 : Nat) = 2 ^ 8 - 1 := by decide
  rw [this, Nat.testBit_two_pow_sub_one]

@[expose] def ent (x r c : Nat) : Nat := (x >>> (64 + 64 * r + 8 * c)) &&& 255

theorem ent_lt (x r c : Nat) : ent x r c < 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide : (255 : Nat) < 256)

theorem testBit_ent (x r c j : Nat) :
    (ent x r c).testBit j = (decide (j < 8) && x.testBit (64 + 64 * r + 8 * c + j)) := by
  rw [ent, Nat.testBit_and, Nat.testBit_shiftRight, testBit_255, Bool.and_comm]

@[expose] def flat (e : Nat → Nat → Nat) (q : Nat) : Nat := if q % 8 < 6 then e (q / 8) (q % 8) else 0

@[expose] def pk (e : Nat → Nat → Nat) : Nat := lanes 8 (flat e) 48

theorem flat_lt {e : Nat → Nat → Nat} {B : Nat} (hB : 0 < B) (he : ∀ r < 6, ∀ c < 6, e r c < B) :
    ∀ q < 48, flat e q < B := by
  intro q hq
  unfold flat
  split
  · exact he _ (by omega) _ (by omega)
  · exact hB

theorem testBit_pk {e : Nat → Nat → Nat} (he : ∀ r < 6, ∀ c < 6, e r c < 256) (i : Nat) :
    (pk e).testBit i =
      (decide (i < 384) && decide (i % 64 < 48) && (e (i / 64) (i % 64 / 8)).testBit (i % 8)) := by
  rw [pk, testBit_lanes (by decide) 48 (flat_lt (by decide) he) i]
  unfold flat
  have h1 : i / 8 / 8 = i / 64 := by omega
  have h2 : i / 8 % 8 = i % 64 / 8 := by omega
  rw [h1, h2]
  by_cases h3 : i % 64 < 48
  · have h4 : i % 64 / 8 < 6 := by omega
    simp [h3, h4]
  · have h4 : ¬ i % 64 / 8 < 6 := by omega
    simp [h3, h4]

theorem encS_def (m : Nat) : encS m = (m <<< 64) ||| (m % SP) := rfl

theorem testBit_encS_hi (m i : Nat) : (encS m).testBit (64 + i) = m.testBit i := by
  have hs : m % SP < 2 ^ (64 + i) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide))
      (Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (Nat.le_add_right 64 i)))
  rw [encS_def, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_lt_two_pow hs]
  simp

theorem encS_shr (m : Nat) : encS m >>> 64 = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, testBit_encS_hi]

theorem ent_encS_pk {e : Nat → Nat → Nat} (he : ∀ r < 6, ∀ c < 6, e r c < 256) {r c : Nat}
    (hr : r < 6) (hc : c < 6) : ent (encS (pk e)) r c = e r c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_ent, Nat.add_assoc, Nat.add_assoc, testBit_encS_hi, testBit_pk he]
  by_cases hj : j < 8
  · have e1 : (64 * r + (8 * c + j)) / 64 = r := by omega
    have e2 : (64 * r + (8 * c + j)) % 64 / 8 = c := by omega
    have e3 : (64 * r + (8 * c + j)) % 8 = j := by omega
    have e4 : 64 * r + (8 * c + j) < 384 := by omega
    have e5 : (64 * r + (8 * c + j)) % 64 < 48 := by omega
    rw [decide_eq_true e4, decide_eq_true e5, e1, e2, e3, decide_eq_true hj]
    simp
  · rw [testBit_byte (he r hr c hc) (by omega)]
    simp [hj]

theorem nadd (a b : Nat) : Nat.add a b = a + b := rfl
theorem nmul (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nland (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem nlor (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem nxor (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem nshr (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem nshl (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl

theorem L1_eq : L1 = lanes 8 (fun q => if q % 8 < 6 then 1 else 0) 48 := by decide

theorem L3_eq : L3 = lanes 8 (fun q => if q % 8 < 6 then 3 else 0) 48 := by decide

theorem L63_eq : L63 = lanes 8 (fun q => if q % 8 < 6 then 63 else 0) 48 := by decide

theorem COL_eq : COL = lanes 64 (fun _ => 255) 6 := by decide

theorem ROW_eq : ROW = 2 ^ 48 - 1 := by decide

theorem L1_pk : L1 = pk fun _ _ => 1 := L1_eq

theorem L3_pk : L3 = pk fun _ _ => 3 := L3_eq

theorem lanes_shr_and {n s : Nat} {f g : Nat → Nat} (hs : s ≤ 8) (hf : ∀ q < n, f q < 2 ^ 8)
    (hg : ∀ q < n, g q < 2 ^ (8 - s)) :
    (lanes 8 f n >>> s) &&& lanes 8 g n = lanes 8 (fun q => (f q >>> s) &&& g q) n := by
  have hg' : ∀ q < n, g q < 2 ^ 8 := fun q hq =>
    Nat.lt_of_lt_of_le (hg q hq) (Nat.pow_le_pow_right (by decide) (by omega))
  have hr : ∀ q < n, (f q >>> s) &&& g q < 2 ^ 8 := fun q hq =>
    Nat.lt_of_le_of_lt Nat.and_le_right (hg' q hq)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_lanes (by decide) n hf,
    testBit_lanes (by decide) n hg', testBit_lanes (by decide) n hr, Nat.testBit_and,
    Nat.testBit_shiftRight]
  by_cases hi : i < 8 * n
  · by_cases hm : i % 8 < 8 - s
    · have e1 : (s + i) / 8 = i / 8 := by omega
      have e2 : (s + i) % 8 = s + i % 8 := by omega
      have e3 : s + i < 8 * n := by omega
      rw [decide_eq_true hi, decide_eq_true e3, e1, e2]
      simp
    · have hz : (g (i / 8)).testBit (i % 8) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hg _ (by omega))
          (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hz]
  · have e3 : ¬ s + i < 8 * n := by omega
    simp [hi, e3]

theorem lanes_and {n : Nat} {f g : Nat → Nat} (hf : ∀ q < n, f q < 2 ^ 8)
    (hg : ∀ q < n, g q < 2 ^ 8) :
    lanes 8 f n &&& lanes 8 g n = lanes 8 (fun q => f q &&& g q) n := by
  have h := lanes_shr_and (s := 0) (by decide) hf hg
  simpa using h

theorem lanes_or {n : Nat} {f g : Nat → Nat} (hf : ∀ q < n, f q < 2 ^ 8)
    (hg : ∀ q < n, g q < 2 ^ 8) :
    lanes 8 f n ||| lanes 8 g n = lanes 8 (fun q => f q ||| g q) n := by
  have hr : ∀ q < n, f q ||| g q < 2 ^ 8 := fun q hq => Nat.or_lt_two_pow (hf q hq) (hg q hq)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_lanes (by decide) n hf, testBit_lanes (by decide) n hg,
    testBit_lanes (by decide) n hr, Nat.testBit_or]
  by_cases hi : i < 8 * n <;> simp [hi]

theorem lanes_xor {n : Nat} {f g : Nat → Nat} (hf : ∀ q < n, f q < 2 ^ 8)
    (hg : ∀ q < n, g q < 2 ^ 8) :
    lanes 8 f n ^^^ lanes 8 g n = lanes 8 (fun q => f q ^^^ g q) n := by
  have hr : ∀ q < n, f q ^^^ g q < 2 ^ 8 := fun q hq => Nat.xor_lt_two_pow (hf q hq) (hg q hq)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_lanes (by decide) n hf, testBit_lanes (by decide) n hg,
    testBit_lanes (by decide) n hr, Nat.testBit_xor]
  by_cases hi : i < 8 * n <;> simp [hi]

theorem lanes_shl1 (n : Nat) (f : Nat → Nat) : lanes 8 f n <<< 1 = lanes 8 (fun q => 2 * f q) n := by
  rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, lanes_mul_const]

theorem lanes_step {n : Nat} {f a b : Nat → Nat} (hf : ∀ q < n, f q < 2 ^ 8)
    (ha : ∀ q < n, a q < 2 ^ (8 - 2)) (hb : ∀ q < n, b q < 2 ^ 8) :
    ((lanes 8 f n >>> 2) &&& lanes 8 a n) + (lanes 8 f n &&& lanes 8 b n) =
      lanes 8 (fun q => ((f q >>> 2) &&& a q) + (f q &&& b q)) n := by
  rw [lanes_shr_and (by decide) hf ha, lanes_and hf hb, lanes_add]

theorem lanes_carry {n : Nat} {f a : Nat → Nat} (hf : ∀ q < n, f q < 2 ^ 8)
    (ha : ∀ q < n, a q < 2 ^ (8 - 1)) :
    (lanes 8 f n &&& (lanes 8 f n >>> 1)) &&& lanes 8 a n =
      lanes 8 (fun q => f q &&& ((f q >>> 1) &&& a q)) n := by
  have hr : ∀ q < n, (f q >>> 1) &&& a q < 2 ^ 8 := fun q hq =>
    Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_of_lt_of_le (ha q hq) (by decide))
  have e : (lanes 8 f n &&& (lanes 8 f n >>> 1)) &&& lanes 8 a n =
      lanes 8 f n &&& ((lanes 8 f n >>> 1) &&& lanes 8 a n) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Bool.and_assoc]
  rw [e, lanes_shr_and (by decide) hf ha, lanes_and hf hr]

@[expose] def fl (q : Nat) : Nat := if q % 8 < 6 then 1 else 0

theorem byte_cases {f : Nat → Nat} (hf : ∀ q < 48, f q < 25) (hz : ∀ q, ¬ q % 8 < 6 → f q = 0)
    (P : Nat → Nat → Prop) (h1 : ∀ v < 25, P 1 v) (h0 : P 0 0) : ∀ q < 48, P (fl q) (f q) := by
  intro q hq
  unfold fl
  by_cases h : q % 8 < 6
  · rw [if_pos h]
    exact h1 _ (hf q hq)
  · rw [if_neg h, hz q h]
    exact h0

theorem lanes_fl (c : Nat) :
    lanes 8 (fun q => if q % 8 < 6 then c else 0) 48 = lanes 8 (fun q => c * fl q) 48 := by
  apply lanes_congr
  intro q _
  unfold fl
  split <;> simp

theorem redK_lanes {f : Nat → Nat} (hf : ∀ q < 48, f q < 25) (hz : ∀ q, ¬ q % 8 < 6 → f q = 0) :
    redK (lanes 8 f 48) = lanes 8 (fun q => f q % 3) 48 := by
  unfold redK
  simp only [strictN_eq, nadd, nland, nshr, nshl, nxor, nlor]
  rw [L63_eq, L3_eq, L1_eq, lanes_fl, lanes_fl, lanes_fl]
  have b0 := byte_cases hf hz (fun b v => v < 2 ^ 8) (by decide) (by decide)
  have b63 := byte_cases hf hz (fun b _ => 63 * b < 2 ^ (8 - 2)) (by decide) (by decide)
  have b3 := byte_cases hf hz (fun b _ => 3 * b < 2 ^ 8) (by decide) (by decide)
  have b32 := byte_cases hf hz (fun b _ => 3 * b < 2 ^ (8 - 2)) (by decide) (by decide)
  have b12 := byte_cases hf hz (fun b _ => 1 * b < 2 ^ (8 - 2)) (by decide) (by decide)
  have b11 := byte_cases hf hz (fun b _ => 1 * b < 2 ^ (8 - 1)) (by decide) (by decide)
  rw [lanes_step b0 b63 b3]
  have c1 := byte_cases hf hz (fun b v => ((v >>> 2) &&& 63 * b) + (v &&& 3 * b) < 2 ^ 8)
    (by decide) (by decide)
  rw [lanes_step c1 b32 b3]
  have c2 := byte_cases hf hz (fun b v =>
    ((((v >>> 2) &&& 63 * b) + (v &&& 3 * b)) >>> 2 &&& 3 * b) +
      ((((v >>> 2) &&& 63 * b) + (v &&& 3 * b)) &&& 3 * b) < 2 ^ 8) (by decide) (by decide)
  rw [lanes_step c2 b12 b3, lanes_carry ?_ b11, lanes_shl1, lanes_or ?_ ?_, lanes_xor ?_ ?_]
  apply lanes_congr
  all_goals
    intro q hq
    have h := hf q hq
    try dsimp only
    unfold fl
    by_cases h6 : q % 8 < 6
    · simp only [if_pos h6]
      generalize f q = v at h ⊢
      revert v
      decide
    · simp only [if_neg h6, hz q h6]
      decide

theorem redK_pk {s : Nat → Nat → Nat} (hs : ∀ r < 6, ∀ c < 6, s r c < 25) :
    redK (pk s) = pk fun r c => s r c % 3 := by
  unfold pk
  rw [redK_lanes (flat_lt (by decide) hs) (fun q hq => by unfold flat; rw [if_neg hq])]
  apply lanes_congr
  intro q _
  unfold flat
  split <;> simp

theorem lanes2_pk {s : Nat → Nat → Nat} (hs : ∀ r < 6, ∀ c < 6, s r c < 256) :
    lanes 64 (fun r => lanes 8 (s r) 6) 6 = pk s := by
  have hin : ∀ r < 6, lanes 8 (s r) 6 < 2 ^ 64 := fun r hr =>
    Nat.lt_of_lt_of_le (lanes_lt 6 (fun c hc => hs r hr c hc))
      (Nat.pow_le_pow_right (by decide) (by decide))
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_lanes (by decide) 6 hin, testBit_pk hs]
  by_cases hi : i < 384
  · rw [testBit_lanes (by decide) 6 (fun c hc => hs _ (by omega) c hc)]
    have e : i % 64 % 8 = i % 8 := by omega
    rw [e]
    simp [hi]
  · simp [hi]

theorem colK_pk {e : Nat → Nat → Nat} (he : ∀ r < 6, ∀ c < 6, e r c < 256) {j : Nat} (hj : j < 6) :
    colK (encS (pk e)) j = lanes 64 (fun r => e r j) 6 := by
  have hc : ∀ r < 6, e r j < 2 ^ 64 := fun r hr =>
    Nat.lt_of_lt_of_le (he r hr j hj) (by decide)
  unfold colK
  simp only [nland, nshr, nadd, nmul]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_assoc, testBit_encS_hi, testBit_pk he,
    COL_eq, testBit_lanes (by decide) 6 (fun _ _ => by decide) i, testBit_lanes (by decide) 6 hc i,
    testBit_255]
  by_cases hi : i < 384
  · by_cases h1 : i % 64 < 8
    · have e1 : 8 * j + i < 384 := by omega
      have e2 : (8 * j + i) % 64 < 48 := by omega
      have e3 : (8 * j + i) / 64 = i / 64 := by omega
      have e4 : (8 * j + i) % 64 / 8 = j := by omega
      have e5 : (8 * j + i) % 8 = i % 64 := by omega
      rw [decide_eq_true e1, decide_eq_true e2, e3, e4, e5]
      simp [hi, h1]
    · rw [testBit_byte (he _ (by omega) j hj) (by omega)]
      simp [h1]
  · simp [hi]

theorem rowK_pk {e : Nat → Nat → Nat} (he : ∀ r < 6, ∀ c < 6, e r c < 256) {j : Nat} (hj : j < 6) :
    rowK (encS (pk e)) j = lanes 8 (e j) 6 := by
  have hc : ∀ c < 6, e j c < 2 ^ 8 := fun c hc => he j hj c hc
  unfold rowK
  simp only [nland, nshr, nadd, nmul]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_assoc, testBit_encS_hi, testBit_pk he,
    ROW_eq, Nat.testBit_two_pow_sub_one, testBit_lanes (by decide) 6 hc i]
  by_cases hi : i < 48
  · have e1 : 64 * j + i < 384 := by omega
    have e2 : (64 * j + i) % 64 < 48 := by omega
    have e3 : (64 * j + i) / 64 = j := by omega
    have e4 : (64 * j + i) % 64 / 8 = i / 8 := by omega
    have e5 : (64 * j + i) % 8 = i % 8 := by omega
    rw [decide_eq_true e1, decide_eq_true e2, e3, e4, e5]
    simp [hi]
  · simp [hi]

theorem lanes_prod (a b : Nat → Nat) :
    lanes 64 a 6 * lanes 8 b 6 = lanes 64 (fun r => lanes 8 (fun c => a r * b c) 6) 6 := by
  rw [Nat.mul_comm, lanes_mul_const]
  apply lanes_congr
  intro r _
  try dsimp only
  rw [Nat.mul_comm, lanes_mul_const]

@[expose] def mulE (a b : Nat → Nat → Nat) (r c : Nat) : Nat :=
  ((a r 0 * b 0 c + a r 1 * b 1 c) + (a r 2 * b 2 c + a r 3 * b 3 c)) +
    (a r 4 * b 4 c + a r 5 * b 5 c)

theorem mulE_lt {a b : Nat → Nat → Nat} (ha : ∀ r < 6, ∀ c < 6, a r c < 3)
    (hb : ∀ r < 6, ∀ c < 6, b r c < 3) : ∀ r < 6, ∀ c < 6, mulE a b r c < 25 := by
  intro r hr c hc
  have hp : ∀ k < 6, a r k * b k c ≤ 4 := fun k hk =>
    Nat.mul_le_mul (Nat.le_of_lt_succ (ha r hr k hk)) (Nat.le_of_lt_succ (hb k hk c hc))
  have h := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (hp 0 (by decide)) (hp 1 (by decide)))
    (Nat.add_le_add (hp 2 (by decide)) (hp 3 (by decide))))
    (Nat.add_le_add (hp 4 (by decide)) (hp 5 (by decide)))
  exact Nat.lt_of_le_of_lt h (by decide)

theorem mulK_pk {a b : Nat → Nat → Nat} (ha : ∀ r < 6, ∀ c < 6, a r c < 3)
    (hb : ∀ r < 6, ∀ c < 6, b r c < 3) :
    mulK (encS (pk a)) (encS (pk b)) = encS (pk fun r c => mulE a b r c % 3) := by
  have ha' : ∀ r < 6, ∀ c < 6, a r c < 256 := fun r hr c hc =>
    Nat.lt_trans (ha r hr c hc) (by decide)
  have hb' : ∀ r < 6, ∀ c < 6, b r c < 256 := fun r hr c hc =>
    Nat.lt_trans (hb r hr c hc) (by decide)
  have hs := mulE_lt ha hb
  unfold mulK
  rw [colK_pk ha' (by decide : 0 < 6), colK_pk ha' (by decide : 1 < 6),
    colK_pk ha' (by decide : 2 < 6), colK_pk ha' (by decide : 3 < 6),
    colK_pk ha' (by decide : 4 < 6), colK_pk ha' (by decide : 5 < 6),
    rowK_pk hb' (by decide : 0 < 6), rowK_pk hb' (by decide : 1 < 6),
    rowK_pk hb' (by decide : 2 < 6), rowK_pk hb' (by decide : 3 < 6),
    rowK_pk hb' (by decide : 4 < 6), rowK_pk hb' (by decide : 5 < 6)]
  simp only [nadd, nmul, lanes_prod, lanes_add]
  rw [lanes2_pk ?_, redK_pk ?_]
  all_goals first
    | rfl
    | exact hs
    | exact fun r hr c hc => Nat.lt_trans (hs r hr c hc) (by decide)

theorem testBit_3 (j : Nat) : (3 : Nat).testBit j = decide (j < 2) := by
  have h : (3 : Nat) = 2 ^ 2 - 1 := by decide
  rw [h, Nat.testBit_two_pow_sub_one]

theorem testBit_1 (j : Nat) : (1 : Nat).testBit j = decide (j < 1) := by
  have h := Nat.testBit_two_pow_sub_one 1 j
  simpa using h

theorem const_lt {k : Nat} (hk : k < 256) : ∀ r < 6, ∀ c < 6, (fun _ _ => k) r c < 256 :=
  fun _ _ _ _ => hk

theorem validK_pk {e : Nat → Nat → Nat} (he : ∀ r < 6, ∀ c < 6, e r c < 3) :
    validK (encS (pk e)) = true := by
  have he' : ∀ r < 6, ∀ c < 6, e r c < 256 := fun r hr c hc =>
    Nat.lt_trans (he r hr c hc) (by decide)
  unfold validK
  simp only [andB_eq, nshr, nland, encS_shr, Bool.and_eq_true, Nat.beq_eq]
  refine ⟨trivial, ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, L3_pk, testBit_pk he', testBit_pk (const_lt (k := 3) (by decide)),
      testBit_3]
    by_cases hi : i < 384 ∧ i % 64 < 48
    · have hv := he (i / 64) (by omega) (i % 64 / 8) (by omega)
      have hk : ∀ v < 3, ∀ k < 8, (v.testBit k && decide (k < 2)) = v.testBit k := by decide
      rw [decide_eq_true hi.1, decide_eq_true hi.2]
      simp only [Bool.true_and]
      exact hk _ hv _ (Nat.mod_lt _ (by decide))
    · rcases Classical.not_and_iff_not_or_not.1 hi with h | h <;> simp [h]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, L1_pk, testBit_pk he',
      testBit_pk he', testBit_pk (const_lt (k := 1) (by decide)), testBit_1, Nat.zero_testBit]
    by_cases hi : i < 384 ∧ i % 64 < 48 ∧ i % 8 < 1
    · have e1 : 1 + i < 384 := by omega
      have e2 : (1 + i) % 64 < 48 := by omega
      have e3 : (1 + i) / 64 = i / 64 := by omega
      have e4 : (1 + i) % 64 / 8 = i % 64 / 8 := by omega
      have e5 : (1 + i) % 8 = 1 := by omega
      have e6 : i % 8 = 0 := by omega
      have hv := he (i / 64) (by omega) (i % 64 / 8) (by omega)
      have hk : ∀ v < 3, (v.testBit 0 && v.testBit 1) = false := by decide
      rw [decide_eq_true e1, decide_eq_true e2, e3, e4, e5, decide_eq_true hi.1,
        decide_eq_true hi.2.1, e6]
      rw [decide_eq_true (by decide : (0 : Nat) < 1)]
      simp only [Bool.true_and, Bool.and_true]
      exact hk _ hv
    · rcases Classical.not_and_iff_not_or_not.1 hi with h | h
      · simp [h]
      · rcases Classical.not_and_iff_not_or_not.1 h with h | h <;> simp [h]

theorem validK_ent {x : Nat} (h : validK x = true) :
    (∀ r < 6, ∀ c < 6, ent x r c < 3) ∧ x = encS (pk (ent x)) := by
  unfold validK at h
  simp only [andB_eq, nshr, nland, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hm : ∀ i, x.testBit (64 + i) = true → i < 384 ∧ i % 64 < 48 ∧ i % 8 < 2 := by
    intro i hi
    have hc := congrArg (fun y => y.testBit i) h2
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, hi, L3_pk,
      testBit_pk (const_lt (k := 3) (by decide)), testBit_3, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2⟩
  have hpk : pk (ent x) = x >>> 64 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [testBit_pk (fun r _ c _ => ent_lt x r c), testBit_ent, Nat.testBit_shiftRight]
    have e : 64 + 64 * (i / 64) + 8 * (i % 64 / 8) + i % 8 = 64 + i := by omega
    have e8 : i % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [e, decide_eq_true e8]
    cases hb : x.testBit (64 + i)
    · simp
    · obtain ⟨a1, a2, _⟩ := hm i hb
      simp [a1, a2]
  have hb : ∀ r < 6, ∀ c < 6, ent x r c < 3 := by
    intro r hr c hc
    have e0 : ∀ j, 64 + 64 * r + 8 * c + j = 64 + (64 * r + 8 * c + j) := fun j => by omega
    have h4 : ent x r c < 2 ^ 2 := by
      apply Nat.lt_pow_two_of_testBit
      intro j hj
      rw [testBit_ent, e0]
      by_cases hj8 : j < 8
      · cases hbit : x.testBit (64 + (64 * r + 8 * c + j))
        · simp
        · have := (hm _ hbit).2.2
          omega
      · simp [hj8]
    have hn : ((ent x r c).testBit 0 && (ent x r c).testBit 1) = false := by
      have hc3 := congrArg (fun y => y.testBit (64 * r + 8 * c)) h3
      have f1 : 64 * r + 8 * c < 384 := by omega
      have f2 : (64 * r + 8 * c) % 64 < 48 := by omega
      have f3 : (64 * r + 8 * c) % 8 < 1 := by omega
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, L1_pk,
        testBit_pk (const_lt (k := 1) (by decide)), testBit_1, Nat.zero_testBit,
        decide_eq_true f1, decide_eq_true f2, decide_eq_true f3, Bool.and_true] at hc3
      rw [testBit_ent, testBit_ent, e0, e0]
      have f4 : 64 + (1 + (64 * r + 8 * c)) = 64 + (64 * r + 8 * c + 1) := by omega
      rw [f4] at hc3
      simpa using hc3
    have key : ∀ v < 4, (v.testBit 0 && v.testBit 1) = false → v < 3 := by decide
    exact key _ h4 hn
  exact ⟨hb, by rw [hpk]; exact h1.symm⟩

theorem decM_eq (x : Nat) :
    decM x = Array.ofFn (n := 36) fun p => ent x (p.val / 6) (p.val % 6) := rfl

theorem decM_encS_pk {e : Nat → Nat → Nat} (he : ∀ r < 6, ∀ c < 6, e r c < 256) :
    decM (encS (pk e)) = Array.ofFn (n := 36) fun p => e (p.val / 6) (p.val % 6) := by
  rw [decM_eq]
  congr 1
  funext p
  have := p.isLt
  exact ent_encS_pk he (by omega) (by omega)

theorem get!_ofFn (A : Nat → Nat → Nat) {j : Nat} (hj : j < 36) :
    (Array.ofFn (n := 36) fun p => A (p.val / 6) (p.val % 6))[j]! = A (j / 6) (j % 6) := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

theorem div6 {r k : Nat} (hk : k < 6) : (6 * r + k) / 6 = r := by omega

theorem mod6 {r k : Nat} (hk : k < 6) : (6 * r + k) % 6 = k := by omega

theorem mulN_ofFn (A B : Nat → Nat → Nat) :
    Certificates.A6C.mulN 6 (Array.ofFn (n := 36) fun p => A (p.val / 6) (p.val % 6))
      (Array.ofFn (n := 36) fun p => B (p.val / 6) (p.val % 6)) =
      Array.ofFn (n := 36) fun p => mulE A B (p.val / 6) (p.val % 6) % 3 := by
  apply Array.ext
  · simp [Certificates.A6C.mulN]
  · intro i h1 h2
    have hi : i < 36 := by simpa using h2
    have hr : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
    have hk : i % 6 < 6 := Nat.mod_lt _ (by decide)
    simp only [Certificates.A6C.mulN, Array.getElem_ofFn, hr, List.foldl]
    simp (disch := omega) only [get!_ofFn A, get!_ofFn B, div6, mod6]
    unfold mulE
    rw [Nat.zero_add]
    congr 1
    ac_rfl

theorem decM_mulK {x y : Nat} (hx : validK x = true) (hy : validK y = true) :
    validK (mulK x y) = true ∧ decM (mulK x y) = Certificates.A6C.mulN 6 (decM x) (decM y) := by
  obtain ⟨hxe, hxp⟩ := validK_ent hx
  obtain ⟨hye, hyp⟩ := validK_ent hy
  generalize ent x = a at hxe hxp
  generalize ent y = b at hye hyp
  subst hxp hyp
  have h3 : ∀ r < 6, ∀ c < 6, mulE a b r c % 3 < 3 := fun _ _ _ _ => Nat.mod_lt _ (by decide)
  have ha' : ∀ r < 6, ∀ c < 6, a r c < 256 := fun r hr c hc =>
    Nat.lt_trans (hxe r hr c hc) (by decide)
  have hb' : ∀ r < 6, ∀ c < 6, b r c < 256 := fun r hr c hc =>
    Nat.lt_trans (hye r hr c hc) (by decide)
  rw [mulK_pk hxe hye]
  refine ⟨validK_pk h3, ?_⟩
  rw [decM_encS_pk (fun r hr c hc => Nat.lt_trans (h3 r hr c hc) (by decide)), decM_encS_pk ha',
    decM_encS_pk hb', mulN_ofFn]

theorem negK_pk {e : Nat → Nat → Nat} (he : ∀ r < 6, ∀ c < 6, e r c < 3) :
    negK (encS (pk e)) = encS (pk fun r c => 2 * e r c % 3) := by
  unfold negK negM
  simp only [nshr, nland, nlor, nshl, encS_shr]
  unfold pk
  have hf : ∀ q < 48, flat e q < 3 := flat_lt (by decide) he
  have hb8 : ∀ q < 48, flat e q < 2 ^ 8 := fun q hq => Nat.lt_trans (hf q hq) (by decide)
  have hm : ∀ q < 48, (if q % 8 < 6 then 1 else 0) < 2 ^ (8 - 1) := fun q _ => by
    split <;> decide
  have hm8 : ∀ q < 48, (if q % 8 < 6 then 1 else 0) < 2 ^ 8 := fun q _ => by
    split <;> decide
  have ha : ∀ q < 48, 2 * (flat e q &&& if q % 8 < 6 then 1 else 0) < 2 ^ 8 := fun q hq =>
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 Nat.and_le_right)
      (by have := hm q hq; omega)
  have hc : ∀ q < 48, (flat e q >>> 1 &&& if q % 8 < 6 then 1 else 0) < 2 ^ 8 := fun q hq =>
    Nat.lt_of_le_of_lt Nat.and_le_right (hm8 q hq)
  rw [L1_eq, lanes_and hb8 hm8, lanes_shl1, lanes_shr_and (by decide) hb8 hm, lanes_or ha hc]
  apply congrArg encS
  apply lanes_congr
  intro q hq
  have hv := hf q hq
  unfold flat at hv ⊢
  by_cases h6 : q % 8 < 6
  · simp only [if_pos h6] at hv ⊢
    generalize e (q / 8) (q % 8) = v at hv ⊢
    revert v
    decide
  · simp only [if_neg h6]
    decide

theorem decM_negK {x : Nat} (hx : validK x = true) :
    validK (negK x) = true ∧ decM (negK x) = Certificates.A6C.negM (decM x) := by
  obtain ⟨hxe, hxp⟩ := validK_ent hx
  generalize ent x = a at hxe hxp
  subst hxp
  have h3 : ∀ r < 6, ∀ c < 6, 2 * a r c % 3 < 3 := fun _ _ _ _ => Nat.mod_lt _ (by decide)
  have ha' : ∀ r < 6, ∀ c < 6, a r c < 256 := fun r hr c hc =>
    Nat.lt_trans (hxe r hr c hc) (by decide)
  rw [negK_pk hxe]
  refine ⟨validK_pk h3, ?_⟩
  rw [decM_encS_pk (fun r hr c hc => Nat.lt_trans (h3 r hr c hc) (by decide)), decM_encS_pk ha',
    Certificates.A6C.negM, Array.map_ofFn]
  rfl

theorem validK_IDK : validK IDK = true := by decide

theorem decM_IDK : decM IDK = Certificates.A6C.idN 6 := by decide

theorem decM_inj {x y : Nat} (hx : validK x = true) (hy : validK y = true) (h : decM x = decM y) :
    x = y := by
  have he : ∀ r < 6, ∀ c < 6, ent x r c = ent y r c := by
    intro r hr c hc
    have h1 := congrArg (fun A => A[6 * r + c]!) h
    simp only [decM_eq] at h1
    rw [get!_ofFn (ent x) (by omega), get!_ofFn (ent y) (by omega), div6 hc, mod6 hc] at h1
    exact h1
  rw [(validK_ent hx).2, (validK_ent hy).2]
  have hl : lanes 8 (flat (ent x)) 48 = lanes 8 (flat (ent y)) 48 := by
    apply lanes_congr
    intro q hq
    unfold flat
    split
    · exact he _ (by omega) _ (by omega)
    · rfl
  unfold pk
  rw [hl]

theorem beq_decM {x y : Nat} (hx : validK x = true) (hy : validK y = true) :
    Nat.beq x y = (decM x == decM y) := by
  rw [Bool.eq_iff_iff]
  simp only [Nat.beq_eq, beq_iff_eq]
  exact ⟨fun h => h ▸ rfl, decM_inj hx hy⟩

@[expose] noncomputable def trT (x p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun p ih => strictN ih fun s =>
      Nat.lor s (Nat.shiftLeft
        (Nat.land (Nat.shiftRight x
          (Nat.add 64 (Nat.add (Nat.mul 64 (Nat.div p 6)) (Nat.mul 8 (Nat.mod p 6))))) 255)
        (Nat.add (Nat.mul 64 (Nat.mod p 6)) (Nat.mul 8 (Nat.div p 6)))))
    p

theorem trK_eq (x : Nat) : trK x = encS (trT x 36) := rfl

theorem trT_succ (x p : Nat) : trT x (p + 1) =
    trT x p ||| (((x >>> (64 + (64 * (p / 6) + 8 * (p % 6)))) &&& 255) <<<
      (64 * (p % 6) + 8 * (p / 6))) := by
  have h : trT x (p + 1) = strictN (trT x p) fun s =>
      Nat.lor s (Nat.shiftLeft
        (Nat.land (Nat.shiftRight x
          (Nat.add 64 (Nat.add (Nat.mul 64 (Nat.div p 6)) (Nat.mul 8 (Nat.mod p 6))))) 255)
        (Nat.add (Nat.mul 64 (Nat.mod p 6)) (Nat.mul 8 (Nat.div p 6)))) := rfl
  rw [h, strictN_eq]
  rfl

theorem testBit_trT (x : Nat) : ∀ p ≤ 36, ∀ i, (trT x p).testBit i =
    (decide (i < 384) && decide (i % 64 < 48) && decide (6 * (i % 64 / 8) + i / 64 < p) &&
      x.testBit (64 + 64 * (i % 64 / 8) + 8 * (i / 64) + i % 8))
  | 0, _, i => by
    change (0 : Nat).testBit i = _
    simp
  | p + 1, hp, i => by
    rw [trT_succ, Nat.testBit_or, testBit_trT x p (by omega) i, Nat.testBit_shiftLeft,
      Nat.testBit_and, Nat.testBit_shiftRight, testBit_255]
    by_cases h1 : 6 * (i % 64 / 8) + i / 64 = p ∧ i < 384 ∧ i % 64 < 48
    · obtain ⟨e1, e2, e3⟩ := h1
      have g1 : i ≥ 64 * (p % 6) + 8 * (p / 6) := by omega
      have g2 : i - (64 * (p % 6) + 8 * (p / 6)) < 8 := by omega
      have g3 : 64 + (64 * (p / 6) + 8 * (p % 6)) + (i - (64 * (p % 6) + 8 * (p / 6))) =
          64 + 64 * (i % 64 / 8) + 8 * (i / 64) + i % 8 := by omega
      have g4 : ¬ (6 * (i % 64 / 8) + i / 64 < p) := by omega
      have g5 : 6 * (i % 64 / 8) + i / 64 < p + 1 := by omega
      rw [g3, decide_eq_true g1, decide_eq_true g2, decide_eq_false g4, decide_eq_true g5,
        decide_eq_true e2, decide_eq_true e3]
      simp
    · have g1 : ¬ (i ≥ 64 * (p % 6) + 8 * (p / 6) ∧ i - (64 * (p % 6) + 8 * (p / 6)) < 8) := by
        rintro ⟨ga, gb⟩
        have q1 : p % 6 < 6 := Nat.mod_lt _ (by decide)
        have q2 : p / 6 < 6 := by omega
        have q3 : i / 64 = p % 6 := by omega
        have q4 : i % 64 = 8 * (p / 6) + (i - (64 * (p % 6) + 8 * (p / 6))) := by omega
        have q5 : i % 64 / 8 = p / 6 := by omega
        have q6 : 6 * (i % 64 / 8) + i / 64 = p := by rw [q3, q5]; omega
        exact h1 ⟨q6, by omega, by omega⟩
      have g2 : (decide (i ≥ 64 * (p % 6) + 8 * (p / 6)) &&
          (x.testBit (64 + (64 * (p / 6) + 8 * (p % 6)) + (i - (64 * (p % 6) + 8 * (p / 6)))) &&
            decide (i - (64 * (p % 6) + 8 * (p / 6)) < 8))) = false := by
        by_cases g : i ≥ 64 * (p % 6) + 8 * (p / 6)
        · have g' : ¬ i - (64 * (p % 6) + 8 * (p / 6)) < 8 := fun h => g1 ⟨g, h⟩
          simp [g']
        · simp [g]
      rw [g2, Bool.or_false]
      by_cases g3 : 6 * (i % 64 / 8) + i / 64 < p
      · have g4 : 6 * (i % 64 / 8) + i / 64 < p + 1 := by omega
        rw [decide_eq_true g3, decide_eq_true g4]
      · rw [decide_eq_false g3]
        by_cases g5 : i < 384 ∧ i % 64 < 48
        · have g4 : ¬ 6 * (i % 64 / 8) + i / 64 < p + 1 := by omega
          rw [decide_eq_false g4]
        · rcases Classical.not_and_iff_not_or_not.1 g5 with h | h <;> simp [h]

theorem trK_valid (x : Nat) : trK x = encS (pk fun r c => ent x c r) := by
  rw [trK_eq]
  apply congrArg encS
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_trT x 36 (Nat.le_refl _), testBit_pk (fun r _ c _ => ent_lt x c r), testBit_ent]
  by_cases h : i < 384 ∧ i % 64 < 48
  · have g1 : 6 * (i % 64 / 8) + i / 64 < 36 := by omega
    have g2 : i % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [decide_eq_true g1, decide_eq_true g2, decide_eq_true h.1, decide_eq_true h.2]
    simp
  · rcases Classical.not_and_iff_not_or_not.1 h with h | h <;> simp [h]

theorem decM_trK {x : Nat} (hx : validK x = true) :
    validK (trK x) = true ∧ decM (trK x) = Certificates.A6C.trN 6 (decM x) := by
  have hxe := (validK_ent hx).1
  rw [trK_valid]
  refine ⟨validK_pk fun r hr c hc => hxe c hc r hr, ?_⟩
  rw [decM_encS_pk fun r _ c _ => ent_lt x c r]
  apply Array.ext
  · simp [Certificates.A6C.trN]
  · intro i h1 h2
    have hi : i < 36 := by simpa using h1
    simp only [Certificates.A6C.trN, Array.getElem_ofFn, decM_eq]
    have hk : i / 6 < 6 := by omega
    rw [get!_ofFn (ent x) (by omega), div6 hk, mod6 hk]

theorem eqPK_eq {x y : Nat} (hx : validK x = true) (hy : validK y = true) :
    eqPK x y = Certificates.A6C.eqP (decM x) (decM y) := by
  unfold eqPK Certificates.A6C.eqP
  rw [orB_eq, beq_decM hx hy, beq_decM hx (decM_negK hy).1, (decM_negK hy).2]

theorem addK_pk {a b : Nat → Nat → Nat} (ha : ∀ r < 6, ∀ c < 6, a r c < 3)
    (hb : ∀ r < 6, ∀ c < 6, b r c < 3) :
    addK (encS (pk a)) (encS (pk b)) = encS (pk fun r c => (a r c + b r c) % 3) := by
  unfold addK
  simp only [nadd, nshr, encS_shr]
  have hs : ∀ r < 6, ∀ c < 6, a r c + b r c < 25 := fun r hr c hc => by
    have := ha r hr c hc
    have := hb r hr c hc
    omega
  have e : pk a + pk b = pk fun r c => a r c + b r c := by
    unfold pk
    rw [lanes_add]
    apply lanes_congr
    intro q _
    unfold flat
    split <;> rfl
  rw [e, redK_pk hs]

theorem decM_addK {x y : Nat} (hx : validK x = true) (hy : validK y = true) :
    validK (addK x y) = true ∧ decM (addK x y) = Certificates.A6C.addM (decM x) (decM y) := by
  obtain ⟨hxe, hxp⟩ := validK_ent hx
  obtain ⟨hye, hyp⟩ := validK_ent hy
  generalize ent x = a at hxe hxp
  generalize ent y = b at hye hyp
  subst hxp hyp
  have h3 : ∀ r < 6, ∀ c < 6, (a r c + b r c) % 3 < 3 := fun _ _ _ _ => Nat.mod_lt _ (by decide)
  have ha' : ∀ r < 6, ∀ c < 6, a r c < 256 := fun r hr c hc =>
    Nat.lt_trans (hxe r hr c hc) (by decide)
  have hb' : ∀ r < 6, ∀ c < 6, b r c < 256 := fun r hr c hc =>
    Nat.lt_trans (hye r hr c hc) (by decide)
  rw [addK_pk hxe hye]
  refine ⟨validK_pk h3, ?_⟩
  rw [decM_encS_pk (fun r hr c hc => Nat.lt_trans (h3 r hr c hc) (by decide)), decM_encS_pk ha',
    decM_encS_pk hb']
  apply Array.ext
  · simp [Certificates.A6C.addM]
  · intro i h1 h2
    have hi : i < 36 := by simpa using h1
    simp only [Certificates.A6C.addM, Array.getElem_ofFn]
    rw [get!_ofFn a hi, get!_ofFn b hi]

theorem entIDK : ∀ k < 6, ∀ c < 6, ent IDK k c = if k = c then 1 else 0 := by decide

theorem mulE_id {A : Nat → Nat → Nat} (hA : ∀ r < 6, ∀ c < 6, A r c < 3) {r c : Nat} (hr : r < 6)
    (hc : c < 6) : mulE A (ent IDK) r c % 3 = A r c := by
  unfold mulE
  rw [entIDK 0 (by decide) c hc, entIDK 1 (by decide) c hc, entIDK 2 (by decide) c hc,
    entIDK 3 (by decide) c hc, entIDK 4 (by decide) c hc, entIDK 5 (by decide) c hc]
  have h0 := hA r hr 0 (by decide)
  have h1 := hA r hr 1 (by decide)
  have h2 := hA r hr 2 (by decide)
  have h3 := hA r hr 3 (by decide)
  have h4 := hA r hr 4 (by decide)
  have h5 := hA r hr 5 (by decide)
  have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

theorem mulN_id {y : Nat} (hy : validK y = true) :
    Certificates.A6C.mulN 6 (decM y) (Certificates.A6C.idN 6) = decM y := by
  rw [← decM_IDK, decM_eq y, decM_eq IDK, mulN_ofFn]
  congr 1
  funext p
  have := p.isLt
  exact mulE_id (validK_ent hy).1 (by omega) (by omega)

theorem mulE_assoc (a b c : Nat → Nat → Nat) (r s : Nat) :
    mulE (fun r c => mulE a b r c % 3) c r s % 3 = mulE a (fun r s => mulE b c r s % 3) r s % 3 := by
  rw [← ZMod.natCast_eq_natCast_iff']
  simp only [mulE]
  push_cast [ZMod.natCast_mod]
  ring

theorem mulN_assoc (x y z : Nat) :
    Certificates.A6C.mulN 6 (Certificates.A6C.mulN 6 (decM x) (decM y)) (decM z) =
      Certificates.A6C.mulN 6 (decM x) (Certificates.A6C.mulN 6 (decM y) (decM z)) := by
  rw [decM_eq x, decM_eq y, decM_eq z, mulN_ofFn (ent x) (ent y), mulN_ofFn (ent y) (ent z),
    mulN_ofFn (fun r c => mulE (ent x) (ent y) r c % 3) (ent z),
    mulN_ofFn (ent x) (fun r c => mulE (ent y) (ent z) r c % 3)]
  congr 1
  funext p
  exact mulE_assoc _ _ _ _ _

theorem decM_pow4K {y : Nat} (hy : validK y = true) :
    validK (pow4K y) = true ∧ decM (pow4K y) = Certificates.A6C.powM 6 (decM y) 4 := by
  obtain ⟨v2, d2⟩ := decM_mulK hy hy
  unfold pow4K
  rw [strictN_eq]
  refine ⟨(decM_mulK v2 v2).1, ?_⟩
  rw [(decM_mulK v2 v2).2]
  simp only [Certificates.A6C.powM]
  rw [mulN_id hy, ← d2, ← mulN_assoc, ← d2]

theorem decM_pow5K {y : Nat} (hy : validK y = true) :
    validK (pow5K y) = true ∧ decM (pow5K y) = Certificates.A6C.powM 6 (decM y) 5 := by
  obtain ⟨v4, d4⟩ := decM_pow4K hy
  unfold pow5K
  refine ⟨(decM_mulK hy v4).1, ?_⟩
  rw [(decM_mulK hy v4).2, d4]
  rfl

theorem commK_eq {x y : Nat} (hx : validK x = true) (hy : validK y = true) :
    commK x y = Certificates.A6C.commP 6 (decM x) (decM y) := by
  unfold commK Certificates.A6C.commP
  rw [eqPK_eq (decM_mulK hx hy).1 (decM_mulK hy hx).1, (decM_mulK hx hy).2, (decM_mulK hy hx).2]

theorem relK_eq {a x : Nat} (ha : validK a = true) (hx : validK x = true) :
    relK a x = Certificates.A6C.relP 6 (decM a) (decM x) := by
  have vaa := (decM_mulK ha ha).1
  have vax := (decM_mulK ha hx).1
  have vxa := (decM_mulK hx ha).1
  have vxax := (decM_mulK vxa hx).1
  unfold relK Certificates.A6C.relP
  rw [andB_eq, andB_eq, eqPK_eq vaa validK_IDK, eqPK_eq (decM_pow4K vax).1 validK_IDK,
    eqPK_eq (decM_pow5K vxax).1 validK_IDK, decM_IDK, (decM_pow4K vax).2, (decM_pow5K vxax).2,
    (decM_mulK ha ha).2, (decM_mulK ha hx).2, (decM_mulK vxa hx).2, (decM_mulK hx ha).2,
    Bool.and_assoc]

theorem decM_size (x : Nat) : (decM x).size = 36 := by simp [decM_eq]

theorem simTK_eq {g gt : Nat} (h : simTK g gt = true) :
    validK g = true ∧ gt = trK g ∧ Certificates.A6C.simOK 6 (decM g) = true := by
  unfold simTK at h
  rw [andB_eq, andB_eq] at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨hv, ht⟩, he⟩ := h
  subst ht
  have vt := (decM_trK hv).1
  rw [eqPK_eq (decM_mulK hv vt).1 validK_IDK, (decM_mulK hv vt).2, (decM_trK hv).2,
    decM_IDK] at he
  refine ⟨hv, rfl, ?_⟩
  have hs : ((decM g).size == 6 * 6) = true := by simp [decM_size]
  have ha : (decM g).all (· < 3) = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi' : i < 36 := by rwa [decM_size] at hi
    simp only [decM_eq, Array.getElem_ofFn, decide_eq_true_eq]
    exact (validK_ent hv).1 _ (by omega) _ (by omega)
  unfold Certificates.A6C.simOK
  unfold Certificates.A6C.eqP at he
  rw [hs, ha, he]
  rfl

end CFSG.KC.A6CK
