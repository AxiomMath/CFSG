module

public import Certificates.Data.Kernel.LocLn.Defs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocLin
public import CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.Certificates.Kernel.ArrBfsSim
import CFSG.Certificates.Kernel.U43Pk.Sound
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KS.LocLn

open CFSG.KD.LocLn CFSG.KC.Enum CFSG.KC.Ord CFSG.KS.Ord
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc Matrix

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

structure KitF (K : Kit) : Prop where
  consts : constsOK 3 8 K.S K.n 5 K.L K.H K.CM K.RM K.ONEh K.LV K.HV = true
  pos : 1 ≤ K.n
  hS : K.S = K.n * 8
  hD : K.D = K.n * K.S
  hE : K.E2 = K.D + K.D
  hMA : K.MA = 2 ^ K.D - 1
  hM2 : K.M2 = K.ONEh + K.ONEh
  hONE : K.ONE = K.ONEh ||| K.ONEh <<< K.D
  hMONE : K.MONE = K.M2 ||| K.M2 <<< K.D

theorem kitF {K : Kit} (hK : kitOK K = true) : KitF K := by
  unfold kitOK at hK
  obtain ⟨h1, hK⟩ := andB_true hK
  obtain ⟨h2, hK⟩ := andB_true hK
  obtain ⟨h3, hK⟩ := andB_true hK
  obtain ⟨h4, hK⟩ := andB_true hK
  obtain ⟨h5, hK⟩ := andB_true hK
  obtain ⟨h6, hK⟩ := andB_true hK
  obtain ⟨h7, h8⟩ := andB_true hK
  have hc := h1
  unfold constsOK at h1
  obtain ⟨-, h1⟩ := andB_true h1
  obtain ⟨hS, -⟩ := andB_true h1
  have e5 : K.MA = 1 <<< K.D - 1 := Nat.eq_of_beq_eq_true h5
  rw [Nat.shiftLeft_eq, Nat.one_mul] at e5
  exact ⟨hc, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true hS, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, e5, Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7,
    Nat.eq_of_beq_eq_true h8⟩

theorem hD8 {K : Kit} (F : KitF K) : K.D = 8 * (K.n * K.n) := by
  rw [F.hD, F.hS]
  ring

theorem lane_mod {X m t : ℕ} (ht : t < m) : lane 8 (X % 2 ^ (8 * m)) t = lane 8 X t := by
  unfold lane
  have e : 2 ^ (8 * m) = 2 ^ (8 * t) * 2 ^ (8 * (m - t)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow 2 (by omega)

theorem lane_div (X s t : ℕ) : lane 8 (X / 2 ^ (8 * s)) t = lane 8 X (s + t) := by
  unfold lane
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_add]

theorem testBit_lane (X t c : ℕ) :
    (lane 8 X t).testBit c = (decide (c < 8) && X.testBit (c + 8 * t)) := by
  unfold lane
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

theorem lane_ext {X Y m : ℕ} (hX : X < 2 ^ (8 * m)) (hY : Y < 2 ^ (8 * m))
    (h : ∀ t < m, lane 8 X t = lane 8 Y t) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases Nat.lt_or_ge i (8 * m) with hi | hi
  · have e := congrArg (fun v => v.testBit (i % 8)) (h (i / 8) (by omega))
    simp only [testBit_lane] at e
    have e2 : i % 8 + 8 * (i / 8) = i := by omega
    rw [e2] at e
    simpa [Nat.mod_lt] using e
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hY (Nat.pow_le_pow_right (by norm_num) hi))]

theorem ordMat_lane {n M : ℕ} (i j : Fin n) :
    ordMat 3 n 8 (n * 8) M i j = ((lane 8 M (n * i.val + j.val) : ℕ) : ZMod 3) := by
  unfold ordMat lane
  have e : n * 8 * i.val + 8 * j.val = 8 * (n * i.val + j.val) := by ring
  rw [e]

theorem canon_inj {n X Y : ℕ} (hn : 0 < n) (hX : Canon 3 n 8 X) (hY : Canon 3 n 8 Y)
    (h : ordMat 3 n 8 (n * 8) X = ordMat 3 n 8 (n * 8) Y) : X = Y := by
  refine lane_ext hX.1 hY.1 fun t ht => ?_
  obtain ⟨i, j, hij⟩ := eA_index hn ht
  have e := congrFun (congrFun h i) j
  rw [ordMat_lane, ordMat_lane, hij] at e
  have := (cast_eq_iff (ZMod 3) (hY.2 t ht)).1 e
  rwa [Nat.mod_eq_of_lt (hX.2 t ht)] at this

@[expose] noncomputable def dec (n P : ℕ) : Array ℕ :=
  Array.ofFn (n := 2 * (n * n) + 1) fun k => lane 8 P k

theorem dec_size (n P : ℕ) : (dec n P).size = 2 * (n * n) + 1 := by simp [dec]

theorem dec_get {n P k : ℕ} (hk : k < 2 * (n * n) + 1) : (dec n P)[k]! = lane 8 P k := by
  unfold dec
  rw [CFSG.KS.U43Pk.ofFn_get _ hk]

@[expose] def Cd (K : Kit) (P : ℕ) : Prop :=
  Canon 3 K.n 8 (hA K P) ∧ Canon 3 K.n 8 (hB K P) ∧ eps K P < 2

theorem hA_eq {K : Kit} (F : KitF K) (P : ℕ) : hA K P = P % 2 ^ (8 * (K.n * K.n)) := by
  change P &&& K.MA = _
  rw [F.hMA, Nat.and_two_pow_sub_one_eq_mod, hD8 F]

theorem hB_eq {K : Kit} (F : KitF K) (P : ℕ) :
    hB K P = P / 2 ^ (8 * (K.n * K.n)) % 2 ^ (8 * (K.n * K.n)) := by
  change (P >>> K.D) &&& K.MA = _
  rw [F.hMA, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, hD8 F]

theorem eps_eq {K : Kit} (F : KitF K) (P : ℕ) : eps K P = P / 2 ^ (8 * (2 * (K.n * K.n))) := by
  change P >>> K.E2 = _
  rw [Nat.shiftRight_eq_div_pow, F.hE, hD8 F]
  ring_nf

theorem lane_hA {K : Kit} (F : KitF K) (P : ℕ) {t : ℕ} (ht : t < K.n * K.n) :
    lane 8 (hA K P) t = lane 8 P t := by
  rw [hA_eq F, lane_mod ht]

theorem lane_hB {K : Kit} (F : KitF K) (P : ℕ) {t : ℕ} (ht : t < K.n * K.n) :
    lane 8 (hB K P) t = lane 8 P (K.n * K.n + t) := by
  rw [hB_eq F, lane_mod ht, lane_div]

theorem dec_lt {K : Kit} (F : KitF K) {P : ℕ} (hP : Cd K P) :
    ∀ k < 2 * (K.n * K.n), (dec K.n P)[k]! < 3 := by
  intro k hk
  rw [dec_get (by omega)]
  rcases Nat.lt_or_ge k (K.n * K.n) with h | h
  · rw [← lane_hA F P h]
    exact hP.1.2 k h
  · have e : k = K.n * K.n + (k - K.n * K.n) := by omega
    rw [e, ← lane_hB F P (by omega)]
    exact hP.2.1.2 _ (by omega)

theorem dec_last {K : Kit} (F : KitF K) {P : ℕ} (hP : Cd K P) :
    (dec K.n P)[2 * (K.n * K.n)]! = eps K P := by
  rw [dec_get (by omega)]
  unfold lane
  rw [← eps_eq F, Nat.mod_eq_of_lt (by have := hP.2.2; omega)]

theorem eE_dec {K : Kit} (F : KitF K) {P : ℕ} (hP : Cd K P) : eE K.n (dec K.n P) = eps K P :=
  dec_last F hP

theorem mA_dec {K : Kit} (F : KitF K) (P : ℕ) :
    mA K.n (ZMod 3) (dec K.n P) = ordMat 3 K.n 8 K.S (hA K P) := by
  ext i j
  have hk := lt_mul_of_lt i.2 j.2
  simp only [mA, Matrix.of_apply, eA]
  rw [F.hS, ordMat_lane, dec_get (by omega), lane_hA F P hk]

theorem mB_dec {K : Kit} (F : KitF K) (P : ℕ) :
    mB K.n (ZMod 3) (dec K.n P) = ordMat 3 K.n 8 K.S (hB K P) := by
  ext i j
  have hk := lt_mul_of_lt i.2 j.2
  simp only [mB, Matrix.of_apply, eB]
  rw [F.hS, ordMat_lane, dec_get (by omega), lane_hB F P hk]

theorem arr_ext {n : ℕ} (hn : 0 < n) {x y : Array ℕ} (hxs : x.size = 2 * (n * n) + 1)
    (hys : y.size = 2 * (n * n) + 1) (hx : ∀ k < 2 * (n * n), x[k]! < 3)
    (hy : ∀ k < 2 * (n * n), y[k]! < 3) (he : x[2 * (n * n)]! = y[2 * (n * n)]!)
    (hA' : mA n (ZMod 3) x = mA n (ZMod 3) y) (hB' : mB n (ZMod 3) x = mB n (ZMod 3) y) :
    x = y := by
  have key : ∀ k < 2 * (n * n) + 1, x[k]! = y[k]! := by
    intro k hk
    rcases Nat.lt_or_ge k (n * n) with h1 | h1
    · have := ((mA_eq_iff (ZMod 3) hn x y).1 hA') k h1
      rwa [Nat.mod_eq_of_lt (hx k (by omega)), Nat.mod_eq_of_lt (hy k (by omega))] at this
    rcases Nat.lt_or_ge k (2 * (n * n)) with h2 | h2
    · obtain ⟨i, j, hij⟩ := eA_index hn (k := k - n * n) (by omega)
      have e := congrFun (congrFun hB' i) j
      simp only [mB, Matrix.of_apply, eB, hij] at e
      have e2 : n * n + (k - n * n) = k := by omega
      rw [e2] at e
      have := (cast_eq_iff (ZMod 3) (hy k h2)).1 e
      rwa [Nat.mod_eq_of_lt (hx k h2)] at this
    · obtain rfl : k = 2 * (n * n) := by omega
      exact he
  apply Array.ext (by rw [hxs, hys])
  intro k h1 h2
  rw [← getElem!_pos x k h1, ← getElem!_pos y k h2]
  exact key k (by omega)

theorem lor_comm' (a b : ℕ) : a ||| b = b ||| a :=
  Nat.eq_of_testBit_eq fun i => by simp [Bool.or_comm]

theorem mk_eq {K : Kit} (F : KitF K) {a b e : ℕ} (ha : a < 2 ^ K.D) (hb : b < 2 ^ K.D) :
    mk K a b e = a + 2 ^ K.D * (b + 2 ^ K.D * e) := by
  change (a ||| b <<< K.D) ||| e <<< K.E2 = _
  have h2 : b <<< K.D + a < 2 ^ K.E2 := by
    rw [Nat.shiftLeft_eq, F.hE, Nat.pow_add]
    calc b * 2 ^ K.D + a < b * 2 ^ K.D + 2 ^ K.D := by omega
      _ = (b + 1) * 2 ^ K.D := by ring
      _ ≤ 2 ^ K.D * 2 ^ K.D := Nat.mul_le_mul_right _ hb
  rw [lor_comm' a, ← Nat.shiftLeft_add_eq_or_of_lt ha, lor_comm',
    ← Nat.shiftLeft_add_eq_or_of_lt h2, Nat.shiftLeft_eq, Nat.shiftLeft_eq, F.hE, Nat.pow_add]
  ring

theorem hA_mk {K : Kit} (F : KitF K) {a b e : ℕ} (ha : a < 2 ^ K.D) (hb : b < 2 ^ K.D) :
    hA K (mk K a b e) = a := by
  rw [hA_eq F, ← hD8 F, mk_eq F ha hb, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem hB_mk {K : Kit} (F : KitF K) {a b e : ℕ} (ha : a < 2 ^ K.D) (hb : b < 2 ^ K.D) :
    hB K (mk K a b e) = b := by
  rw [hB_eq F, ← hD8 F, mk_eq F ha hb, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt ha, Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

theorem eps_mk {K : Kit} (F : KitF K) {a b e : ℕ} (ha : a < 2 ^ K.D) (hb : b < 2 ^ K.D) :
    eps K (mk K a b e) = e := by
  have e1 : 8 * (2 * (K.n * K.n)) = K.D + K.D := by rw [hD8 F]; ring
  rw [eps_eq F, e1, mk_eq F ha hb, Nat.pow_add]
  have e2 : a + 2 ^ K.D * (b + 2 ^ K.D * e) = (a + 2 ^ K.D * b) + 2 ^ K.D * 2 ^ K.D * e := by ring
  have h3 : a + 2 ^ K.D * b < 2 ^ K.D * 2 ^ K.D := by
    calc a + 2 ^ K.D * b < 2 ^ K.D + 2 ^ K.D * b := by omega
      _ = 2 ^ K.D * (b + 1) := by ring
      _ ≤ 2 ^ K.D * 2 ^ K.D := Nat.mul_le_mul_left _ hb
  rw [e2, Nat.add_mul_div_left _ _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)),
    Nat.div_eq_of_lt h3, Nat.zero_add]

theorem canon_lt {K : Kit} (F : KitF K) {X : ℕ} (h : Canon 3 K.n 8 X) : X < 2 ^ K.D := by
  rw [hD8 F]
  exact h.1

theorem cd_mk {K : Kit} (F : KitF K) {a b e : ℕ} (ha : Canon 3 K.n 8 a) (hb : Canon 3 K.n 8 b)
    (he : e < 2) : Cd K (mk K a b e) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hA_mk F (canon_lt F ha) (canon_lt F hb)]
    exact ha
  · rw [hB_mk F (canon_lt F ha) (canon_lt F hb)]
    exact hb
  · rw [eps_mk F (canon_lt F ha) (canon_lt F hb)]
    exact he

theorem mulH_sound {K : Kit} (F : KitF K) {A B : ℕ} (ha : Canon 3 K.n 8 A)
    (hb : Canon 3 K.n 8 B) : Canon 3 K.n 8 (mulH K A B) ∧
      ordMat 3 K.n 8 K.S (mulH K A B) = ordMat 3 K.n 8 K.S A * ordMat 3 K.n 8 K.S B :=
  mulR_sound F.consts ha hb

theorem beq_one_rec {α : Sort _} (x : ℕ) (u v : α) :
    Bool.rec (motive := fun _ => α) u v (Nat.beq x (nat_lit 1)) = if x = 1 then v else u := by
  by_cases h : x = 1
  · subst h
    rfl
  · have hb : Nat.beq x 1 = false := Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)
    rw [hb, if_neg h]

theorem mulN_eq (K : Kit) (P Q : ℕ) : mulN K P Q =
    mk K (mulH K (hA K P) (if eps K P = 1 then hB K Q else hA K Q))
      (mulH K (hB K P) (if eps K P = 1 then hA K Q else hB K Q)) ((eps K P + eps K Q) % 2) := by
  unfold mulN
  simp only [CFSG.KC.Pack.strictN_eq]
  rw [beq_one_rec]
  by_cases h : eps K P = 1
  · rw [if_pos h, if_pos h, if_pos h]
    congr 1
    exact Nat.and_one_is_mod _
  · rw [if_neg h, if_neg h, if_neg h]
    congr 1
    exact Nat.and_one_is_mod _

theorem canon_ite {n X Y : ℕ} (c : Prop) [Decidable c] (hX : Canon 3 n 8 X)
    (hY : Canon 3 n 8 Y) : Canon 3 n 8 (if c then X else Y) := by
  split
  · exact hX
  · exact hY

theorem eltMul_lt {n : ℕ} (x y : Array ℕ) : ∀ k < 2 * (n * n), (eltMul n x y)[k]! < 3 := by
  intro k hk
  rw [eltMul_get (by omega)]
  by_cases h1 : k < n * n
  · rw [if_pos h1]
    exact Nat.mod_lt _ (by norm_num)
  · rw [if_neg h1, if_pos hk]
    exact Nat.mod_lt _ (by norm_num)

theorem mul_dec {K : Kit} (hK : kitOK K = true) {n P Q : ℕ} (hn : K.n = n) (hP : Cd K P)
    (hQ : Cd K Q) : eltMul n (dec n P) (dec n Q) = dec n (mulN K P Q) ∧ Cd K (mulN K P Q) := by
  subst hn
  have F := kitF hK
  have hn0 : 0 < K.n := F.pos
  obtain ⟨c1, m1⟩ := mulH_sound F hP.1 (canon_ite (eps K P = 1) hQ.2.1 hQ.1)
  obtain ⟨c2, m2⟩ := mulH_sound F hP.2.1 (canon_ite (eps K P = 1) hQ.1 hQ.2.1)
  have he : (eps K P + eps K Q) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hR : Cd K (mulN K P Q) := by
    rw [mulN_eq]
    exact cd_mk F c1 c2 he
  refine ⟨?_, hR⟩
  have la := canon_lt F c1
  have lb := canon_lt F c2
  apply arr_ext hn0 (size_eltMul _ _) (dec_size _ _) (eltMul_lt _ _) (dec_lt F hR)
  · rw [dec_last F hR]
    change eE K.n (eltMul K.n (dec K.n P) (dec K.n Q)) = _
    rw [eE_eltMul hn0, eE_dec F hP, eE_dec F hQ, mulN_eq, eps_mk F la lb]
  · rw [mA_eltMul (ZMod 3) hn0, mulN_eq]
    simp only [mA_dec F, mB_dec F]
    rw [hA_mk F la lb, m1, eE_dec F hP]
    by_cases h : eps K P = 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  · rw [mB_eltMul (ZMod 3) hn0, mulN_eq]
    simp only [mA_dec F, mB_dec F]
    rw [hB_mk F la lb, m2, eE_dec F hP]
    by_cases h : eps K P = 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]

@[expose] def tau (n t : ℕ) : ℕ := n * (t % n) + t / n

theorem tau_lt {n t : ℕ} (hn : 0 < n) (ht : t < n * n) : tau n t < n * n :=
  lt_mul_of_lt (Nat.mod_lt _ hn) (Nat.div_lt_of_lt_mul ht)

theorem tau_tau {n t : ℕ} (hn : 0 < n) (ht : t < n * n) : tau n (tau n t) = t := by
  unfold tau
  obtain ⟨e1, e2⟩ := index_div_mod (n := n) (i := t % n) hn (Nat.div_lt_of_lt_mul ht)
  rw [e2, e1]
  exact Nat.div_add_mod t n

theorem trH_eq (K : Kit) (X : ℕ) : trH K X = Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => acc ||| ((X >>> (8 * k)) &&& 255) <<< (8 * tau K.n k)) (K.n * K.n) := by
  unfold trH
  congr 1
  funext k acc
  rw [CFSG.KC.Pack.strictN_eq]
  rfl

theorem step_bit (X k j b : ℕ) : (((X >>> (8 * k)) &&& 255) <<< (8 * j)).testBit b = true ↔
    b / 8 = j ∧ X.testBit (8 * k + b % 8) = true := by
  have e : (255 : ℕ) = 2 ^ 8 - 1 := rfl
  rw [e, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, ?_⟩
    have e2 : 8 * k + (b - 8 * j) = 8 * k + b % 8 := by omega
    rwa [e2] at h2
  · rintro ⟨h1, h2⟩
    have e2 : 8 * k + (b - 8 * j) = 8 * k + b % 8 := by omega
    refine ⟨by omega, ?_, by omega⟩
    rwa [e2]

theorem trAcc_bit {n X : ℕ} : ∀ m b, (Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => acc ||| ((X >>> (8 * k)) &&& 255) <<< (8 * tau n k)) m).testBit b = true ↔
    ∃ k < m, tau n k = b / 8 ∧ X.testBit (8 * k + b % 8) = true
  | 0, b => by simp
  | m + 1, b => by
    have ih := trAcc_bit (n := n) (X := X) m b
    change ((Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => acc ||| ((X >>> (8 * k)) &&& 255) <<< (8 * tau n k)) m) |||
        ((X >>> (8 * m)) &&& 255) <<< (8 * tau n m)).testBit b = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, step_bit]
    constructor
    · rintro (⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨k, by omega, h1, h2⟩
      · exact ⟨m, by omega, h1.symm, h2⟩
    · rintro ⟨k, hk, h1, h2⟩
      rcases Nat.lt_or_ge k m with h | h
      · exact Or.inl ⟨k, h, h1, h2⟩
      · obtain rfl : k = m := by omega
        exact Or.inr ⟨h1.symm, h2⟩

theorem lane_trH {K : Kit} (F : KitF K) (X : ℕ) {t : ℕ} (ht : t < K.n * K.n) :
    lane 8 (trH K X) t = lane 8 X (tau K.n t) := by
  apply Nat.eq_of_testBit_eq
  intro c
  rw [testBit_lane, testBit_lane]
  by_cases hc : c < 8
  · simp only [hc, decide_true, Bool.true_and]
    rw [trH_eq]
    apply Bool.eq_iff_iff.2
    rw [trAcc_bit]
    have e1 : (c + 8 * t) / 8 = t := by omega
    have e2 : (c + 8 * t) % 8 = c := by omega
    rw [e1, e2]
    constructor
    · rintro ⟨k, hk, h1, h2⟩
      have e3 : k = tau K.n t := by rw [← h1, tau_tau F.pos hk]
      subst e3
      rwa [Nat.add_comm] at h2
    · intro h
      exact ⟨tau K.n t, tau_lt F.pos ht, tau_tau F.pos ht, by rwa [Nat.add_comm]⟩
  · simp [hc]

theorem canon_trH {K : Kit} (F : KitF K) {X : ℕ} (hX : Canon 3 K.n 8 X) :
    Canon 3 K.n 8 (trH K X) := by
  refine ⟨?_, fun t ht => ?_⟩
  · rw [trH_eq]
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    apply Bool.eq_false_iff.2
    intro h
    rw [trAcc_bit] at h
    obtain ⟨k, hk, h1, -⟩ := h
    have := tau_lt F.pos hk
    omega
  · rw [lane_trH F X ht]
    exact hX.2 _ (tau_lt F.pos ht)

theorem ordMat_trH {K : Kit} (F : KitF K) (X : ℕ) :
    ordMat 3 K.n 8 K.S (trH K X) = (ordMat 3 K.n 8 K.S X)ᵀ := by
  ext i j
  rw [F.hS, Matrix.transpose_apply, ordMat_lane, ordMat_lane,
    lane_trH F X (lt_mul_of_lt i.2 j.2)]
  unfold tau
  obtain ⟨e1, e2⟩ := index_div_mod (i := i.val) F.pos j.2
  rw [e1, e2]

theorem invN_eq (K : Kit) (P : ℕ) : invN K P = if eps K P = 1 then
    mk K (trH K (hA K P)) (trH K (hB K P)) (eps K P) else
    mk K (trH K (hB K P)) (trH K (hA K P)) (eps K P) := by
  unfold invN
  simp only [CFSG.KC.Pack.strictN_eq]
  rw [beq_one_rec]

theorem inv_dec {K : Kit} (hK : kitOK K = true) {n P : ℕ} (hn : K.n = n) (hP : Cd K P) :
    eltInv n (dec n P) = dec n (invN K P) ∧ Cd K (invN K P) := by
  subst hn
  have F := kitF hK
  have hn0 : 0 < K.n := F.pos
  have ta := canon_trH F hP.1
  have tb := canon_trH F hP.2.1
  have la := canon_lt F ta
  have lb := canon_lt F tb
  have hR : Cd K (invN K P) := by
    rw [invN_eq]
    split
    · exact cd_mk F ta tb hP.2.2
    · exact cd_mk F tb ta hP.2.2
  refine ⟨?_, hR⟩
  have hx := dec_lt F hP
  apply arr_ext hn0 (size_eltInv _) (dec_size _ _) ?_ (dec_lt F hR)
  · rw [dec_last F hR]
    change eE K.n (eltInv K.n (dec K.n P)) = _
    rw [eE_eltInv hn0, eE_dec F hP, invN_eq]
    split
    · exact (eps_mk F la lb).symm
    · exact (eps_mk F lb la).symm
  · rw [mA_eltInv (ZMod 3) hn0, invN_eq, eE_dec F hP]
    simp only [mA_dec F, mB_dec F]
    by_cases h : eps K P = 1
    · rw [if_pos h, if_pos h, hA_mk F la lb, ordMat_trH F]
    · rw [if_neg h, if_neg h, hA_mk F lb la, ordMat_trH F]
  · rw [mB_eltInv (ZMod 3) hn0, invN_eq, eE_dec F hP]
    simp only [mA_dec F, mB_dec F]
    by_cases h : eps K P = 1
    · rw [if_pos h, if_pos h, hB_mk F la lb, ordMat_trH F]
    · rw [if_neg h, if_neg h, hB_mk F lb la, ordMat_trH F]
  · intro k hk
    rw [eltInv_get (by omega)]
    rcases Nat.lt_or_ge k (K.n * K.n) with h1 | h1
    · have hd' : k / K.n < K.n := Nat.div_lt_of_lt_mul h1
      rw [if_pos h1]
      split
      · exact eA_lt hx (Nat.mod_lt _ hn0) hd'
      · exact eB_lt hx (Nat.mod_lt _ hn0) hd'
    · have hd' : (k - K.n * K.n) / K.n < K.n := Nat.div_lt_of_lt_mul (by omega)
      rw [if_neg (by omega), if_pos hk]
      split
      · exact eB_lt hx (Nat.mod_lt _ hn0) hd'
      · exact eA_lt hx (Nat.mod_lt _ hn0) hd'

theorem canon_bit7 {n X : ℕ} (h : Canon 3 n 8 X) (s : ℕ) : X.testBit (8 * s + 7) = false := by
  rcases Nat.lt_or_ge s (n * n) with hs | hs
  · have e := testBit_lane X s 7
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (h.2 s hs) (by norm_num : 3 ≤ 2 ^ 7))] at e
    have e2 : X.testBit (7 + 8 * s) = false := by simpa using e.symm
    rwa [Nat.add_comm]
  · exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem lane_double {X : ℕ} (h7 : ∀ s, X.testBit (8 * s + 7) = false) (t : ℕ) :
    lane 8 (X + X) t = 2 * lane 8 X t := by
  apply Nat.eq_of_testBit_eq
  intro c
  have e2 : X + X = 2 ^ 1 * X := by ring
  have e3 : 2 * lane 8 X t = 2 ^ 1 * lane 8 X t := by ring
  rw [testBit_lane, e2, e3, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, testBit_lane]
  rcases Nat.lt_or_ge c 1 with hc | hc
  · obtain rfl : c = 0 := by omega
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · have e : 0 + 8 * t - 1 = 8 * (t - 1) + 7 := by omega
      rw [e, h7]
      simp
  · rcases Nat.lt_or_ge c 8 with hc8 | hc8
    · have e : c + 8 * t - 1 = c - 1 + 8 * t := by omega
      have h1 : c - 1 < 8 := by omega
      have h2 : 1 ≤ c + 8 * t := by omega
      rw [e]
      simp [hc8, hc, h1, h2]
    · rcases Nat.eq_or_lt_of_le hc8 with rfl | hc9
      · have e : 8 - 1 + 8 * t = 8 * t + 7 := by omega
        rw [e, h7]
        simp
      · have h1 : ¬ c < 8 := by omega
        have h2 : ¬ c - 1 < 8 := by omega
        simp [h1, h2]

theorem canon_M2 {K : Kit} (F : KitF K) :
    Canon 3 K.n 8 K.M2 ∧ ordMat 3 K.n 8 K.S K.M2 = -1 := by
  obtain ⟨c1, o1⟩ := one_sound F.consts
  have hl : ∀ t < K.n * K.n, lane 8 K.ONEh t ≤ 1 := by
    intro t ht
    obtain ⟨i, j, hij⟩ := eA_index F.pos ht
    have e := congrFun (congrFun o1 i) j
    rw [F.hS, ordMat_lane, hij, Matrix.one_apply] at e
    have e' : ((lane 8 K.ONEh t : ℕ) : ZMod 3) = ((if i = j then 1 else 0 : ℕ) : ZMod 3) := by
      rw [e]
      split <;> simp
    have h3 : (if i = j then 1 else 0 : ℕ) < 3 := by split <;> norm_num
    have := (cast_eq_iff (ZMod 3) h3).1 e'
    rw [Nat.mod_eq_of_lt (c1.2 t ht)] at this
    rw [this]
    split <;> norm_num
  have h2 : K.ONEh + K.ONEh = 2 ^ 1 * K.ONEh := by ring
  have hnn := Nat.mul_pos F.pos F.pos
  refine ⟨⟨?_, fun t ht => ?_⟩, ?_⟩
  · rw [F.hM2]
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [h2, Nat.testBit_two_pow_mul]
    rcases Nat.lt_or_ge (i - 1) (8 * (K.n * K.n)) with h | h
    · have e : i - 1 = 8 * (K.n * K.n - 1) + 7 := by omega
      rw [e, canon_bit7 c1, Bool.and_false]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le c1.1 (Nat.pow_le_pow_right (by norm_num) h)),
        Bool.and_false]
  · rw [F.hM2, lane_double (canon_bit7 c1)]
    have := hl t ht
    omega
  · ext i j
    rw [F.hS, ordMat_lane, F.hM2, lane_double (canon_bit7 c1), Nat.cast_mul, ← ordMat_lane,
      ← F.hS, o1, Matrix.neg_apply, Nat.cast_ofNat, two_eq_neg_one (ZMod 3)]
    ring

theorem one_mk {K : Kit} (F : KitF K) : K.ONE = mk K K.ONEh K.ONEh 0 := by
  change _ = (K.ONEh ||| K.ONEh <<< K.D) ||| 0 <<< K.E2
  rw [F.hONE]
  simp

theorem mone_mk {K : Kit} (F : KitF K) : K.MONE = mk K K.M2 K.M2 0 := by
  change _ = (K.M2 ||| K.M2 <<< K.D) ||| 0 <<< K.E2
  rw [F.hMONE]
  simp

theorem one_dec {K : Kit} (hK : kitOK K = true) {n : ℕ} (hn : K.n = n) :
    eltOne n = dec n K.ONE ∧ Cd K K.ONE := by
  subst hn
  have F := kitF hK
  obtain ⟨c1, o1⟩ := one_sound F.consts
  have l1 := canon_lt F c1
  have hR : Cd K K.ONE := by
    rw [one_mk F]
    exact cd_mk F c1 c1 (by norm_num)
  refine ⟨?_, hR⟩
  apply arr_ext F.pos size_eltOne (dec_size _ _) ?_ (dec_lt F hR)
  · rw [dec_last F hR, eltOne_get (by omega), if_neg (lt_irrefl _), one_mk F, eps_mk F l1 l1]
  · rw [mA_eltOne (ZMod 3) F.pos, mA_dec F, one_mk F, hA_mk F l1 l1, o1]
  · rw [mB_eltOne (ZMod 3) F.pos, mB_dec F, one_mk F, hB_mk F l1 l1, o1]
  · intro k hk
    rw [eltOne_get (by omega), if_pos hk]
    split_ifs <;> norm_num

theorem mone_dec {K : Kit} (hK : kitOK K = true) {n : ℕ} (hn : K.n = n) :
    eltMinusOne n = dec n K.MONE ∧ Cd K K.MONE := by
  subst hn
  have F := kitF hK
  obtain ⟨c1, o1⟩ := canon_M2 F
  have l1 := canon_lt F c1
  have hR : Cd K K.MONE := by
    rw [mone_mk F]
    exact cd_mk F c1 c1 (by norm_num)
  refine ⟨?_, hR⟩
  apply arr_ext F.pos size_eltMinusOne (dec_size _ _) ?_ (dec_lt F hR)
  · rw [dec_last F hR, eltMinusOne_get (by omega), if_neg (lt_irrefl _), mone_mk F,
      eps_mk F l1 l1]
  · rw [mA_eltMinusOne (ZMod 3) F.pos, mA_dec F, mone_mk F, hA_mk F l1 l1, o1]
  · rw [mB_eltMinusOne (ZMod 3) F.pos, mB_dec F, mone_mk F, hB_mk F l1 l1, o1]
  · intro k hk
    rw [eltMinusOne_get (by omega), if_pos hk]
    split_ifs <;> norm_num

theorem canonK_inj {K : Kit} (F : KitF K) {X Y : ℕ} (hX : Canon 3 K.n 8 X)
    (hY : Canon 3 K.n 8 Y) (h : ordMat 3 K.n 8 K.S X = ordMat 3 K.n 8 K.S Y) : X = Y := by
  rw [F.hS] at h
  exact canon_inj F.pos hX hY h

theorem neg_sound {K : Kit} (F : KitF K) {B : ℕ} (hB : Canon 3 K.n 8 B) :
    Canon 3 K.n 8 (mulH K B K.M2) ∧
      ordMat 3 K.n 8 K.S (mulH K B K.M2) = - ordMat 3 K.n 8 K.S B := by
  obtain ⟨c, o⟩ := mulH_sound F hB (canon_M2 F).1
  rw [(canon_M2 F).2, Matrix.mul_neg, Matrix.mul_one] at o
  exact ⟨c, o⟩

theorem beq_true_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem eq_dec {K : Kit} (hK : kitOK K = true) {n P Q : ℕ} (hn : K.n = n) (hP : Cd K P)
    (hQ : Cd K Q) : eltEq n (dec n P) (dec n Q) = eqN K P Q := by
  subst hn
  have F := kitF hK
  obtain ⟨cn, on⟩ := neg_sound F hQ.1
  apply Bool.eq_iff_iff.2
  rw [eltEq_iff (ZMod 3) F.pos, eE_dec F hP, eE_dec F hQ, mA_dec F, mA_dec F]
  unfold eqN
  simp only [CFSG.KC.Pack.strictB_eq]
  rw [CFSG.KC.Pack.band_iff, CFSG.KS.U43Pk.bIf_eq, beq_true_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro (h2 | h2)
    · rw [canonK_inj F hP.1 hQ.1 h2, Nat.beq_refl]
      rfl
    · have e := canonK_inj F hP.1 cn (h2.trans on.symm)
      by_cases h3 : Nat.beq (hA K P) (hA K Q) = true
      · rw [if_pos h3]
      · rw [if_neg h3, e]
        exact Nat.beq_refl _
  · intro h2
    by_cases h3 : Nat.beq (hA K P) (hA K Q) = true
    · left
      rw [beq_true_iff.1 h3]
    · rw [if_neg h3] at h2
      right
      rw [beq_true_iff.1 h2, on]

theorem lane_land (X t : ℕ) : (X >>> (8 * t)) &&& 255 = lane 8 X t := by
  have e : (255 : ℕ) = 2 ^ 8 - 1 := rfl
  rw [Nat.shiftRight_eq_div_pow, e, Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem horner {N : ℕ} (f : ℕ → ℕ) : ∀ m ≤ N, Nat.rec (motive := fun _ => ℕ) 0
    (fun j acc => acc * 3 + f (N - 1 - j)) m = Nat.ofDigits 3 ((List.range' (N - m) m).map f)
  | 0, _ => by simp
  | m + 1, h => by
    change Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => acc * 3 + f (N - 1 - j)) m * 3 +
      f (N - 1 - m) = _
    rw [horner f m (by omega)]
    have e : N - (m + 1) = N - 1 - m := by omega
    have e2 : N - 1 - m + 1 = N - m := by omega
    rw [e, List.range'_succ, List.map_cons, Nat.ofDigits_cons, e2]
    push_cast
    ring

theorem b3N_eq (K : Kit) (X : ℕ) :
    b3N K X = Nat.ofDigits 3 ((List.range (K.n * K.n)).map (lane 8 X)) := by
  rw [List.range_eq_range', ← Nat.sub_self (K.n * K.n), ← horner (lane 8 X) _ le_rfl]
  unfold b3N
  congr 1
  funext j acc
  rw [CFSG.KC.Pack.strictN_eq]
  change acc * 3 + ((X >>> (8 * (K.n * K.n - 1 - j))) &&& 255) = _
  rw [lane_land]

theorem lane_neg {K : Kit} (F : KitF K) {A : ℕ} (hA' : Canon 3 K.n 8 A) {t : ℕ}
    (ht : t < K.n * K.n) : lane 8 (mulH K A K.M2) t = (3 - lane 8 A t % 3) % 3 := by
  obtain ⟨cn, on⟩ := neg_sound F hA'
  obtain ⟨i, j, hij⟩ := eA_index F.pos ht
  have e := congrFun (congrFun on i) j
  rw [Matrix.neg_apply, F.hS, ordMat_lane, ordMat_lane, hij] at e
  have h3 : (3 - lane 8 A t % 3) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have e2 : ((lane 8 (mulH K A K.M2) t : ℕ) : ZMod 3) = (((3 - lane 8 A t % 3) % 3 : ℕ) : ZMod 3) := by
    rw [e, ZMod.natCast_mod, Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (by norm_num))),
      ZMod.natCast_mod, ZMod.natCast_self]
    ring
  have := (cast_eq_iff (ZMod 3) h3).1 e2
  rwa [Nat.mod_eq_of_lt (cn.2 t ht)] at this

theorem min_rec (a b : ℕ) : Bool.rec (motive := fun _ => ℕ) b a (Nat.ble a b) = min a b := by
  cases h : Nat.ble a b
  · have h' : ¬ a ≤ b := fun h' => absurd (h.symm.trans (Nat.ble_eq_true_of_le h'))
      Bool.false_ne_true
    rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h'))]
  · exact (min_eq_left (Nat.le_of_ble_eq_true h)).symm

theorem key_dec {K : Kit} (hK : kitOK K = true) {n P : ℕ} (hn : K.n = n) (hP : Cd K P) :
    eltKey n (dec n P) = keyN K P := by
  subst hn
  have F := kitF hK
  have hx := dec_lt F hP
  have h1 : kA K.n (dec K.n P) = b3N K (hA K P) := by
    unfold kA
    rw [b3N_eq]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    have hk' := List.mem_range.1 hk
    rw [Nat.mod_eq_of_lt (hx k (by omega)), dec_get (by omega), lane_hA F P hk']
  have h2 : kN K.n (dec K.n P) = b3N K (mulH K (hA K P) K.M2) := by
    unfold kN
    rw [b3N_eq]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    have hk' := List.mem_range.1 hk
    rw [lane_neg F hP.1 hk', dec_get (by omega), lane_hA F P hk']
  unfold eltKey keyN
  simp only [CFSG.KC.Pack.strictN_eq]
  rw [h1, h2, min_rec, eE_dec F hP]
  rfl

@[expose] def fzL (f : ℕ → ℕ) (l : List ℕ) : ℕ :=
  match l.find? (fun k => f k != 0) with
  | some k => f k
  | none => 0

theorem fzL_cons (f : ℕ → ℕ) (a : ℕ) (l : List ℕ) :
    fzL f (a :: l) = if f a = 0 then fzL f l else f a := by
  unfold fzL
  rw [List.find?_cons]
  by_cases h : f a = 0
  · simp [h]
  · have hb : (f a != 0) = true := bne_iff_ne.2 h
    simp [hb, h]

theorem scan_eq {N : ℕ} (f : ℕ → ℕ) : ∀ m ≤ N, Nat.rec (motive := fun _ => ℕ) 0
    (fun j acc => Bool.rec (motive := fun _ => ℕ) (f (N - 1 - j)) acc
      (Nat.beq (f (N - 1 - j)) 0)) m = fzL f (List.range' (N - m) m)
  | 0, _ => by simp [fzL]
  | m + 1, h => by
    change Bool.rec (motive := fun _ => ℕ) (f (N - 1 - m)) (Nat.rec (motive := fun _ => ℕ) 0
      (fun j acc => Bool.rec (motive := fun _ => ℕ) (f (N - 1 - j)) acc
        (Nat.beq (f (N - 1 - j)) 0)) m) (Nat.beq (f (N - 1 - m)) 0) = _
    rw [scan_eq f m (by omega)]
    have e : N - (m + 1) = N - 1 - m := by omega
    have e2 : N - 1 - m + 1 = N - m := by omega
    rw [e, List.range'_succ, fzL_cons, e2]
    by_cases h0 : f (N - 1 - m) = 0
    · rw [if_pos h0, h0]
      rfl
    · have hb : Nat.beq (f (N - 1 - m)) 0 = false :=
        Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)
      rw [if_neg h0, hb]

theorem fnzN_eq (K : Kit) (P : ℕ) : fnzN K P = fzL (lane 8 P) (List.range (K.n * K.n)) := by
  rw [List.range_eq_range', ← Nat.sub_self (K.n * K.n), ← scan_eq (lane 8 P) _ le_rfl]
  unfold fnzN
  congr 1
  funext j acc
  rw [CFSG.KC.Pack.strictN_eq, CFSG.KC.Pack.strictN_eq]
  change Bool.rec (motive := fun _ => ℕ) ((P >>> (8 * (K.n * K.n - 1 - j))) &&& 255) acc
    (Nat.beq ((P >>> (8 * (K.n * K.n - 1 - j))) &&& 255) 0) = _
  rw [lane_land]

theorem fnz_dec {K : Kit} (F : KitF K) {P : ℕ} (hP : Cd K P) :
    firstNZ K.n (dec K.n P) = fnzN K P := by
  have hx := dec_lt F hP
  have hv : ∀ k ∈ List.range (K.n * K.n), (dec K.n P)[k]! % 3 = lane 8 P k := fun k hk => by
    have hk' := List.mem_range.1 hk
    rw [Nat.mod_eq_of_lt (hx k (by omega)), dec_get (by omega)]
  have hF : List.find? (fun k => (dec K.n P)[k]! % 3 != 0) (List.range (K.n * K.n)) =
      List.find? (fun k => lane 8 P k != 0) (List.range (K.n * K.n)) := by
    apply List.find?_congr
    intro k hk
    rw [hv k hk]
  rw [fnzN_eq]
  unfold firstNZ fzL
  rw [hF]
  cases hf : List.find? (fun k => lane 8 P k != 0) (List.range (K.n * K.n)) with
  | none => rfl
  | some k =>
    dsimp only
    exact hv k (List.mem_of_find?_eq_some hf)

theorem norm_dec {K : Kit} (hK : kitOK K = true) {n P : ℕ} (hn : K.n = n) (hP : Cd K P) :
    eltNorm n (dec n P) = dec n (normN K P) ∧ Cd K (normN K P) := by
  subst hn
  have F := kitF hK
  obtain ⟨m1, cm⟩ := mone_dec hK rfl
  obtain ⟨e1, c1⟩ := mul_dec hK rfl cm hP
  unfold eltNorm normN
  rw [fnz_dec F hP]
  by_cases h : fnzN K P = 2
  · have hb : (fnzN K P == 2) = true := by rw [h]; rfl
    have hb' : Nat.beq (fnzN K P) 2 = true := by rw [h]; rfl
    rw [if_pos hb, hb', m1]
    exact ⟨e1, c1⟩
  · have hb : (fnzN K P == 2) = false := by simp [h]
    have hb' : Nat.beq (fnzN K P) 2 = false := Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)
    rw [if_neg (by rw [hb]; exact Bool.false_ne_true), hb']
    exact ⟨rfl, hP⟩

theorem act_dec {K : Kit} (hK : kitOK K = true) {n G P k : ℕ} (hn : K.n = n)
    {gens : Array (Array ℕ)} (hG : gens[k]! = dec n G) (hGc : Cd K G) (hP : Cd K P) :
    locAct n gens k (dec n P) = dec n (actN K G P) ∧ Cd K (actN K G P) := by
  obtain ⟨e1, c1⟩ := mul_dec hK hn hGc hP
  obtain ⟨e2, c2⟩ := norm_dec hK hn c1
  unfold locAct actN
  rw [hG, e1, e2, CFSG.KC.Pack.strictN_eq]
  exact ⟨rfl, c2⟩

theorem canon_spec {K : Kit} (hK : kitOK K = true) {P : ℕ} (h : canonN K P = true) : Cd K P := by
  have F := kitF hK
  unfold canonN at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h3⟩ := andB_true h
  rw [F.hD] at h1 h2
  exact ⟨validM_canon F.consts h1, validM_canon F.consts h2, Nat.blt_eq.mp h3⟩

theorem valid_dec {K : Kit} (hK : kitOK K = true) {n P : ℕ} (hn : K.n = n)
    (h : validN K P = true) : eltValid n (dec n P) = true ∧ Cd K P := by
  subst hn
  have F := kitF hK
  unfold validN at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  have hP := canon_spec hK h1
  refine ⟨?_, hP⟩
  obtain ⟨i1, ci⟩ := inv_dec hK rfl hP
  obtain ⟨m1, -⟩ := mul_dec hK rfl hP ci
  obtain ⟨o1, -⟩ := one_dec hK rfl
  have e : eltMul K.n (dec K.n P) (eltInv K.n (dec K.n P)) = eltOne K.n := by
    rw [i1, m1, Nat.eq_of_beq_eq_true h2, o1]
  have eA' := congrArg (mA K.n (ZMod 3)) e
  rw [mA_eltMul (ZMod 3) F.pos, mA_eltOne (ZMod 3) F.pos, mA_eltInv (ZMod 3) F.pos,
    mB_eltInv (ZMod 3) F.pos] at eA'
  rw [eltValid_iff (ZMod 3)]
  refine ⟨dec_size _ _, dec_lt F hP, ?_, ?_⟩
  · rw [dec_last F hP]
    exact hP.2.2
  · by_cases h3 : eE K.n (dec K.n P) = 1
    · rw [if_pos h3, if_pos h3] at eA'
      exact eA'
    · rw [if_neg h3, if_neg h3] at eA'
      exact eA'

theorem powN_succ (K : Kit) (P m : ℕ) : powN K P (m + 1) = mulN K (powN K P m) P := by
  change CFSG.KC.Enum.strictN (powN K P m) (fun a => mulN K a P) = _
  rw [CFSG.KC.Pack.strictN_eq]

theorem pow_dec {K : Kit} (hK : kitOK K = true) {n P : ℕ} (hn : K.n = n) (hP : Cd K P) :
    ∀ m, ePow n (dec n P) m = dec n (powN K P m) ∧ Cd K (powN K P m)
  | 0 => one_dec hK hn
  | m + 1 => by
    obtain ⟨e, c⟩ := pow_dec hK hn hP m
    obtain ⟨e2, c2⟩ := mul_dec hK hn c hP
    rw [powN_succ, ePow, e]
    exact ⟨e2, c2⟩

theorem conj_dec {K : Kit} (hK : kitOK K = true) {n S X : ℕ} (hn : K.n = n) (hS : Cd K S)
    (hX : Cd K X) : eltConj n (dec n S) (dec n X) = dec n (conjN K S X) ∧ Cd K (conjN K S X) := by
  obtain ⟨e1, c1⟩ := mul_dec hK hn hS hX
  obtain ⟨e2, c2⟩ := inv_dec hK hn hS
  obtain ⟨e3, c3⟩ := mul_dec hK hn c1 c2
  unfold eltConj conjN
  rw [e1, e2, e3, CFSG.KC.Pack.strictN_eq]
  exact ⟨rfl, c3⟩

theorem hA_mulN {K : Kit} (F : KitF K) {P Q : ℕ} (hP : Cd K P) (hQ : Cd K Q) :
    hA K (mulN K P Q) = mAN K P Q ∧ eps K (mulN K P Q) = (eps K P + eps K Q) % 2 := by
  obtain ⟨c1, -⟩ := mulH_sound F hP.1 (canon_ite (eps K P = 1) hQ.2.1 hQ.1)
  obtain ⟨c2, -⟩ := mulH_sound F hP.2.1 (canon_ite (eps K P = 1) hQ.1 hQ.2.1)
  rw [mulN_eq, hA_mk F (canon_lt F c1) (canon_lt F c2), eps_mk F (canon_lt F c1) (canon_lt F c2)]
  refine ⟨?_, rfl⟩
  unfold mAN
  rw [beq_one_rec]

theorem comm_dec {K : Kit} (hK : kitOK K = true) {n X Y : ℕ} (hn : K.n = n) (hX : Cd K X)
    (hY : Cd K Y) : eltEq n (eltMul n (dec n X) (dec n Y)) (eltMul n (dec n Y) (dec n X)) =
      commN K X Y := by
  have F := kitF hK
  obtain ⟨e1, c1⟩ := mul_dec hK hn hX hY
  obtain ⟨e2, c2⟩ := mul_dec hK hn hY hX
  rw [e1, e2, eq_dec hK hn c1 c2]
  obtain ⟨a1, b1⟩ := hA_mulN F hX hY
  obtain ⟨a2, b2⟩ := hA_mulN F hY hX
  unfold eqN commN
  rw [b1, b2, Nat.add_comm (eps K Y), Nat.beq_refl]
  simp only [CFSG.KC.Pack.strictB_eq]
  rw [a1, a2]

theorem flag_dec {K : Kit} (hK : kitOK K = true) {n P : ℕ} (hn : K.n = n) (hP : Cd K P) :
    flagN K P = (if isO8 n (dec n P) = true then 1 else 0) +
      (if isO2 n (dec n P) = true then 2 else 0) := by
  obtain ⟨o1, c1⟩ := one_dec hK hn
  have hp : ∀ m, eltEq n (ePow n (dec n P) m) (eltOne n) = eqN K (powN K P m) K.ONE := by
    intro m
    obtain ⟨e, c⟩ := pow_dec hK hn hP m
    rw [e, o1, eq_dec hK hn c c1]
  have h1 : eltEq n (dec n P) (eltOne n) = eqN K P K.ONE := by rw [o1, eq_dec hK hn hP c1]
  unfold flagN isO8 isO2
  rw [hp, hp, hp, h1]
  cases eqN K (powN K P 8) K.ONE <;> cases eqN K (powN K P 4) K.ONE <;>
    cases eqN K (powN K P 2) K.ONE <;> cases eqN K P K.ONE <;> rfl

theorem lenL_eq : ∀ l : List ℕ, CFSG.KD.LocLn.lenL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (CFSG.KD.LocLn.lenL l) = _
    rw [lenL_eq l]
    rfl

theorem smallL_spec : ∀ l : List ℕ, smallL l = true → ∀ d ∈ l, d < 3
  | [], _, d, hd => absurd hd List.not_mem_nil
  | a :: l, h, d, hd => by
    change Bool.rec (motive := fun _ => Bool) false (smallL l) (Nat.blt a 3) = true at h
    obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
    rcases List.mem_cons.1 hd with rfl | hd
    · exact Nat.blt_eq.mp h1
    · exact smallL_spec l h2 d hd

theorem lane_pkL : ∀ l : List ℕ, (∀ d ∈ l, d < 256) → ∀ k (hk : k < l.length),
    lane 8 (pkL l) k = l[k]
  | [], _, k, hk => absurd hk (Nat.not_lt_zero k)
  | a :: l, h, k, hk => by
    have ha : a < 256 := h a (List.mem_cons_self ..)
    change lane 8 (a + (pkL l) <<< 8) k = _
    rw [Nat.shiftLeft_eq]
    rcases k with _ | k
    · unfold lane
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
      rfl
    · have e : lane 8 (a + pkL l * 2 ^ 8) (k + 1) = lane 8 ((a + pkL l * 2 ^ 8) / 2 ^ (8 * 1)) k := by
        rw [lane_div]
        congr 1
        omega
      rw [e, Nat.mul_one, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 8), Nat.div_eq_of_lt ha,
        Nat.zero_add, lane_pkL l (fun d hd => h d (List.mem_cons_of_mem _ hd)) k
          (by simp at hk; omega)]
      rfl

theorem codeN_sound {K : Kit} {n : ℕ} (hn : K.n = n) {x : Array ℕ} {P : ℕ}
    (h : codeN K x P = true) : x = dec n P := by
  subst hn
  unfold codeN at h
  obtain ⟨h1, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h3⟩ := CFSG.KC.Pack.band_iff.1 h
  have hl : x.toList.length = 2 * (K.n * K.n) + 1 := by
    rw [← lenL_eq, Nat.eq_of_beq_eq_true h1]
    simp only [Nat.succ_eq_add_one, Nat.add_eq, Nat.mul_eq]
    omega
  have hs := smallL_spec _ h2
  have hp : pkL x.toList = P := Nat.eq_of_beq_eq_true h3
  apply Array.ext (by rw [dec_size, ← Array.length_toList, hl])
  intro k h1' h2'
  rw [← getElem!_pos (dec K.n P) k h2', dec_get (by rw [dec_size] at h2'; exact h2'), ← hp,
    lane_pkL _ (fun d hd => by have := hs d hd; omega) k (by rw [Array.length_toList]; exact h1')]
  simp

theorem wordN_spec : ∀ w : List (ℕ × Bool), wordN w = true → ∀ l ∈ w, l.1 < 3
  | [], _, l, hl => absurd hl List.not_mem_nil
  | a :: w, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (wordN w) (Nat.blt a.1 3) = true at h
    obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
    rcases List.mem_cons.1 hl with rfl | hl
    · exact Nat.blt_eq.mp h1
    · exact wordN_spec w h2 l hl

theorem sel_dec {n W0 W1 W2 i : ℕ} (hi : i < 3) :
    (#[dec n W0, dec n W1, dec n W2] : Array (Array ℕ))[i]! = dec n (selN W0 W1 W2 i) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

theorem sel_cd {K : Kit} {W0 W1 W2 i : ℕ} (h0 : Cd K W0) (h1 : Cd K W1) (h2 : Cd K W2)
    (hi : i < 3) : Cd K (selN W0 W1 W2 i) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

theorem eval_dec {K : Kit} (hK : kitOK K = true) {n W0 W1 W2 : ℕ} (hn : K.n = n)
    (h0 : Cd K W0) (h1 : Cd K W1) (h2 : Cd K W2) :
    ∀ (w : List (ℕ × Bool)) (acc : ℕ), (∀ l ∈ w, l.1 < 3) → Cd K acc →
      w.foldl (fun a l => eltMul n a (if l.2 then eltInv n
          (#[dec n W0, dec n W1, dec n W2] : Array (Array ℕ))[l.1]!
        else (#[dec n W0, dec n W1, dec n W2] : Array (Array ℕ))[l.1]!)) (dec n acc) =
        dec n (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
          (fun l _ ih acc => CFSG.KC.Enum.strictN (mulN K acc (Prod.rec (motive := fun _ => ℕ)
            (fun i b => Bool.rec (motive := fun _ => ℕ) (selN W0 W1 W2 i)
              (invN K (selN W0 W1 W2 i)) b) l)) ih) w acc) ∧
      Cd K (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
          (fun l _ ih acc => CFSG.KC.Enum.strictN (mulN K acc (Prod.rec (motive := fun _ => ℕ)
            (fun i b => Bool.rec (motive := fun _ => ℕ) (selN W0 W1 W2 i)
              (invN K (selN W0 W1 W2 i)) b) l)) ih) w acc)
  | [], acc, _, hc => ⟨rfl, hc⟩
  | (i, b) :: w, acc, hw, hc => by
    have hi : i < 3 := hw (i, b) (List.mem_cons_self ..)
    have hs := sel_cd h0 h1 h2 hi
    obtain ⟨ei, ci⟩ := inv_dec hK hn hs
    have hl : (if b = true then eltInv n
        (#[dec n W0, dec n W1, dec n W2] : Array (Array ℕ))[i]!
        else (#[dec n W0, dec n W1, dec n W2] : Array (Array ℕ))[i]!) =
        dec n (Bool.rec (motive := fun _ => ℕ) (selN W0 W1 W2 i) (invN K (selN W0 W1 W2 i)) b) ∧
        Cd K (Bool.rec (motive := fun _ => ℕ) (selN W0 W1 W2 i) (invN K (selN W0 W1 W2 i)) b) := by
      cases b
      · exact ⟨by rw [sel_dec hi]; rfl, hs⟩
      · exact ⟨by rw [sel_dec hi]; exact ei, ci⟩
    obtain ⟨em, cm⟩ := mul_dec hK hn hc hl.2
    rw [List.foldl_cons]
    dsimp only
    rw [hl.1, em, CFSG.KC.Pack.strictN_eq]
    exact eval_dec hK hn h0 h1 h2 w _ (fun l hl' => hw l (List.mem_cons_of_mem _ hl')) cm

theorem eqN_one {K : Kit} (hK : kitOK K = true) {n : ℕ} (hn : K.n = n) {A : ℕ} (hA' : Cd K A)
    (m : ℕ) : eltEq n (ePow n (dec n A) m) (eltOne n) = eqN K (powN K A m) K.ONE := by
  obtain ⟨o1, c1⟩ := one_dec hK hn
  obtain ⟨e, c⟩ := pow_dec hK hn hA' m
  rw [e, o1, eq_dec hK hn c c1]

theorem repN_sound {K : Kit} (hK : kitOK K = true) {n : ℕ} (hn : K.n = n)
    {inF : Array ℕ → Bool} {r : LocRep} {X T G1 G2 : ℕ} (hx : r.x = dec n X)
    (ht : r.t = dec n T) (hg1 : r.g₁ = dec n G1) (hg2 : r.g₂ = dec n G2)
    (h : repN K X T G1 G2 r.wa r.wb r.ma r.mb r.j = true) (hf1 : inF r.g₁ = true)
    (hf2 : inF r.g₂ = true) : repOK n inF r = true := by
  have F := kitF hK
  unfold repN at h
  obtain ⟨v1, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨v2, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨v3, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨v4, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨z1, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨z2, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨c1, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨c2, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨w1, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨w2, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨m1, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨m2, h⟩ := CFSG.KC.Pack.band_iff.1 h
  simp only [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨p1, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨p2, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨p3, p4⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨V1, cX⟩ := valid_dec hK hn v1
  obtain ⟨V2, cT⟩ := valid_dec hK hn v2
  obtain ⟨V3, cG1⟩ := valid_dec hK hn v3
  obtain ⟨V4, cG2⟩ := valid_dec hK hn v4
  obtain ⟨k1, kc1⟩ := conj_dec hK hn cG1 cX
  obtain ⟨k2, kc2⟩ := conj_dec hK hn cG2 cX
  have hws : (#[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] : Array (Array ℕ)) =
      #[dec n X, dec n (conjN K G1 X), dec n (conjN K G2 X)] := by
    rw [hx, hg1, hg2, k1, k2]
  obtain ⟨ea, ca⟩ := eval_dec hK hn cX kc1 kc2 r.wa K.ONE (wordN_spec _ w1) (one_dec hK hn).2
  obtain ⟨eb, cb⟩ := eval_dec hK hn cX kc1 kc2 r.wb K.ONE (wordN_spec _ w2) (one_dec hK hn).2
  have EA : evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wa =
      dec n (evalN K X (conjN K G1 X) (conjN K G2 X) r.wa) := by
    rw [hws, evalWord, (one_dec hK hn).1]
    exact ea
  have EB : evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wb =
      dec n (evalN K X (conjN K G1 X) (conjN K G2 X) r.wb) := by
    rw [hws, evalWord, (one_dec hK hn).1]
    exact eb
  have ca' : Cd K (evalN K X (conjN K G1 X) (conjN K G2 X) r.wa) := ca
  have cb' : Cd K (evalN K X (conjN K G1 X) (conjN K G2 X) r.wb) := cb
  obtain ⟨eab, cab⟩ := mul_dec hK hn ca' cb'
  have q1 := eqN_one hK hn ca' r.ma
  have q2 := eqN_one hK hn cb' r.mb
  have q3 := eqN_one hK hn cab (2 * r.j)
  have q4 := eqN_one hK hn cab r.j
  have hc1 : eltEq n (eltMul n r.g₁ r.t) (eltMul n r.t r.g₁) = true := by
    obtain ⟨e1, d1⟩ := mul_dec hK hn cG1 cT
    obtain ⟨e2, d2⟩ := mul_dec hK hn cT cG1
    rw [hg1, ht, e1, e2, eq_dec hK hn d1 d2]
    exact c1
  have hc2 : eltEq n (eltMul n r.g₂ r.t) (eltMul n r.t r.g₂) = true := by
    obtain ⟨e1, d1⟩ := mul_dec hK hn cG2 cT
    obtain ⟨e2, d2⟩ := mul_dec hK hn cT cG2
    rw [hg2, ht, e1, e2, eq_dec hK hn d1 d2]
    exact c2
  have he1 : (eE n r.g₁ == 0) = true := by
    subst hn
    rw [hg1, eE_dec F cG1, Nat.eq_of_beq_eq_true z1]
    rfl
  have he2 : (eE n r.g₂ == 0) = true := by
    subst hn
    rw [hg2, eE_dec F cG2, Nat.eq_of_beq_eq_true z2]
    rfl
  have hwa : (r.wa.all fun l => decide (l.1 < 3)) = true :=
    List.all_eq_true.2 fun l hl => decide_eq_true (wordN_spec _ w1 l hl)
  have hwb : (r.wb.all fun l => decide (l.1 < 3)) = true :=
    List.all_eq_true.2 fun l hl => decide_eq_true (wordN_spec _ w2 l hl)
  have hma' : r.ma % 2 = 1 := Nat.eq_of_beq_eq_true m1
  have hmb' : r.mb % 2 = 1 := Nat.eq_of_beq_eq_true m2
  have hma : (r.ma % 2 == 1) = true := by rw [hma']; rfl
  have hmb : (r.mb % 2 == 1) = true := by rw [hmb']; rfl
  have P1 : eltEq n (ePow n (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wa)
      r.ma) (eltOne n) = true := by rw [EA, q1]; exact p1
  have P2 : eltEq n (ePow n (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wb)
      r.mb) (eltOne n) = true := by rw [EB, q2]; exact p2
  have P3 : eltEq n (ePow n (eltMul n
      (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wa)
      (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wb)) (2 * r.j))
      (eltOne n) = true := by rw [EA, EB, eab, q3]; exact p3
  have P4 : eltEq n (ePow n (eltMul n
      (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wa)
      (evalWord n #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] r.wb)) r.j)
      (eltOne n) = false := by
    rw [EA, EB, eab, q4]
    cases hq : eqN K (powN K (mulN K (evalN K X (conjN K G1 X) (conjN K G2 X) r.wa)
      (evalN K X (conjN K G1 X) (conjN K G2 X) r.wb)) r.j) K.ONE
    · rfl
    · rw [hq] at p4
      exact absurd p4 Bool.false_ne_true
  unfold repOK
  rw [← hx, ← ht, ← hg1, ← hg2] at *
  simp only [V1, V2, V3, V4, hf1, hf2, he1, he2, hc1, hc2, hwa, hwb, hma, hmb, P1, P2, P3, P4,
    Bool.and_true, Bool.true_and, Bool.not_false]

theorem ptN_spec {K : Kit} {m N : ℕ} {G T : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {PA LA SO SOI : ℕ → ℕ}
    {i : ℕ} (h : ptN K m N G T E PA LA SO SOI i = true) :
    validN K (T i) = true ∧ CFSG.KS.SporSch.LyM.sortB (fun j => keyN K (T j)) SO SOI N i = true ∧
      (∀ k < m, E i k < N ∧ actN K (G k) (T i) = T (E i k) ∧
        (E i k = 0 ∨ posN m PA LA (E i k) ≤ m * i + k)) ∧
      (i = 0 → T 0 = K.ONE ∧ PA 0 = 0 ∧ LA 0 = 0) ∧
      (i ≠ 0 → PA i < i ∧ LA i < m ∧ E (PA i) (LA i) = i ∧
        (i + 1 ≠ N → posN m PA LA i < posN m PA LA (i + 1))) := by
  unfold ptN at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h⟩ := CFSG.KS.U43Pk.bAnd_spec h
  obtain ⟨h2, h⟩ := CFSG.KS.U43Pk.bAnd_spec h
  obtain ⟨h3, h4⟩ := CFSG.KS.U43Pk.bAnd_spec h
  refine ⟨h1, h2, fun k hk => ?_, fun hi => ?_, fun hi => ?_⟩
  · have e := CFSG.KC.Pack.allBlk_spec h3 k hk
    rw [Nat.add_eq, Nat.zero_add, CFSG.KC.Pack.strictB_eq] at e
    obtain ⟨e1, e⟩ := CFSG.KS.U43Pk.bAnd_spec e
    obtain ⟨e2, e3⟩ := CFSG.KS.U43Pk.bAnd_spec e
    refine ⟨Eq.mp Nat.blt_eq e1, Nat.eq_of_beq_eq_true e2, ?_⟩
    rw [CFSG.KS.U43Pk.bIf_eq] at e3
    by_cases h0 : E i k = 0
    · exact Or.inl h0
    · have hb : Nat.beq (E i k) 0 = false :=
        Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      rw [hb] at e3
      simp only [Bool.false_eq_true, ↓reduceIte] at e3
      exact Or.inr (Nat.le_of_ble_eq_true e3)
  · subst hi
    rw [CFSG.KS.U43Pk.bIf_eq] at h4
    simp only [Nat.beq_refl, ↓reduceIte] at h4
    obtain ⟨e1, e⟩ := CFSG.KS.U43Pk.bAnd_spec h4
    obtain ⟨e2, e3⟩ := CFSG.KS.U43Pk.bAnd_spec e
    exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3⟩
  · have hb : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [CFSG.KS.U43Pk.bIf_eq, hb] at h4
    simp only [Bool.false_eq_true, ↓reduceIte] at h4
    obtain ⟨e1, e⟩ := CFSG.KS.U43Pk.bAnd_spec h4
    obtain ⟨e2, e⟩ := CFSG.KS.U43Pk.bAnd_spec e
    obtain ⟨e3, e4⟩ := CFSG.KS.U43Pk.bAnd_spec e
    refine ⟨Eq.mp Nat.blt_eq e1, Eq.mp Nat.blt_eq e2, Nat.eq_of_beq_eq_true e3, fun hi' => ?_⟩
    rw [CFSG.KS.U43Pk.bIf_eq] at e4
    have hb' : Nat.beq (Nat.succ i) N = false :=
      Bool.eq_false_iff.2 fun h => hi' (Nat.eq_of_beq_eq_true h)
    rw [hb'] at e4
    simp only [Bool.false_eq_true, ↓reduceIte] at e4
    exact Eq.mp Nat.blt_eq e4

theorem tables_of {K : Kit} (hK : kitOK K = true) {n m N : ℕ} (hn : K.n = n)
    {gens : Array (Array ℕ)} {G T : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {PA LA SO SOI : ℕ → ℕ} (hN : 2 ≤ N)
    (hG : ∀ k < m, gens[k]! = dec n (G k) ∧ validN K (G k) = true)
    (hpt : ∀ i < N, ptN K m N G T E PA LA SO SOI i = true) :
    CFSG.KS.ArrBfsSim.Tables m N (locAct n gens) (eltKey n) (fun i => dec n (T i)) E PA LA ∧
      (∀ i < N, eltValid n (dec n (T i)) = true) ∧ dec n (T 0) = eltOne n := by
  have hs : ∀ i < N, CFSG.KS.SporSch.LyM.sortB (fun j => keyN K (T j)) SO SOI N i = true :=
    fun i hi => (ptN_spec (hpt i hi)).2.1
  have hinj := CFSG.KS.SporSch.LyLoop.sortB_inj hs
  have hc : ∀ i < N, Cd K (T i) := fun i hi => (valid_dec hK hn (ptN_spec (hpt i hi)).1).2
  refine ⟨⟨hN, fun i hi k hk => ?_, fun a ha b hb e => ?_, ?_, ?_, fun j hj1 hjN => ?_,
    fun j hj1 hjN => ?_, fun i hi k hk => ?_⟩, fun i hi => ?_, ?_⟩
  · obtain ⟨e1, e2, -⟩ := (ptN_spec (hpt i hi)).2.2.1 k hk
    obtain ⟨g1, g2⟩ := hG k hk
    refine ⟨e1, ?_⟩
    rw [(act_dec hK hn g1 (valid_dec hK hn g2).2 (hc i hi)).1, e2]
  · refine hinj a ha b hb ?_
    have e' : eltKey n (dec n (T a)) = eltKey n (dec n (T b)) := e
    rwa [key_dec hK hn (hc a ha), key_dec hK hn (hc b hb)] at e'
  · exact ((ptN_spec (hpt 0 (by omega))).2.2.2.1 rfl).2.1
  · exact ((ptN_spec (hpt 0 (by omega))).2.2.2.1 rfl).2.2
  · obtain ⟨h1, h2, h3, -⟩ := (ptN_spec (hpt j hjN)).2.2.2.2 (by omega)
    exact ⟨h1, h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := (ptN_spec (hpt j (by omega))).2.2.2.2 (by omega)
    exact h4 (by omega)
  · exact ((ptN_spec (hpt i hi)).2.2.1 k hk).2.2
  · exact (valid_dec hK hn (ptN_spec (hpt i hi)).1).1
  · rw [((ptN_spec (hpt 0 (by omega))).2.2.2.1 rfl).1, (one_dec hK hn).1]

end CFSG.KS.LocLn

end
