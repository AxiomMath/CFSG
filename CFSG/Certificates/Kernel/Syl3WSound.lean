module

public import Certificates.Data.Kernel.Syl3W
public import Certificates.Data.Claims1310uSyl3
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack

public section

namespace CFSG.KC.Syl3W.Sound

open CFSG.KC.Syl3W CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u
open CFSG.KC.Enum (strictB)
open CFSG.KC.LQT.P (allN anyN)
open CFSG.KC.BalanceSC (getL notB)

theorem getL_eq_getD {α : Type} (d : α) (L : List α) (i : ℕ) : getL d L i = L.getD i d := by
  induction L generalizing i with
  | nil => rfl
  | cons x L ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem allN_true {m : ℕ} {f : ℕ → Bool} (h : allN m f = true) {i : ℕ} (hi : i < m) :
    f i = true :=
  CFSG.KC.Misc.ArrEnum.allNP_iff.1 h i hi

theorem anyN_true {m : ℕ} {f : ℕ → Bool} (h : anyN m f = true) : ∃ i < m, f i = true := by
  rw [CFSG.KC.Misc.ArrEnum.anyNP_eq, List.any_eq_true] at h
  obtain ⟨i, hi, h⟩ := h
  exact ⟨i, List.mem_range.1 hi, h⟩

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem bIf_eq_true' (c t : Bool) : bIf(c, t, true) = (!c || t) := by cases c <;> rfl

theorem notB_eq (a : Bool) : CFSG.KC.BalanceSC.notB a = !a := by cases a <;> rfl

theorem nIf_eq (c : Bool) (t e : ℕ) : nIf(c, t, e) = if c then t else e := by cases c <;> rfl

set_option exponentiation.threshold 512 in
theorem ln_slot {P i e : ℕ} (he : e < 36) : ln (slot P i) e = ln P (36 * i + e) := by
  have m1 : (497323236409786642155382248146820840100456150797347717440463976893159497012533375533055 :
      ℕ) = 2 ^ 288 - 1 := by norm_num
  have m2 : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
  change (((P >>> (288 * i)) &&&
      497323236409786642155382248146820840100456150797347717440463976893159497012533375533055) >>>
      (8 * e)) &&& 255 = (P >>> (8 * (36 * i + e))) &&& 255
  rw [m1, m2]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hb : b < 8
  · have h1 : 8 * e + b < 288 := by omega
    have h2 : 288 * i + (8 * e + b) = 8 * (36 * i + e) + b := by ring
    simp [hb, h1, h2]
  · simp [hb]

@[expose] noncomputable def decM (P : ℕ) : Array ℤ := Array.ofFn (n := 36) fun e => ((ln P e.val : ℕ) : ℤ) - 100

theorem size_decM (P : ℕ) : (decM P).size = 36 := by simp [decM]

theorem getD_decM {P e : ℕ} (he : e < 36) : (decM P).getD e 0 = ((ln P e : ℕ) : ℤ) - 100 := by
  rw [decM, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos he, Option.getD_some]

theorem arr_eq_of_getD {a b : Array ℤ} (ha : a.size = 36) (hb : b.size = 36)
    (h : ∀ e < 36, a.getD e 0 = b.getD e 0) : a = b := by
  apply Array.ext (by rw [ha, hb])
  intro e h1 h2
  have := h e (by omega)
  rwa [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this

theorem mulArr_of_prodOK {A B C : ℕ} (h : prodOK A B C = true) :
    syl3MulArr (decM A) (decM B) = decM C := by
  apply arr_eq_of_getD (by simp [syl3MulArr]) (size_decM C)
  intro e he
  have hr : e / 6 < 6 := by omega
  have hc : e % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hrc := allN_true (allN_true h hr) hc
  simp only [dotS, rowS, colS, Nat.add_eq, Nat.mul_eq, Nat.beq_eq] at hrc
  have he' : 6 * (e / 6) + e % 6 = e := Nat.div_add_mod e 6
  rw [he'] at hrc
  rw [syl3MulArr, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos he, Option.getD_some,
    getD_decM he]
  simp only []
  rw [getD_decM (by omega), getD_decM (by omega), getD_decM (by omega), getD_decM (by omega),
    getD_decM (by omega), getD_decM (by omega), getD_decM (by omega), getD_decM (by omega),
    getD_decM (by omega), getD_decM (by omega), getD_decM (by omega), getD_decM (by omega)]
  simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hrc ⊢
  have hz := congrArg (fun x : ℕ => (x : ℤ)) hrc
  push_cast at hz
  have e1 : 6 * 2 + e % 6 = 12 + e % 6 := by norm_num
  have e2 : 6 * 3 + e % 6 = 18 + e % 6 := by norm_num
  have e3 : 6 * 4 + e % 6 = 24 + e % 6 := by norm_num
  have e4 : 6 * 5 + e % 6 = 30 + e % 6 := by norm_num
  rw [e1, e2, e3, e4]
  linear_combination hz

theorem decM_of_chainK {LF : List ℕ} {ONE : ℕ} :
    ∀ (w S : List ℕ), chainK LF ONE w S = true →
      decM (getL 0 S 0) = w.foldr (fun s M => syl3MulArr (decM (getL 0 LF s)) M) (decM ONE) := by
  intro w
  induction w with
  | nil =>
    intro S h
    change Nat.beq (getL 0 S 0) ONE = true at h
    rw [Nat.eq_of_beq_eq_true h]
    rfl
  | cons s w ih =>
    intro S h
    change bAnd(prodOK (getL 0 LF s) (getL 0 S 1) (getL 0 S 0), chainK LF ONE w S.tail) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    have h1 := ih S.tail h.2
    have h2 : getL 0 S.tail 0 = getL 0 S 1 := by
      cases S with
      | nil => rfl
      | cons x S => rfl
    rw [h2] at h1
    rw [List.foldr_cons, ← h1, mulArr_of_prodOK h.1]

theorem codesW_spec {P len : ℕ} :
    ∀ (L : List ℕ) (n : ℕ), codesW P len L n = true →
      L.length + n = len ∧ ∀ m < L.length, L[m]! = ln P (n + m) := by
  intro L
  induction L with
  | nil =>
    intro n h
    change Nat.beq n len = true at h
    exact ⟨by simpa using Nat.eq_of_beq_eq_true h, fun m hm => absurd hm (by simp)⟩
  | cons c L ih =>
    intro n h
    change bAnd(Nat.beq c (ln P n), codesW P len L (Nat.succ n)) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := ih _ h.2
    refine ⟨by simp only [List.length_cons]; omega, fun m hm => ?_⟩
    cases m with
    | zero => simpa using Nat.eq_of_beq_eq_true h.1
    | succ m =>
      have := h2 m (by simpa using hm)
      rw [List.getElem!_cons_succ, this]
      congr 1
      omega

theorem beq_land_one (F n : ℕ) : Nat.beq (Nat.land (Nat.shiftRight F n) 1) 1 = F.testBit n := by
  change ((F >>> n) &&& 1 == 1) = F.testBit n
  rw [Nat.testBit, Nat.and_comm]
  cases h : 1 &&& F >>> n with
  | zero => rfl
  | succ k =>
    have : 1 &&& F >>> n ≤ 1 := Nat.and_le_left
    have hk : k = 0 := by omega
    subst hk
    rfl

theorem land_one_eq (x n : ℕ) : Nat.land (Nat.shiftRight x n) 1 = if x.testBit n then 1 else 0 := by
  have h := beq_land_one x n
  have hle : Nat.land (Nat.shiftRight x n) 1 ≤ 1 := Nat.and_le_right
  cases ht : x.testBit n with
  | true =>
    rw [ht] at h
    simpa using Nat.eq_of_beq_eq_true h
  | false =>
    rw [ht] at h
    have := Nat.ne_of_beq_eq_false h
    simp only [Bool.false_eq_true, if_false]
    omega

theorem length_filter_testBit (x m : ℕ) :
    ((List.range m).filter fun n => x.testBit n).length = cntK x m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    change _ = Nat.add (cntK x m) (Nat.land (Nat.shiftRight x m) 1)
    rw [land_one_eq]
    cases h : x.testBit m <;> simp [h]

theorem dg_eq (n : ℕ) : dg n 0 = n % 3 ∧ dg n 1 = n / 3 % 3 ∧ dg n 2 = n / 9 % 3 ∧
    dg n 3 = n / 27 % 3 ∧ dg n 4 = n / 81 % 3 ∧ dg n 5 = n / 243 % 3 := by
  change n / 3 ^ 0 % 3 = n % 3 ∧ n / 3 ^ 1 % 3 = n / 3 % 3 ∧ n / 3 ^ 2 % 3 = n / 9 % 3 ∧
    n / 3 ^ 3 % 3 = n / 27 % 3 ∧ n / 3 ^ 4 % 3 = n / 81 % 3 ∧ n / 3 ^ 5 % 3 = n / 243 % 3
  norm_num

theorem emod_iff (I : ℤ) (N Y : ℕ) (h : I = (N : ℤ) - 3 * (Y : ℤ)) : I % 3 = 0 ↔ N % 3 = 0 := by
  subst h
  omega

theorem fixArr_decM (A n : ℕ) : syl3FixArr (decM A) (syl3VecArr n) = fixP A n := by
  obtain ⟨d0, d1, d2, d3, d4, d5⟩ := dg_eq n
  unfold syl3FixArr fixP
  rw [CFSG.KC.Misc.ArrEnum.allNP_eq]
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  refine forall_congr' fun c => imp_congr_right fun hc => ?_
  have hc6 := List.mem_range.1 hc
  rw [getD_decM (by omega), getD_decM (by omega), getD_decM (by omega), getD_decM (by omega),
    getD_decM (by omega), getD_decM (by omega)]
  have hx : ∀ t < 6, (syl3VecArr n).getD t 0 = ((dg n t : ℕ) : ℤ) := by
    intro t ht
    interval_cases t <;> simp [syl3VecArr, d0, d1, d2, d3, d4, d5]
  rw [hx 0 (by norm_num), hx 1 (by norm_num), hx 2 (by norm_num), hx 3 (by norm_num),
    hx 4 (by norm_num), hx 5 (by norm_num), hx c hc6]
  unfold fixC
  rw [decide_eq_true_iff, Nat.beq_eq]
  simp only [Nat.add_eq, Nat.mul_eq]
  refine emod_iff _ _ (34 * (dg n 0 + dg n 1 + dg n 2 + dg n 3 + dg n 4 + dg n 5) + dg n c) ?_
  push_cast
  ring

end CFSG.KC.Syl3W.Sound

end
