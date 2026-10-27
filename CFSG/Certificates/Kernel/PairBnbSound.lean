module

public import Certificates.Data.Kernel.PairBnb
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.PairGraph

public section

namespace CFSG.KC.PairBnb

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

theorem forceN_eq {β : Sort _} (y : Nat) (k : Nat → β) : forceN y k = k y := by
  cases y <;> rfl

theorem ble_f {a b : Nat} (h : Nat.ble a b = false) : ¬ a ≤ b :=
  Nat.not_le_of_not_ble_eq_true (by simp [h])

theorem ble_t {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem beq_f {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := Nat.ne_of_beq_eq_false h

theorem beq_t {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem ble_dec (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · simp [ble_f h]
  · simp [ble_t h]

theorem brec_and (a b c : Bool) :
    Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false c b) a =
      (a && b && c) := by
  cases a <;> cases b <;> rfl

theorem brec_or (a : Bool) (b : Bool) :
    Bool.rec (motive := fun _ => Bool) a true b = if b = true then true else a := by
  cases b <;> rfl

theorem log2_shr (y k : Nat) (h : y >>> k ≠ 0) : y.log2 = (y >>> k).log2 + k := by
  rw [Nat.shiftRight_eq_div_pow] at h ⊢
  have hy : y ≠ 0 := fun e => h (by rw [e, Nat.zero_div])
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  have a1 := Nat.log2_self_le h
  have a2 := (Nat.lt_log2_self (n := y / 2 ^ k))
  have d1 := Nat.div_mul_le_self y (2 ^ k)
  have d2 := Nat.lt_mul_div_succ y hp
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply (Nat.log2_lt hy).2
    calc y < 2 ^ k * (y / 2 ^ k + 1) := d2
      _ ≤ 2 ^ k * 2 ^ ((y / 2 ^ k).log2 + 1) := Nat.mul_le_mul_left _ a2
      _ = 2 ^ ((y / 2 ^ k).log2 + k + 1) := by
        rw [← Nat.pow_add]
        congr 1
        omega
  · apply (Nat.le_log2 hy).2
    calc 2 ^ ((y / 2 ^ k).log2 + k) = 2 ^ (y / 2 ^ k).log2 * 2 ^ k := Nat.pow_add _ _ _
      _ ≤ y / 2 ^ k * 2 ^ k := Nat.mul_le_mul_right _ a1
      _ ≤ y := d1

theorem shr_lt (y k : Nat) (hy : y < 2 ^ (k + k)) : y >>> k < 2 ^ k := by
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add]
  exact hy

theorem hb_step (k : Nat) (f : Nat → Nat → Nat) (hf : ∀ y o, y < 2 ^ k → f y o = o + y.log2)
    (y o : Nat) (hy : y < 2 ^ (k + k)) :
    forceN (Nat.shiftRight y k)
      (fun a => Bool.rec (motive := fun _ => Nat) (f a (Nat.add o k)) (f y o) (Nat.beq a 0)) =
      o + y.log2 := by
  rw [forceN_eq]
  cases h : Nat.beq (Nat.shiftRight y k) 0
  · have h0 : y >>> k ≠ 0 := beq_f h
    change f (y >>> k) (o + k) = _
    rw [hf _ _ (shr_lt y k hy), log2_shr y k h0]
    omega
  · have h0 : y >>> k = 0 := beq_t h
    change f y o = _
    apply hf
    rw [Nat.shiftRight_eq_div_pow] at h0
    refine Nat.lt_of_not_le fun hc => ?_
    have := Nat.div_pos hc (Nat.two_pow_pos k)
    omega

theorem logT_lt : ∀ y < 256,
    Nat.land (Nat.shiftRight logT (Nat.shiftLeft y 3)) 255 = Nat.log2 y := by
  decide +kernel

theorem hb8_eq (y o : Nat) (hy : y < 2 ^ 8) : hb8 y o = o + y.log2 := by
  change o + Nat.land (Nat.shiftRight logT (Nat.shiftLeft y 3)) 255 = _
  rw [logT_lt y hy]

theorem hb16_eq (y o : Nat) (hy : y < 2 ^ 16) : hb16 y o = o + y.log2 :=
  hb_step 8 hb8 hb8_eq y o hy

theorem hb32_eq (y o : Nat) (hy : y < 2 ^ 32) : hb32 y o = o + y.log2 :=
  hb_step 16 hb16 hb16_eq y o hy

theorem hb64_eq (y o : Nat) (hy : y < 2 ^ 64) : hb64 y o = o + y.log2 :=
  hb_step 32 hb32 hb32_eq y o hy

theorem hb128_eq (y o : Nat) (hy : y < 2 ^ 128) : hb128 y o = o + y.log2 :=
  hb_step 64 hb64 hb64_eq y o hy

theorem hbR_eq (x : Nat) : hbR x = x.log2 := by
  unfold hbR
  cases h : Nat.blt x 340282366920938463463374607431768211456
  · rfl
  · have h0 : x < 2 ^ 128 := Nat.le_of_ble_eq_true h
    change hb128 x 0 = _
    rw [hb128_eq x 0 h0, Nat.zero_add]

variable (g : WGraph)

theorem growR_eq (fuel cand C mx : Nat) :
    growR g.nb g.wt fuel cand C mx = g.grow fuel cand C mx := by
  induction fuel generalizing cand C mx with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (forceN (hbR cand) fun l => forceN (Nat.land cand (g.nb l)) fun c' =>
        forceN (Nat.lor C (Nat.pow 2 l)) fun C' => forceN (g.wt l) fun w =>
          forceN (Bool.rec mx w (Nat.ble mx w)) fun m' => growR g.nb g.wt n c' C' m')
      (C, mx) (Nat.beq cand 0) = g.grow (n + 1) cand C mx
    simp only [forceN_eq, hbR_eq, ih, WGraph.grow]
    cases h : Nat.beq cand 0
    · simp only [beq_f h, if_false]
      congr 1
      cases h2 : Nat.ble mx (g.wt cand.log2)
      · simp only [Nat.max_def, ble_f h2, if_false]
      · simp only [Nat.max_def, ble_t h2, if_true]
    · simp [beq_t h]

theorem boundR_eq (fuel mask : Nat) : boundR g.nb g.wt fuel mask = g.bound fuel mask := by
  induction fuel generalizing mask with
  | zero =>
    change Bool.rec none (some 0) (Nat.beq mask 0) = g.bound 0 mask
    simp only [WGraph.bound]
    cases h : Nat.beq mask 0
    · simp [beq_f h]
    · simp [beq_t h]
  | succ n ih =>
    change Bool.rec (forceN (hbR mask) fun l =>
        Prod.rec (motive := fun _ => Option Nat)
          (fun C mx => forceN (Nat.xor mask C) fun m' =>
            Option.rec (motive := fun _ => Option Nat) none (fun b => some (Nat.add b mx))
              (boundR g.nb g.wt n m'))
          (growR g.nb g.wt 256 (Nat.land mask (g.nb l)) (Nat.pow 2 l) (g.wt l)))
      (some 0) (Nat.beq mask 0) = g.bound (n + 1) mask
    simp only [forceN_eq, hbR_eq, growR_eq, ih]
    rw [WGraph.bound]
    cases h : Nat.beq mask 0
    · simp only [beq_f h, if_false]
      change _ = Option.map (· + (g.grow 256 (Nat.land mask (g.nb mask.log2)) (Nat.pow 2 mask.log2)
        (g.wt mask.log2)).2) (g.bound n (Nat.xor mask (g.grow 256 (Nat.land mask (g.nb mask.log2))
        (Nat.pow 2 mask.log2) (g.wt mask.log2)).1))
      rcases g.grow 256 (Nat.land mask (g.nb mask.log2)) (Nat.pow 2 mask.log2) (g.wt mask.log2)
        with ⟨C, mx⟩
      rcases g.bound n (Nat.xor mask C) with _ | b <;> rfl
    · simp [beq_t h]

theorem bit_eq (m v : Nat) : Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 v)) = m.testBit v := by
  have key : ∀ j, (m &&& 2 ^ v).testBit j = (m.testBit v && decide (v = j)) := by
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases h : v = j
    · subst h
      simp
    · simp [h]
  change Nat.blt 0 (m &&& 1 <<< v) = _
  rw [Nat.one_shiftLeft]
  cases hb : m.testBit v
  · have h0 : m &&& 2 ^ v = 0 := Nat.eq_of_testBit_eq fun j => by
      rw [key, hb]
      simp
    rw [h0]
    rfl
  · have h0 : m &&& 2 ^ v ≠ 0 := fun h0 => by
      have := key v
      rw [h0, hb] at this
      simp at this
    simpa [Nat.blt_eq, Nat.pos_iff_ne_zero] using h0

theorem findR_eq (mask : Nat) (order : List Nat) :
    findR mask order = order.find? (fun v => mask.testBit v) := by
  induction order with
  | nil => rfl
  | cons v l ih =>
    change Bool.rec (motive := fun _ => Option Nat) (findR mask l) (some v)
      (Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v))) = _
    rw [List.find?_cons, ih, bit_eq]
    cases mask.testBit v <;> rfl

theorem bnbR_eq (order : List Nat) (fuel mask budget : Nat) :
    bnbR g.nb g.wt order fuel mask budget = g.bnb order fuel mask budget := by
  induction fuel generalizing mask budget with
  | zero => rfl
  | succ n ih =>
    change Bool.rec
        (Option.rec (motive := fun _ => Bool) false
          (fun v => forceN (g.wt v) fun w =>
            Bool.rec false
              (Bool.rec false
                (forceN (Nat.xor mask (Nat.pow 2 v)) fun m2 => bnbR g.nb g.wt order n m2 budget)
                (forceN (Nat.xor mask (Nat.land mask (Nat.lor (g.nb v) (Nat.pow 2 v)))) fun m1 =>
                  bnbR g.nb g.wt order n m1 (Nat.sub budget w)))
              (Nat.ble w budget))
          (findR mask order))
        true
        (Option.rec (motive := fun _ => Bool) false (fun b => Nat.ble b budget)
          (boundR g.nb g.wt 256 mask)) = g.bnb order (n + 1) mask budget
    simp only [forceN_eq, ih, boundR_eq, findR_eq, brec_and, ble_dec, brec_or]
    rw [WGraph.bnb]
    generalize g.bound 256 mask = ob
    generalize List.find? (fun v => mask.testBit v) order = of
    rcases ob with _ | b <;> rcases of with _ | v <;> rfl

theorem bnbR_pairGraph (nW : Nat) (L : List Nat) (wR wW : Nat) (nbf : Nat → Nat)
    (hnb : ∀ v, nbf v = L.getD v 0) (order : List Nat) (fuel mask budget : Nat) :
    bnbR nbf (wtF nW wR wW) order fuel mask budget =
      (pairGraph nW L wR wW).bnb order fuel mask budget := by
  have h1 : nbf = (pairGraph nW L wR wW).nb := funext hnb
  have h2 : wtF nW wR wW = (pairGraph nW L wR wW).wt := funext fun v => by
    change Bool.rec (motive := fun _ => Nat) wR wW (Nat.ble (v + 1) nW) =
      if v < nW then wW else wR
    cases h : Nat.ble (v + 1) nW
    · have : ¬ v < nW := ble_f h
      simp [this]
    · have : v < nW := ble_t h
      simp [this]
  rw [h1, h2, bnbR_eq]

theorem wtF_eq (nW : Nat) (L : List Nat) (wR wW v : Nat) :
    wtF nW wR wW v = (pairGraph nW L wR wW).wt v := by
  change Bool.rec (motive := fun _ => Nat) wR wW (Nat.ble (v + 1) nW) =
    if v < nW then wW else wR
  cases h : Nat.ble (v + 1) nW
  · have : ¬ v < nW := ble_f h
    simp [this]
  · have : v < nW := ble_t h
    simp [this]

theorem spR_zero (order : List Nat) (m : Nat) : spR order m 0 = m := rfl

theorem spR_succ (order : List Nat) (m k : Nat) :
    spR order m (k + 1) = Option.rec (motive := fun _ => Nat) (spR order m k)
      (fun v => Nat.xor (spR order m k) (Nat.pow 2 v)) (findR (spR order m k) order) :=
  forceN_eq (spR order m k) fun s' =>
    Option.rec (motive := fun _ => Nat) s' (fun v => Nat.xor s' (Nat.pow 2 v)) (findR s' order)

theorem leafR_spec (nbf wtf : Nat → Nat) (order : List Nat) (fuel budget m k : Nat)
    (h : leafR nbf wtf order fuel budget m k = true) :
    ∃ v, findR (spR order m k) order = some v ∧ wtf v ≤ budget ∧
      bnbR nbf wtf order (fuel - k - 1) (Nat.xor (spR order m k) (Nat.land (spR order m k)
        (Nat.lor (nbf v) (Nat.pow 2 v)))) (budget - wtf v) = true := by
  unfold leafR at h
  simp only [forceN_eq] at h
  cases hf : findR (spR order m k) order with
  | none =>
    rw [hf] at h
    exact absurd h Bool.false_ne_true
  | some v =>
    rw [hf] at h
    dsimp only at h
    cases hw : Nat.ble (wtf v) budget
    · rw [hw] at h
      exact absurd h Bool.false_ne_true
    · rw [hw] at h
      exact ⟨v, rfl, ble_t hw, h⟩

theorem spine_step (order : List Nat) (fuel budget m k n : Nat) (hn : fuel - k - 1 = n)
    (hl : leafR g.nb g.wt order fuel budget m k = true)
    (ih : g.bnb order n (spR order m (k + 1)) budget = true) :
    g.bnb order (n + 1) (spR order m k) budget = true := by
  obtain ⟨v, hf, hw, hb⟩ := leafR_spec g.nb g.wt order fuel budget m k hl
  rw [spR_succ, hf] at ih
  dsimp only at ih
  rw [bnbR_eq, hn] at hb
  have hfind : order.find? (fun v => (spR order m k).testBit v) = some v := by
    rw [← findR_eq]
    exact hf
  rw [WGraph.bnb]
  split_ifs
  · rfl
  · rw [hfind]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hw, hb⟩, ih⟩

theorem bnb_spine (nbf wtf : Nat → Nat) (hnb : ∀ v, nbf v = g.nb v) (hwt : ∀ v, wtf v = g.wt v)
    (order : List Nat) (fuel budget m K : Nat) (hK : K ≤ fuel)
    (hleaf : ∀ k < K, leafR nbf wtf order fuel budget m k = true)
    (htail : bnbR nbf wtf order (fuel - K) (spR order m K) budget = true) :
    g.bnb order fuel m budget = true := by
  obtain rfl : nbf = g.nb := funext hnb
  obtain rfl : wtf = g.wt := funext hwt
  rw [bnbR_eq] at htail
  have key : ∀ n, n ≤ K →
      g.bnb order (fuel - (K - n)) (spR order m (K - n)) budget = true := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa using htail
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      obtain ⟨k, hk⟩ : ∃ k, k = K - (n + 1) := ⟨_, rfl⟩
      rw [← hk]
      have e1 : K - n = k + 1 := by omega
      have e2 : fuel - (k + 1) = fuel - k - 1 := by omega
      have e3 : fuel - k = fuel - k - 1 + 1 := by omega
      rw [e1, e2] at ih'
      rw [e3]
      exact spine_step g order fuel budget m k _ rfl (hleaf k (by omega)) ih'
  have := key K (Nat.le_refl K)
  rwa [Nat.sub_self, Nat.sub_zero, spR_zero] at this

theorem nbP_of_lt (T v s : Nat) (hT : T < 2 ^ s) (hv : s ≤ v * 128) : nbP T v = 0 := by
  have h0 : T >>> (v <<< 7) = 0 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    apply Nat.div_eq_of_lt
    have h7 : v * 2 ^ 7 = v * 128 := rfl
    rw [h7]
    exact Nat.lt_of_lt_of_le hT (Nat.pow_le_pow_right (by decide) hv)
  change (T >>> (v <<< 7)) &&& 340282366920938463463374607431768211455 = 0
  rw [h0, Nat.zero_and]

end CFSG.KC.PairBnb
