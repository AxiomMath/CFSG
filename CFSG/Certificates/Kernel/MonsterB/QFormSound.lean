module

public import Certificates.Data.Kernel.MonsterB.QForm
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound

public section

namespace CFSG.KC.QForm

open CFSG.KLie.CT CFSG.KC.U6Orb CFSG.KC.Bfs

theorem xorK_xor (n : ℕ) (f g : ℕ → ℕ) :
    xorK n (fun t => f t ^^^ g t) = xorK n f ^^^ xorK n g := by
  induction n with
  | zero =>
    change 0 = 0 ^^^ 0
    rw [Nat.xor_self]
  | succ n ih =>
    rw [xorK_succ, xorK_succ, xorK_succ, ih]
    ac_rfl

theorem xorK_zero {n : ℕ} {f : ℕ → ℕ} (h : ∀ t < n, f t = 0) : xorK n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorK_succ, h n (Nat.lt_succ_self n), ih fun t ht => h t (Nat.lt_succ_of_lt ht),
      Nat.xor_self]

theorem xorK_single {n a : ℕ} {f : ℕ → ℕ} (ha : a < n) (h : ∀ t < n, t ≠ a → f t = 0) :
    xorK n f = f a := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [xorK_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
    · rw [h n (Nat.lt_succ_self n) (by omega), Nat.zero_xor,
        ih ha fun t ht hta => h t (Nat.lt_succ_of_lt ht) hta]
    · rw [xorK_zero fun t ht => h t (Nat.lt_succ_of_lt ht) (by omega), Nat.xor_zero]

theorem xorK_lt {n w : ℕ} {f : ℕ → ℕ} (h : ∀ t < n, f t < 2 ^ w) : xorK n f < 2 ^ w := by
  induction n with
  | zero => exact Nat.two_pow_pos w
  | succ n ih =>
    rw [xorK_succ]
    exact Nat.xor_lt_two_pow (h n (Nat.lt_succ_self n)) (ih fun t ht => h t (Nat.lt_succ_of_lt ht))

theorem nIf_bit_xor (a b t m : ℕ) :
    Bool.rec (motive := fun _ => ℕ) 0 m (bit (a ^^^ b) t) =
      Bool.rec (motive := fun _ => ℕ) 0 m (bit a t) ^^^
        Bool.rec (motive := fun _ => ℕ) 0 m (bit b t) := by
  rw [bit_eq, bit_eq, bit_eq, Nat.testBit_xor]
  cases a.testBit t <;> cases b.testBit t <;> simp

theorem actK_xor (M a b : ℕ) : actK M (a ^^^ b) = actK M a ^^^ actK M b := by
  unfold actK
  rw [← xorK_xor]
  exact xorK_congr fun t _ => nIf_bit_xor a b t _

theorem actK_two_pow (M : ℕ) {a : ℕ} (ha : a < 22) : actK M (2 ^ a) = fget M a 22 := by
  unfold actK
  rw [xorK_single (a := a) ha]
  · change Bool.rec (motive := fun _ => ℕ) 0 _ (bit (2 ^ a) a) = _
    rw [bit_eq, Nat.testBit_two_pow, decide_eq_true rfl]
  · intro t _ hta
    change Bool.rec (motive := fun _ => ℕ) 0 _ (bit (2 ^ a) t) = 0
    rw [bit_eq, Nat.testBit_two_pow, decide_eq_false (Ne.symm hta)]

theorem fget_lt (X i w : ℕ) : fget X i w < 2 ^ w := by
  rw [fget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem actK_lt (M v : ℕ) : actK M v < 2 ^ 22 := by
  unfold actK
  refine xorK_lt fun t _ => ?_
  cases bit v t
  · exact Nat.two_pow_pos 22
  · exact fget_lt _ _ _

theorem xor_le_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a ^^^ b ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl <;> decide

theorem xorK_le_one {n : ℕ} {f : ℕ → ℕ} (h : ∀ t < n, f t ≤ 1) : xorK n f ≤ 1 := by
  induction n with
  | zero => exact Nat.zero_le 1
  | succ n ih =>
    rw [xorK_succ]
    exact xor_le_one (h n (Nat.lt_succ_self n)) (ih fun t ht => h t (Nat.lt_succ_of_lt ht))

theorem parK_le (x : ℕ) : parK x ≤ 1 := xorK_le_one fun _ _ => Nat.and_le_right

theorem bK_eq (U x y : ℕ) : bK U x y = betaK U x y ^^^ betaK U y x := rfl

theorem parK_xor (a b : ℕ) : parK (a ^^^ b) = parK a ^^^ parK b := by
  unfold parK
  rw [← xorK_xor]
  refine xorK_congr fun t _ => ?_
  change ((a ^^^ b) >>> t) &&& 1 = ((a >>> t) &&& 1) ^^^ ((b >>> t) &&& 1)
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]

theorem betaK_xor_right (U x y y' : ℕ) : betaK U x (y ^^^ y') = betaK U x y ^^^ betaK U x y' := by
  unfold betaK
  change parK ((y ^^^ y') &&& actK U x) = parK (y &&& actK U x) ^^^ parK (y' &&& actK U x)
  rw [Nat.and_xor_distrib_right, parK_xor]

theorem betaK_xor_left (U x x' y : ℕ) : betaK U (x ^^^ x') y = betaK U x y ^^^ betaK U x' y := by
  unfold betaK
  change parK (y &&& actK U (x ^^^ x')) = parK (y &&& actK U x) ^^^ parK (y &&& actK U x')
  rw [actK_xor, Nat.and_xor_distrib_left, parK_xor]

theorem qK_xor (U x y : ℕ) : qK U (x ^^^ y) = qK U x ^^^ qK U y ^^^ bK U x y := by
  unfold qK
  rw [bK_eq, betaK_xor_left, betaK_xor_right, betaK_xor_right]
  ac_rfl

theorem bK_comm (U x y : ℕ) : bK U x y = bK U y x := by
  rw [bK_eq, bK_eq]
  exact Nat.xor_comm _ _

theorem bK_self (U x : ℕ) : bK U x x = 0 := by
  rw [bK_eq, Nat.xor_self]

theorem bK_xor_left (U x x' y : ℕ) : bK U (x ^^^ x') y = bK U x y ^^^ bK U x' y := by
  rw [bK_eq, bK_eq, bK_eq, betaK_xor_left, betaK_xor_right]
  ac_rfl

theorem bK_xor_right (U x y y' : ℕ) : bK U x (y ^^^ y') = bK U x y ^^^ bK U x y' := by
  rw [bK_comm, bK_xor_left, bK_comm U y, bK_comm U y']

theorem bK_le (U x y : ℕ) : bK U x y ≤ 1 := xor_le_one (parK_le _) (parK_le _)

theorem qK_le (U x : ℕ) : qK U x ≤ 1 := parK_le _

theorem eq_of_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  calc a = a ^^^ (b ^^^ b) := by rw [Nat.xor_self, Nat.xor_zero]
    _ = b := by rw [← Nat.xor_assoc, h, Nat.zero_xor]

theorem xor_two_pow_of_lt {y m : ℕ} (hy : y < 2 ^ m) : y ^^^ 2 ^ m = 2 ^ m + y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases lt_trichotomy i m with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h, decide_eq_false (by omega), Bool.xor_false]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy, decide_eq_true rfl]
    rfl
  · have h1 : y < 2 ^ i := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) h.le)
    have h2 : 2 ^ m + y < 2 ^ i := by
      have : 2 ^ (m + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) h
      rw [Nat.pow_succ] at this
      omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2, decide_eq_false (by omega)]
    rfl

theorem zero_of_xor_hom {F : ℕ → ℕ} {n : ℕ}
    (hF : ∀ a < 2 ^ n, ∀ b < 2 ^ n, F (a ^^^ b) = F a ^^^ F b) (h1 : ∀ i < n, F (2 ^ i) = 0) :
    ∀ x < 2 ^ n, F x = 0 := by
  have h0 : F 0 = 0 := by
    have := hF 0 (Nat.two_pow_pos n) 0 (Nat.two_pow_pos n)
    rwa [Nat.xor_self, Nat.xor_self] at this
  suffices H : ∀ m ≤ n, ∀ x < 2 ^ m, F x = 0 from fun x hx => H n le_rfl x hx
  intro m
  induction m with
  | zero =>
    intro _ x hx
    rw [Nat.pow_zero, Nat.lt_one_iff] at hx
    rw [hx]
    exact h0
  | succ m ih =>
    intro hm x hx
    by_cases hxm : x < 2 ^ m
    · exact ih (by omega) x hxm
    · have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
      have hlt : x - 2 ^ m < 2 ^ m := by omega
      have e : x = (x - 2 ^ m) ^^^ 2 ^ m := by rw [xor_two_pow_of_lt hlt]; omega
      have hmn : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have hmn' : 2 ^ m < 2 ^ n := Nat.pow_lt_pow_right (by decide) (by omega)
      have h2 : F ((x - 2 ^ m) ^^^ 2 ^ m) = 0 := by
        rw [hF (x - 2 ^ m) (by omega) (2 ^ m) hmn', ih (by omega) _ hlt, h1 m (by omega),
          Nat.xor_self]
      rw [e]
      exact h2

theorem invK_sound {U M : ℕ} (h : invK U M = true) :
    (∀ x < 2 ^ 22, ∀ y < 2 ^ 22, bK U (actK M x) (actK M y) = bK U x y) ∧
      ∀ x < 2 ^ 22, qK U (actK M x) = qK U x := by
  rw [invK, allN_iff] at h
  have hq : ∀ a < 22, qK U (actK M (2 ^ a)) = qK U (2 ^ a) := fun a ha => by
    have := (andB_eq_true.1 (h a ha)).1
    rw [actK_two_pow M ha, ← pw2_eq]
    exact Nat.eq_of_beq_eq_true this
  have hb : ∀ a < 22, ∀ b < 22,
      bK U (actK M (2 ^ a)) (actK M (2 ^ b)) = bK U (2 ^ a) (2 ^ b) := fun a ha b hb => by
    have := (andB_eq_true.1 (h a ha)).2
    rw [allN_iff] at this
    rw [actK_two_pow M ha, actK_two_pow M hb, ← pw2_eq, ← pw2_eq]
    exact Nat.eq_of_beq_eq_true (this b hb)
  have hE : ∀ x < 2 ^ 22, ∀ y < 2 ^ 22, bK U (actK M x) (actK M y) ^^^ bK U x y = 0 := by
    have hadd : ∀ y, ∀ a b : ℕ, (bK U (actK M (a ^^^ b)) (actK M y) ^^^ bK U (a ^^^ b) y) =
        (bK U (actK M a) (actK M y) ^^^ bK U a y) ^^^
          (bK U (actK M b) (actK M y) ^^^ bK U b y) := by
      intro y a b
      rw [actK_xor, bK_xor_left, bK_xor_left]
      ac_rfl
    have h1 : ∀ b < 22, ∀ x < 2 ^ 22, bK U (actK M x) (actK M (2 ^ b)) ^^^ bK U x (2 ^ b) = 0 :=
      fun b hb' => zero_of_xor_hom
        (F := fun x => bK U (actK M x) (actK M (2 ^ b)) ^^^ bK U x (2 ^ b))
        (fun a _ c _ => hadd _ a c) fun a ha => by rw [hb a ha b hb', Nat.xor_self]
    intro x hx
    refine zero_of_xor_hom (F := fun y => bK U (actK M x) (actK M y) ^^^ bK U x y)
      (fun a _ c _ => ?_) (fun b hb' => h1 b hb' x hx)
    rw [actK_xor, bK_xor_right, bK_xor_right]
    ac_rfl
  have hB : ∀ x < 2 ^ 22, ∀ y < 2 ^ 22, bK U (actK M x) (actK M y) = bK U x y :=
    fun x hx y hy => eq_of_xor_eq_zero (hE x hx y hy)
  refine ⟨hB, fun x hx => eq_of_xor_eq_zero ?_⟩
  refine zero_of_xor_hom (F := fun x => qK U (actK M x) ^^^ qK U x) (fun a ha c hc => ?_)
    (fun a ha => by rw [hq a ha, Nat.xor_self]) x hx
  rw [actK_xor, qK_xor, qK_xor, hB a ha c hc]
  generalize bK U a c = t
  generalize qK U a = p
  generalize qK U c = r
  generalize qK U (actK M a) = p'
  generalize qK U (actK M c) = r'
  calc p' ^^^ r' ^^^ t ^^^ (p ^^^ r ^^^ t) = p' ^^^ r' ^^^ (p ^^^ r) ^^^ (t ^^^ t) := by ac_rfl
    _ = _ := by rw [Nat.xor_self, Nat.xor_zero]; ac_rfl

theorem split_bytes (v : ℕ) :
    v = (v &&& 255) ^^^ ((((v >>> 8) &&& 255) <<< 8) ^^^ ((v >>> 16) <<< 16)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e255 : (255 : ℕ) = 2 ^ 8 - 1 := rfl
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, e255,
    Nat.testBit_two_pow_sub_one]
  by_cases h8 : i < 8
  · simp [h8, show ¬ i ≥ 8 by omega, show ¬ i ≥ 16 by omega]
  · by_cases h16 : i < 16
    · have e : 8 + (i - 8) = i := by omega
      simp [h8, show i ≥ 8 by omega, show ¬ i ≥ 16 by omega, e, show i - 8 < 8 by omega]
    · have e : 16 + (i - 16) = i := by omega
      simp [h8, show i ≥ 8 by omega, show i ≥ 16 by omega, e, show ¬ i - 8 < 8 by omega]

theorem actB_eq {T M : ℕ → ℕ} {ng : ℕ} (h : tabOK T M ng = true) {k : ℕ} (hk : k < ng)
    {v : ℕ} (hv : v < 2 ^ 22) : actB T k v = actK (M k) v := by
  rw [tabOK, allN_iff] at h
  obtain ⟨h0, h1, h2⟩ : _ ∧ _ ∧ _ := by
    have := h k hk
    rw [andB_eq_true, andB_eq_true] at this
    exact this
  rw [allN_iff] at h0 h1 h2
  have b0 : v &&& 255 < 256 := Nat.lt_succ_of_le Nat.and_le_right
  have b1 : (v >>> 8) &&& 255 < 256 := Nat.lt_succ_of_le Nat.and_le_right
  have b2 : v >>> 16 < 64 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by omega)
  have e0 := Nat.eq_of_beq_eq_true (h0 _ b0)
  have e1 := Nat.eq_of_beq_eq_true (h1 _ b1)
  have e2 := Nat.eq_of_beq_eq_true (h2 _ b2)
  change fget (T (3 * k)) (v &&& 255) 22 ^^^ (fget (T (3 * k + 1)) ((v >>> 8) &&& 255) 22 ^^^
    fget (T (3 * k + 2)) (v >>> 16) 22) = _
  change fget (T (3 * k)) (v &&& 255) 22 = actK (M k) (v &&& 255) at e0
  change fget (T (3 * k + 1)) ((v >>> 8) &&& 255) 22 = actK (M k) (((v >>> 8) &&& 255) <<< 8) at e1
  change fget (T (3 * k + 2)) (v >>> 16) 22 = actK (M k) ((v >>> 16) <<< 16) at e2
  rw [e0, e1, e2, ← actK_xor, ← actK_xor, ← split_bytes]

theorem xor_one_of_ne {a : ℕ} (ha : a ≤ 1) (h : a ≠ 1) : a ^^^ 1 = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl
  · rfl
  · exact absurd rfl h

theorem card_singular {U s z : ℕ} (hs : s < 2 ^ 22) (hz : z < 2 ^ 22) (hq : qK U s = 0)
    (hb : bK U s z = 1) :
    ((Finset.range (2 ^ 22)).filter fun v => bK U s v = 1 ∧ qK U v = 0).card = 2 ^ 20 := by
  set R := Finset.range (2 ^ 22)
  have hxz : ∀ v, v ^^^ z ^^^ z = v := fun v => by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hxs : ∀ v, v ^^^ s ^^^ s = v := fun v => by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hR : ∀ {v w}, v ∈ R → w < 2 ^ 22 → v ^^^ w ∈ R := fun hv hw =>
    Finset.mem_range.2 (Nat.xor_lt_two_pow (Finset.mem_range.1 hv) hw)
  have hbz : ∀ v, bK U s (v ^^^ z) = bK U s v ^^^ 1 := fun v => by rw [bK_xor_right, hb]
  have h01 : ∀ v, bK U s v ≠ 1 ↔ bK U s v = 0 := fun v => by
    have := bK_le U s v
    omega
  have hA : (R.filter fun v => ¬ bK U s v = 1).card = (R.filter fun v => bK U s v = 1).card := by
    refine Finset.card_nbij' (· ^^^ z) (· ^^^ z) (fun v hv => ?_) (fun v hv => ?_)
      (fun v _ => hxz v) (fun v _ => hxz v)
    · rw [Finset.mem_coe, Finset.mem_filter] at hv ⊢
      refine ⟨hR hv.1 hz, ?_⟩
      rw [hbz, (h01 v).1 hv.2]
      rfl
    · rw [Finset.mem_coe, Finset.mem_filter] at hv ⊢
      refine ⟨hR hv.1 hz, ?_⟩
      rw [hbz, hv.2]
      decide
  have hA1 : (R.filter fun v => bK U s v = 1).card = 2 ^ 21 := by
    have := Finset.card_filter_add_card_filter_not (s := R) (fun v => bK U s v = 1)
    rw [hA, Finset.card_range] at this
    omega
  have hqs : ∀ v, bK U s v = 1 → bK U s (v ^^^ s) = 1 ∧ qK U (v ^^^ s) = qK U v ^^^ 1 :=
    fun v hv => ⟨by rw [bK_xor_right, bK_self, Nat.xor_zero, hv], by
      rw [qK_xor, hq, Nat.xor_zero, bK_comm, hv]⟩
  set A1 := R.filter fun v => bK U s v = 1
  have hV : (R.filter fun v => bK U s v = 1 ∧ qK U v = 0) = A1.filter fun v => qK U v = 0 := by
    rw [Finset.filter_filter]
  have hW : (A1.filter fun v => ¬ qK U v = 0).card = (A1.filter fun v => qK U v = 0).card := by
    refine Finset.card_nbij' (· ^^^ s) (· ^^^ s) (fun v hv => ?_) (fun v hv => ?_)
      (fun v _ => hxs v) (fun v _ => hxs v)
    · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at hv ⊢
      obtain ⟨hs1, hs2⟩ := hqs v hv.1.2
      refine ⟨⟨hR hv.1.1 hs, hs1⟩, ?_⟩
      have := qK_le U v
      rw [hs2, show qK U v = 1 by omega]
      rfl
    · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at hv ⊢
      obtain ⟨hs1, hs2⟩ := hqs v hv.1.2
      refine ⟨⟨hR hv.1.1 hs, hs1⟩, ?_⟩
      rw [hs2, hv.2]
      decide
  have := Finset.card_filter_add_card_filter_not (s := A1) (fun v => qK U v = 0)
  rw [hW, hA1] at this
  rw [hV]
  omega

theorem reach_inv {act : ℕ → ℕ → ℕ} {ng root : ℕ} {P : ℕ → Prop} (h0 : P root)
    (hs : ∀ k < ng, ∀ x, P x → P (act k x)) {x : ℕ} (h : Reach act ng root x) : P x := by
  induction h with
  | root => exact h0
  | step k hk _ ih => exact hs k hk _ ih

theorem reach_congr {act act' : ℕ → ℕ → ℕ} {ng root : ℕ} {P : ℕ → Prop} (h0 : P root)
    (hs : ∀ k < ng, ∀ x, P x → P (act k x)) (he : ∀ k < ng, ∀ x, P x → act' k x = act k x)
    {x : ℕ} : Reach act' ng root x ↔ Reach act ng root x := by
  constructor
  · intro h
    have H : P x ∧ Reach act ng root x := by
      induction h with
      | root => exact ⟨h0, Reach.root⟩
      | step k hk _ ih =>
        rw [he k hk _ ih.1]
        exact ⟨hs k hk _ ih.1, Reach.step k hk ih.2⟩
    exact H.2
  · intro h
    have H : P x ∧ Reach act' ng root x := by
      induction h with
      | root => exact ⟨h0, Reach.root⟩
      | step k hk _ ih =>
        refine ⟨hs k hk _ ih.1, ?_⟩
        rw [← he k hk _ ih.1]
        exact Reach.step k hk ih.2
    exact H.2

end CFSG.KC.QForm

end
