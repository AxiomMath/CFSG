module

public import Certificates.Data.Kernel.L34Syl.Defs
public import CFSG.Certificates.Kernel.Spor.PK.PermOf
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.L34Syl.SB

open CFSG.KC.Enum CFSG.KC.L34Syl CFSG.KS.PK

@[expose] noncomputable def gdep (b ng D k : Nat) : Nat :=
  fld(lane (nat_lit 64) (nat_lit 18446744073709551615) D k,
    Nat.add (Nat.add b (nat_lit 4)) (Nat.mul b ng), nat_lit 255)

@[expose] noncomputable def odep (OD k : Nat) : Nat :=
  fld(lane (nat_lit 64) (nat_lit 18446744073709551615) OD k, nat_lit 42, nat_lit 63)

@[expose] noncomputable def sdep (OD k : Nat) : Nat :=
  fld(lane (nat_lit 64) (nat_lit 18446744073709551615) OD k, nat_lit 36, nat_lit 63)

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem band {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true :=
  (CFSG.KS.bAnd_iff a b).1 h

theorem bIf_t {c t e : Bool} (h : bIf(c, t, e) = true) (hc : c = true) : t = true := by
  subst hc
  exact h

theorem bIf_f {c t e : Bool} (h : bIf(c, t, e) = true) (hc : c = false) : e = true := by
  subst hc
  exact h

theorem bNot_t {b : Bool} (h : bNot b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem beqT {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem bltT {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa using h

theorem bleT {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem beq_self (a : Nat) : Nat.beq a a = true := Nat.beq_refl a

theorem beq_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h
  exact Nat.beq_refl a

theorem beq_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem allN_sp {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true :=
  CFSG.KS.allN_spec h

theorem allBlk_in {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (Nat.lt_succ_self len), allBlk_in fun l hl => h l (by omega)]

theorem blocks_in {f : Nat → Bool} : ∀ {q : Nat},
    (∀ h < q, allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) = true) →
    Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q = true
  | 0, _ => rfl
  | q + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q)
      (allBlk (Nat.shiftLeft q (nat_lit 6)) f (nat_lit 64)) = true
    rw [h q (Nat.lt_succ_self q), blocks_in fun l hl => h l (by omega)]

theorem allN_in {n : Nat} {f : Nat → Bool} (h : ∀ i < n, f i = true) : allN n f = true := by
  have e6 : ∀ x : Nat, Nat.shiftLeft x (nat_lit 6) = x * 64 := fun x => by
    change x <<< 6 = x * 64
    rw [Nat.shiftLeft_eq]
  have e64 : Nat.shiftRight n (nat_lit 6) = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have er : Nat.land n (nat_lit 63) = n % 64 := by
    change n &&& (2 ^ 6 - 1) = n % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod n 6
  change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) (Nat.shiftRight n (nat_lit 6)))
      (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
        (Nat.land n (nat_lit 63))) = true
  have h1 : allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) = true := by
    refine allBlk_in fun l hl => h _ ?_
    rw [er] at hl
    rw [e6, e64]
    simp only [Nat.add_eq]
    omega
  have h2 := blocks_in (f := f) (q := Nat.shiftRight n (nat_lit 6)) fun q hq => by
    refine allBlk_in fun l hl => h _ ?_
    rw [e64] at hq
    rw [e6]
    simp only [Nat.add_eq]
    have : l < 64 := hl
    omega
  rw [h1, h2]

theorem eq2_sp {n w m r p q : Nat} (h : eq2 n w m r p q = true) :
    ∀ i < n, pg w m r i = pg w m p (pg w m q i) :=
  fun i hi => beqT (allN_sp h i hi)

theorem eq22_sp {n w m p q r s : Nat} (h : eq22 n w m p q r s = true) :
    ∀ i < n, pg w m p (pg w m q i) = pg w m r (pg w m s i) :=
  fun i hi => beqT (allN_sp h i hi)

theorem canonP_sp {n w m nw x : Nat} (h : canonP n w m nw x = true) :
    x >>> nw = 0 ∧ ∀ i < n, pg w m x i < n := by
  obtain ⟨h1, h2⟩ := band h
  exact ⟨beqT h1, fun i hi => bltT (allN_sp h2 i hi)⟩

theorem invPt_sp {n w m x y : Nat} (h : invPt n w m x y = true) :
    ∀ i < n, pg w m x (pg w m y i) = i :=
  fun i hi => beqT (allN_sp h i hi)

theorem idPt_sp {n w m x : Nat} (h : idPt n w m x = true) : ∀ i < n, pg w m x i = i :=
  fun i hi => beqT (allN_sp h i hi)

theorem fld_eq (x o b : Nat) : fld(x, o, 2 ^ b - 1) = x / 2 ^ o % 2 ^ b := by
  change x >>> o &&& (2 ^ b - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem lt_of_shr {x nw : Nat} (h : x >>> nw = 0) : x < 2 ^ nw := by
  rw [Nat.shiftRight_eq_div_pow] at h
  have e := Nat.div_add_mod x (2 ^ nw)
  have hm := Nat.mod_lt x (Nat.two_pow_pos nw)
  rw [h, Nat.mul_zero, Nat.zero_add] at e
  omega

theorem mask_eq (w : Nat) : CFSG.KS.mask w = 2 ^ w - 1 := by
  change (1 <<< w) - 1 = _
  rw [Nat.one_shiftLeft]

theorem blt_land (s i : Nat) :
    Nat.blt (nat_lit 0) (Nat.land s (Nat.shiftLeft (nat_lit 1) i)) = s.testBit i := by
  change Nat.blt 0 (s &&& 1 <<< i) = _
  rw [Nat.one_shiftLeft]
  cases hs : s.testBit i
  · have e : s &&& 2 ^ i = 0 := Nat.eq_of_testBit_eq fun j => by
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases e : i = j
      · subst e
        simp [hs]
      · simp [e]
    rw [e]
    rfl
  · have ht : (s &&& 2 ^ i).testBit i = true := by
      rw [Nat.testBit_and, Nat.testBit_two_pow, hs]
      simp
    have hpos : 0 < s &&& 2 ^ i := Nat.pos_of_ne_zero fun h => by
      rw [h, Nat.zero_testBit] at ht
      exact absurd ht (by decide)
    simpa using hpos

theorem testBit_shl1 (x j : Nat) : (Nat.shiftLeft (nat_lit 1) x).testBit j = decide (x = j) := by
  change (1 <<< x).testBit j = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem xor_even (j : Nat) : Nat.xor (2 * j) (nat_lit 1) = 2 * j + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((2 * j) ^^^ 1).testBit i = _
  rw [Nat.testBit_xor]
  cases i with
  | zero =>
    have h1 : 2 * j % 2 = 0 := by omega
    have h2 : (2 * j + 1) % 2 = 1 := by omega
    simp [Nat.testBit_zero, h1, h2]
  | succ i =>
    have h1 : 2 * j / 2 = j := by omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    simp [Nat.testBit_succ, h1, h2]

theorem xor_odd (j : Nat) : Nat.xor (2 * j + 1) (nat_lit 1) = 2 * j := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((2 * j + 1) ^^^ 1).testBit i = _
  rw [Nat.testBit_xor]
  cases i with
  | zero =>
    have h1 : 2 * j % 2 = 0 := by omega
    have h2 : (2 * j + 1) % 2 = 1 := by omega
    simp [Nat.testBit_zero, h1, h2]
  | succ i =>
    have h1 : 2 * j / 2 = j := by omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    simp [Nat.testBit_succ, h1, h2]

theorem lor_testBit (a b j : Nat) : (Nat.lor a b).testBit j = (a.testBit j || b.testBit j) :=
  Nat.testBit_or a b j

theorem img_testBit (n w m g s j : Nat) :
    (img n w m g s).testBit j = true ↔ ∃ i < n, s.testBit i = true ∧ pg w m g i = j := by
  unfold img
  induction n with
  | zero => simp
  | succ n ih =>
    change (Nat.lor (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i ih => Nat.lor ih (nIf(Nat.blt (nat_lit 0) (Nat.land s (Nat.shiftLeft (nat_lit 1) i)),
        Nat.shiftLeft (nat_lit 1) (pg w m g i), nat_lit 0))) n)
      (nIf(Nat.blt (nat_lit 0) (Nat.land s (Nat.shiftLeft (nat_lit 1) n)),
        Nat.shiftLeft (nat_lit 1) (pg w m g n), nat_lit 0))).testBit j = true ↔ _
    rw [lor_testBit, Bool.or_eq_true, ih, blt_land]
    constructor
    · rintro (⟨i, hi, h1, h2⟩ | h)
      · exact ⟨i, by omega, h1, h2⟩
      · cases hs : s.testBit n
        · rw [hs] at h
          simp at h
        · rw [hs] at h
          change (Nat.shiftLeft (nat_lit 1) (pg w m g n)).testBit j = true at h
          rw [testBit_shl1] at h
          exact ⟨n, by omega, hs, by simpa using h⟩
    · rintro ⟨i, hi, h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h1, h2⟩
      · right
        rw [h1]
        change (Nat.shiftLeft (nat_lit 1) (pg w m g i)).testBit j = true
        rw [testBit_shl1, h2]
        simp

theorem fold_testBit (f : Nat → Nat) (K j : Nat) :
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) (f k))) K : Nat).testBit j = true ↔
      ∃ a < K, f a = j := by
  induction K with
  | zero => simp
  | succ K ih =>
    change (Nat.lor (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) (f k))) K)
      (Nat.shiftLeft (nat_lit 1) (f K))).testBit j = true ↔ _
    rw [lor_testBit, Bool.or_eq_true, ih, testBit_shl1]
    constructor
    · rintro (⟨a, ha, h⟩ | h)
      · exact ⟨a, by omega, h⟩
      · exact ⟨K, by omega, by simpa using h⟩
    · rintro ⟨a, ha, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · exact Or.inl ⟨a, ha, h⟩
      · right
        simpa using h

theorem cntK_eq (N : Nat) (f : Nat → Bool) :
    cntK N f = ((Finset.range N).filter fun k => f k = true).card := by
  unfold cntK
  induction N with
  | zero => simp
  | succ N ih =>
    change Bool.rec (motive := fun _ => Nat)
        (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun k ih => Bool.rec (motive := fun _ => Nat) ih (Nat.succ ih) (f k)) N)
        (Nat.succ (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun k ih => Bool.rec (motive := fun _ => Nat) ih (Nat.succ ih) (f k)) N)) (f N) = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    have hN : N ∉ (Finset.range N).filter fun k => f k = true := by simp
    cases f N
    · simp
    · simp [Finset.card_insert_of_notMem hN]

theorem isPermN_congr' {n : Nat} {f g : Nat → Nat} (h : ∀ x < n, f x = g x) (hf : IsPermN n f) :
    IsPermN n g := by
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · rw [← h x hx]
    exact hf.1 x hx
  · rw [← h x hx, ← h y hy] at hxy
    exact hf.2 x hx y hy hxy

theorem permOf_id' (n : Nat) : permOf n (fun x => x) = 1 :=
  (permOf_eq_one_iff (isPermN_id n)).2 fun _ _ => rfl

theorem itr_succ' (f : Nat → Nat) : ∀ k x, itr f (k + 1) x = itr f k (f x)
  | 0, _ => rfl
  | k + 1, x => by
    change f (itr f (k + 1) x) = f (itr f k (f x))
    rw [itr_succ' f k x]

theorem isPermN_itr' {n : Nat} {f : Nat → Nat} (hf : IsPermN n f) : ∀ k, IsPermN n (itr f k)
  | 0 => isPermN_id n
  | k + 1 => hf.comp (isPermN_itr' hf k)

theorem canonW_sp {w m X y1 : Nat} : ∀ {s y : Nat}, canonW w m X y1 s y = true →
    ∀ i < s, y1 < itr (pg w m X) (i + 1) y
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | s + 1, y, h, i, hi => by
    have h' : strictB (pg w m X y) (fun y' => bAnd(Nat.blt y1 y', canonW w m X y1 s y')) = true :=
      h
    rw [sB] at h'
    obtain ⟨h1, h2⟩ := band h'
    cases i with
    | zero => exact bltT h1
    | succ i =>
      rw [itr_succ']
      exact canonW_sp h2 i (by omega)

theorem depth_ind {N : Nat} {dep : Nat → Nat} {P : Nat → Prop}
    (h0 : ∀ k < N, dep k = 0 → P k)
    (hs : ∀ k < N, dep k ≠ 0 → ∃ par < N, dep par + 1 = dep k ∧ (P par → P k)) :
    ∀ k < N, P k := by
  suffices ∀ d, ∀ k < N, dep k = d → P k from fun k hk => this _ k hk rfl
  intro d
  induction d with
  | zero => exact h0
  | succ d ih =>
    intro k hk hd
    obtain ⟨par, hp, hdp, hP⟩ := hs k hk (by omega)
    exact hP (ih par hp (by omega))

theorem exists_dep0 {N : Nat} {dep : Nat → Nat} (hN : 0 < N)
    (hs : ∀ k < N, dep k ≠ 0 → ∃ par < N, dep par + 1 = dep k) : ∃ k < N, dep k = 0 := by
  refine depth_ind (P := fun _ => ∃ k < N, dep k = 0) (fun k hk h => ⟨k, hk, h⟩)
    (fun k hk h => ?_) 0 hN
  obtain ⟨par, hp, e⟩ := hs k hk h
  exact ⟨par, hp, e, id⟩

theorem mono_of_adj {N : Nat} {f : Nat → Nat} (h : ∀ k < N, k ≠ 0 → f (k - 1) < f k) :
    ∀ k < N, ∀ k' < N, k < k' → f k < f k' := by
  suffices ∀ d k, k + d + 1 < N → f k < f (k + d + 1) by
    intro k hk k' hk' hlt
    have := this (k' - k - 1) k (by omega)
    have e : k + (k' - k - 1) + 1 = k' := by omega
    rwa [e] at this
  intro d
  induction d with
  | zero =>
    intro k hk
    have := h (k + 1) (by omega) (by omega)
    simpa using this
  | succ d ih =>
    intro k hk
    have h1 := ih k (by omega)
    have h2 := h (k + d + 2) (by omega) (by omega)
    have e1 : k + d + 2 - 1 = k + d + 1 := by omega
    have e2 : k + (d + 1) + 1 = k + d + 2 := by omega
    rw [e1] at h2
    rw [e2]
    omega

theorem pow_mul_mem {G : Type*} [Group G] {S : Set G} {x : G} (hx : ∀ y ∈ S, x * y ∈ S) :
    ∀ k, ∀ y ∈ S, x ^ k * y ∈ S
  | 0, y, hy => by rwa [pow_zero, one_mul]
  | k + 1, y, hy => by
    rw [pow_succ, mul_assoc]
    exact pow_mul_mem hx k _ (hx y hy)

theorem closure_sub {G : Type*} [Group G] [Finite G] {s S : Set G} (h1 : (1 : G) ∈ S)
    (hm : ∀ x ∈ s, ∀ y ∈ S, x * y ∈ S) : ∀ g ∈ Subgroup.closure s, g ∈ S := by
  let H : Subgroup G :=
    { carrier := {g | ∀ y ∈ S, g * y ∈ S}
      one_mem' := fun y hy => by rwa [one_mul]
      mul_mem' := fun {a b} ha hb y hy => by
        rw [mul_assoc]
        exact ha _ (hb y hy)
      inv_mem' := fun {a} ha y hy => by
        have hpos := orderOf_pos a
        have e : a ^ (orderOf a - 1) = a⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        rw [← e]
        exact pow_mul_mem ha _ y hy }
  intro g hg
  have hle : Subgroup.closure s ≤ H := (Subgroup.closure_le H).2 fun x hx => hm x hx
  have := hle hg 1 h1
  rwa [mul_one] at this

end CFSG.KC.L34Syl.SB

end
