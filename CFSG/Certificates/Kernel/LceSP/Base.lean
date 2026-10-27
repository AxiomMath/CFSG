module

public import Certificates.Data.Kernel.LceSTab
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Group

public section

namespace CFSG.Certificates.LceP

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop

theorem andB_iff (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem orB_iff (a b : Bool) : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem letB_eq (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by
  cases v <;> rfl

theorem strictN_eq (v : ℕ) (k : ℕ → ℕ) : strictN v k = k v := by
  cases v <;> rfl

theorem brec_eq {α : Sort*} (a b : α) (c : Bool) :
    Bool.rec (motive := fun _ => α) a b c = if c = true then b else a := by
  cases c <;> rfl

theorem allRec_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc (f q)) n = true ↔
      ∀ q < n, f q = true
  | 0 => ⟨fun _ q hq => absurd hq (Nat.not_lt_zero q), fun _ => rfl⟩
  | n + 1 => by
    change andB (Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc (f q)) n) (f n) =
      true ↔ _
    rw [andB_iff, allRec_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | rfl
      · exact h1 q h
      · exact h2
    · intro h
      exact ⟨fun q hq => h q (by omega), h n (by omega)⟩

theorem allRec2_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun q acc => andB (f q) acc) n = true ↔
      ∀ q < n, f q = true
  | 0 => ⟨fun _ q hq => absurd hq (Nat.not_lt_zero q), fun _ => rfl⟩
  | n + 1 => by
    change andB (f n) (Nat.rec (motive := fun _ => Bool) true (fun q acc => andB (f q) acc) n) =
      true ↔ _
    rw [andB_iff, allRec2_iff f n]
    constructor
    · rintro ⟨h2, h1⟩ q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | rfl
      · exact h1 q h
      · exact h2
    · intro h
      exact ⟨h n (by omega), fun q hq => h q (by omega)⟩

theorem anyRec_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) false (fun q acc => orB acc (f q)) n = true →
      ∃ q < n, f q = true
  | 0 => fun h => absurd h Bool.false_ne_true
  | n + 1 => fun h => by
    change orB (Nat.rec (motive := fun _ => Bool) false (fun q acc => orB acc (f q)) n) (f n) =
      true at h
    rcases (orB_iff _ _).1 h with h1 | h1
    · obtain ⟨q, hq, h2⟩ := anyRec_iff f n h1
      exact ⟨q, by omega, h2⟩
    · exact ⟨n, by omega, h1⟩

theorem hintLoop (F : ℕ → ℕ → Bool) (m sh : ℕ) : ∀ k, k ≤ m → ∀ H,
    Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun k ih H => andB (F (Nat.sub m (Nat.succ k)) H) (ih (Nat.shiftRight H sh))) k H = true →
    ∀ t < k, F (m - k + t) (H >>> (sh * t)) = true
  | 0, _, _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | k + 1, hk, H, h, t, ht => by
    change andB (F (Nat.sub m (Nat.succ k)) H) (Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun k ih H => andB (F (Nat.sub m (Nat.succ k)) H) (ih (Nat.shiftRight H sh))) k
        (Nat.shiftRight H sh)) = true at h
    rw [andB_iff] at h
    obtain ⟨h1, h2⟩ := h
    rcases t with _ | t
    · simpa using h1
    · have := hintLoop F m sh k (by omega) _ h2 t (by omega)
      have e1 : m - k + t = m - (k + 1) + (t + 1) := by omega
      have e2 : Nat.shiftRight H sh >>> (sh * t) = H >>> (sh * (t + 1)) := by
        change H >>> sh >>> (sh * t) = _
        rw [← Nat.shiftRight_add]
        congr 1
        ring
      rw [e1, e2] at this
      exact this

theorem two_pow_eight_mul (k : ℕ) : 2 ^ (8 * k) = 256 ^ k := by
  rw [pow_mul]
  norm_num

theorem wLet_eq (W i : ℕ) : wLet W i = W / 256 ^ i % 256 := by
  change W >>> (8 * i) &&& 255 = _
  have h : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, two_pow_eight_mul]

theorem wLet_lt (W i : ℕ) : wLet W i < 256 := by
  rw [wLet_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem byte_add_high {W B i n : ℕ} (hi : i < n) :
    (W + B * 256 ^ n) / 256 ^ i % 256 = W / 256 ^ i % 256 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have e : B * 256 ^ (i + d + 1) = 256 ^ i * (256 * (B * 256 ^ d)) := by ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem byte_concat {A B p i : ℕ} (hA : A < 256 ^ p) :
    (A + B * 256 ^ p) / 256 ^ i % 256 =
      if i < p then A / 256 ^ i % 256 else B / 256 ^ (i - p) % 256 := by
  split_ifs with hi
  · exact byte_add_high hi
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hi)
    have e : (A + B * 256 ^ p) / 256 ^ (p + j) = B / 256 ^ j := by
      rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm B, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt hA, Nat.zero_add]
    rw [e, Nat.add_sub_cancel_left]

theorem land_mask (x k : ℕ) : Nat.land x (Nat.sub (Nat.shiftLeft 1 k) 1) = x % 2 ^ k := by
  change x &&& ((1 <<< k) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]

theorem land1 (x : ℕ) : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x

theorem shr_eq (x k : ℕ) : Nat.shiftRight x k = x / 2 ^ k := Nat.shiftRight_eq_div_pow x k

theorem lor_shl {a b k : ℕ} (ha : a < 2 ^ k) : Nat.lor a (Nat.shiftLeft b k) = a + b * 2 ^ k := by
  change a ||| b <<< k = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

section Values

variable {G : Type*} [Group G] (gen : ℕ → G)

@[expose] def lv (l : ℕ) : G :=
  if l = 255 then 1 else if l % 2 = 0 then gen (l / 2) else (gen (l / 2))⁻¹

@[expose] noncomputable def bv (W n : ℕ) : G :=
  ((List.range n).map fun i => lv gen (wLet W i)).prod

theorem bv_succ (W n : ℕ) : bv gen W (n + 1) = bv gen W n * lv gen (wLet W n) := by
  unfold bv
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

theorem bv_zero (W : ℕ) : bv gen W 0 = 1 := rfl

theorem bv_eq (W n : ℕ) :
    bv gen W n = ((List.range n).map fun i => lv gen (W / 256 ^ i % 256)).prod := by
  simp only [bv, wLet_eq]

theorem bv_concat {A B p q : ℕ} (hA : A < 256 ^ p) :
    bv gen (A + B * 256 ^ p) (p + q) = bv gen A p * bv gen B q := by
  rw [bv_eq, bv_eq, bv_eq, List.range_add, List.map_append, List.prod_append, List.map_map]
  congr 2
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [byte_concat hA]
    simp only [hi, ↓reduceIte]
  · apply List.map_congr_left
    intro j _
    have hj : ¬p + j < p := by omega
    simp only [Function.comp_apply, byte_concat hA, hj, ↓reduceIte, Nat.add_sub_cancel_left]

theorem bv_one {c : ℕ} (hc : c < 256) : bv gen c 1 = lv gen c := by
  simp [bv_eq, Nat.mod_eq_of_lt hc]

set_option maxRecDepth 100000 in
theorem xor_one_cases : ∀ c < 256, c ^^^ 1 = if c % 2 = 0 then c + 1 else c - 1 := by decide

theorem lv_xor_one {c : ℕ} (hc : c < 254) : lv gen (c ^^^ 1) = (lv gen c)⁻¹ := by
  rw [xor_one_cases c (by omega)]
  unfold lv
  split_ifs <;> first | omega | (simp_all; congr 1; omega)

theorem lv_255 : lv gen 255 = 1 := by simp [lv]

end Values

theorem inv16_lt (INV c : ℕ) : inv16 INV c < 65536 := by
  change (INV >>> (c <<< 4)) &&& (2 ^ 16 - 1) < 65536
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem invOK_spec {INV INV8 L : ℕ} (h : invOK INV INV8 L = true) :
    L < 255 ∧ L % 2 = 0 ∧ ∀ c < 256,
      (c < L → inv16 INV c = c ^^^ 1 ∧ wLet INV8 c = c ^^^ 1) ∧
      (L ≤ c → c = 255 → inv16 INV c = 255) ∧
      (L ≤ c → c ≠ 255 → inv16 INV c = 65535) := by
  unfold invOK at h
  obtain ⟨hL, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hL2, h⟩ := (andB_iff _ _).1 h
  obtain ⟨-, h⟩ := (andB_iff _ _).1 h
  obtain ⟨-, hloop⟩ := (andB_iff _ _).1 h
  rw [Nat.blt_eq] at hL
  rw [Nat.beq_eq, land1] at hL2
  refine ⟨hL, hL2, fun c hc => ?_⟩
  have hc' := (allRec2_iff (fun c => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (inv16 INV c) (nat_lit 65535)) (Nat.beq (wLet INV8 c) (nat_lit 254)))
        (andB (Nat.beq (inv16 INV c) (nat_lit 255)) (Nat.beq (wLet INV8 c) (nat_lit 255)))
        (Nat.beq c (nat_lit 255)))
      (andB (Nat.beq (inv16 INV c) (Nat.xor c (nat_lit 1)))
        (Nat.beq (wLet INV8 c) (Nat.xor c (nat_lit 1))))
      (Nat.blt c L)) (nat_lit 256)).1 hloop c hc
  rw [brec_eq, brec_eq] at hc'
  refine ⟨fun hcL => ?_, fun hcL hc255 => ?_, fun hcL hc255 => ?_⟩
  · rw [ite_eq_left (by simpa using hcL)] at hc'
    simp only [andB_iff, Nat.beq_eq] at hc'
    exact hc'
  · rw [ite_eq_right (by simpa using hcL), ite_eq_left (by simpa using hc255)] at hc'
    simp only [andB_iff, Nat.beq_eq] at hc'
    exact hc'.1
  · rw [ite_eq_right (by simpa using hcL), ite_eq_right (by simpa using hc255)] at hc'
    simp only [andB_iff, Nat.beq_eq] at hc'
    exact hc'.1

theorem lettersOK_spec {INV INV8 L W n : ℕ} (hinv : invOK INV INV8 L = true)
    (h : lettersOK INV W n = true) : ∀ i < n, wLet W i < L ∨ wLet W i = 255 := by
  intro i hi
  have h1 := (allRec_iff _ n).1 h i hi
  rw [Nat.blt_eq] at h1
  obtain ⟨-, -, hc⟩ := invOK_spec hinv
  obtain ⟨-, -, h3⟩ := hc _ (wLet_lt W i)
  rcases Nat.lt_or_ge (wLet W i) L with h' | h'
  · exact Or.inl h'
  · by_cases h'' : wLet W i = 255
    · exact Or.inr h''
    · rw [h3 h' h''] at h1
      exact absurd h1 (lt_irrefl _)

section Free

variable {G : Type*} [Group G] (gen : ℕ → G)

@[expose] def enc : List ℕ → ℕ
  | [] => 0
  | x :: l => enc l * 256 + (x + 1)

@[expose] noncomputable def lval (l : List ℕ) : G := (l.reverse.map (lv gen)).prod

theorem lval_cons (x : ℕ) (l : List ℕ) : lval gen (x :: l) = lval gen l * lv gen x := by
  simp [lval, List.reverse_cons, List.map_append, List.prod_append]

theorem freeRed_spec {INV INV8 L W n : ℕ} (hinv : invOK INV INV8 L = true)
    (hlet : lettersOK INV W n = true) : ∀ i ≤ n, ∃ l : List ℕ,
      freeRed INV8 W i = enc l ∧ (∀ x ∈ l, x < L) ∧ lval gen l = bv gen W i
  | 0, _ => ⟨[], rfl, by simp, rfl⟩
  | i + 1, hi => by
    obtain ⟨l, hl, hlL, hlv⟩ := freeRed_spec hinv hlet i (by omega)
    obtain ⟨hL, -, hc⟩ := invOK_spec hinv
    have hx := lettersOK_spec hinv hlet i (by omega)
    have e : freeRed INV8 W (i + 1) = Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ)
        (Nat.add (Nat.mul (freeRed INV8 W i) 256) (Nat.succ (wLet W i)))
        (Nat.shiftRight (freeRed INV8 W i) 8)
        (andB (Nat.blt 0 (freeRed INV8 W i))
          (Nat.beq (Nat.land (freeRed INV8 W i) 255) (Nat.succ (wLet INV8 (wLet W i))))))
      (freeRed INV8 W i) (Nat.beq (wLet W i) 255) := rfl
    rw [e, brec_eq, bv_succ, ← hlv, hl]
    split_ifs with h255
    · rw [Nat.beq_eq] at h255
      rw [h255, lv_255, mul_one]
      exact ⟨l, rfl, hlL, rfl⟩
    · rw [Nat.beq_eq] at h255
      have hxL : wLet W i < L := hx.resolve_right h255
      obtain ⟨-, h8⟩ := (hc _ (wLet_lt W i)).1 hxL
      rw [h8, brec_eq]
      have hpush : ∃ l' : List ℕ, Nat.add (Nat.mul (enc l) 256) (Nat.succ (wLet W i)) = enc l' ∧
          (∀ x ∈ l', x < L) ∧ lval gen l' = lval gen l * lv gen (wLet W i) := by
        refine ⟨wLet W i :: l, rfl, ?_, lval_cons gen _ _⟩
        intro x hx'
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact hxL
        · exact hlL x hx'
      split_ifs with hcond
      · simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at hcond
        obtain ⟨hpos, htop⟩ := hcond
        rcases l with _ | ⟨y, l'⟩
        · exact absurd hpos (by simp [enc])
        · have hy := hlL y (by simp)
          have e1 : Nat.land (enc (y :: l')) 255 = y + 1 := by
            change (enc l' * 256 + (y + 1)) &&& (2 ^ 8 - 1) = _
            rw [Nat.and_two_pow_sub_one_eq_mod]
            omega
          rw [e1] at htop
          have hyx : y = wLet W i ^^^ 1 := by
            change y + 1 = Nat.xor (wLet W i) 1 + 1 at htop
            exact Nat.succ.inj htop
          refine ⟨l', ?_, fun x hx' => hlL x (by simp [hx']), ?_⟩
          · change (enc l' * 256 + (y + 1)) >>> 8 = enc l'
            rw [Nat.shiftRight_eq_div_pow]
            omega
          · rw [lval_cons, hyx, lv_xor_one gen (by omega), mul_assoc, inv_mul_cancel, mul_one]
      · exact hpush

theorem freeRed_zero {INV INV8 L W n : ℕ} (hinv : invOK INV INV8 L = true)
    (hlet : lettersOK INV W n = true) (h0 : freeRed INV8 W n = 0) : bv gen W n = 1 := by
  obtain ⟨l, hl, -, hv⟩ := freeRed_spec gen hinv hlet n le_rfl
  rw [← hv]
  rcases l with _ | ⟨y, l'⟩
  · rfl
  · rw [h0] at hl
    simp [enc] at hl

theorem strip_spec (W : ℕ) : ∀ i, (strip W i).1 < 256 ^ (strip W i).2 ∧
    bv gen (strip W i).1 (strip W i).2 = bv gen W i
  | 0 => ⟨by simp [strip], rfl⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := strip_spec W i
    have e : strip W (i + 1) = Bool.rec (motive := fun _ => ℕ × ℕ)
        (Nat.lor (strip W i).1 (Nat.shiftLeft (wLet W i) (Nat.mul 8 (strip W i).2)),
          Nat.succ (strip W i).2)
        ((strip W i).1, (strip W i).2) (Nat.beq (wLet W i) 255) := rfl
    rw [e, brec_eq, bv_succ, ← h2]
    split_ifs with h255
    · rw [Nat.beq_eq] at h255
      rw [h255, lv_255, mul_one]
      exact ⟨h1, rfl⟩
    · have hlt : (strip W i).1 < 2 ^ (Nat.mul 8 (strip W i).2) := by
        change _ < 2 ^ (8 * _)
        rwa [two_pow_eight_mul]
      dsimp only
      rw [lor_shl hlt]
      change (strip W i).1 + wLet W i * 2 ^ (8 * (strip W i).2) < 256 ^ ((strip W i).2 + 1) ∧
        bv gen ((strip W i).1 + wLet W i * 2 ^ (8 * (strip W i).2)) ((strip W i).2 + 1) = _
      rw [two_pow_eight_mul, bv_concat gen h1, bv_one gen (wLet_lt W i)]
      refine ⟨?_, rfl⟩
      have := wLet_lt W i
      calc (strip W i).1 + wLet W i * 256 ^ (strip W i).2
          < 256 ^ (strip W i).2 + wLet W i * 256 ^ (strip W i).2 := by omega
        _ = (wLet W i + 1) * 256 ^ (strip W i).2 := by ring
        _ ≤ 256 * 256 ^ (strip W i).2 := Nat.mul_le_mul_right _ (by omega)
        _ = 256 ^ ((strip W i).2 + 1) := by ring

theorem rot_eq {r n s : ℕ} (hr : r < 256 ^ n) (hs : s ≤ n) :
    rot r n s = r / 256 ^ s + r % 256 ^ s * 256 ^ (n - s) := by
  unfold rot
  rw [land_mask, shr_eq]
  change r / 2 ^ (8 * s) ||| (r % 2 ^ (8 * s)) <<< (8 * (n - s)) = _
  have hA : r / 2 ^ (8 * s) < 2 ^ (8 * (n - s)) := by
    rw [two_pow_eight_mul, two_pow_eight_mul, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      Nat.sub_add_cancel hs]
    exact hr
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hA, Nat.shiftLeft_eq, two_pow_eight_mul,
    two_pow_eight_mul]
  ring

theorem bv_rot {r n s : ℕ} (hr : r < 256 ^ n) (hs : s < n) (h1 : bv gen r n = 1) :
    bv gen (rot r n s) n = 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = s + d := ⟨n - s, by omega⟩
  rw [rot_eq hr (by omega), Nat.add_sub_cancel_left]
  have hA : r / 256 ^ s < 256 ^ d := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm d s]
    exact hr
  have hB : r % 256 ^ s < 256 ^ s := Nat.mod_lt _ (by positivity)
  have hr' : r = r % 256 ^ s + r / 256 ^ s * 256 ^ s := by
    rw [Nat.mul_comm]
    exact (Nat.mod_add_div r _).symm
  rw [hr', bv_concat gen hB] at h1
  rw [Nat.add_comm s d, bv_concat gen hA]
  exact mul_eq_one_comm.mp h1

theorem wRel_sound {INV INV8 L W n r m : ℕ} (hinv : invOK INV INV8 L = true)
    (h : wRel INV INV8 W n r m = true) (hr : r < 2 ^ (8 * m)) (h1 : bv gen r m = 1) :
    bv gen W n = 1 := by
  unfold wRel at h
  simp only [andB_iff, orB_iff, Nat.beq_eq] at h
  obtain ⟨hlet, -, hfr | hrot⟩ := h
  · exact freeRed_zero gen hinv hlet hfr
  · unfold isRelRot at hrot
    change andB (Nat.beq (strip W n).2 m) (isRot r m (strip W n).1) = true at hrot
    simp only [andB_iff, Nat.beq_eq] at hrot
    obtain ⟨hk, hrot⟩ := hrot
    obtain ⟨s, hs, hseq⟩ := anyRec_iff _ m hrot
    rw [Nat.beq_eq] at hseq
    rw [← (strip_spec gen W n).2, hk, ← hseq]
    rw [two_pow_eight_mul] at hr
    exact bv_rot gen hr hs h1

theorem wSub_sound {INV W n s m : ℕ} (h : wSub INV W n s m = true) :
    bv gen W n = bv gen s m := by
  unfold wSub at h
  change andB (lettersOK INV W n) (andB (sentOK W n)
    (andB (Nat.beq (strip W n).1 s) (Nat.beq (strip W n).2 m))) = true at h
  simp only [andB_iff, Nat.beq_eq] at h
  obtain ⟨-, -, h⟩ := h
  rw [← (strip_spec gen W n).2, h.1, h.2]

end Free

end CFSG.Certificates.LceP

end
