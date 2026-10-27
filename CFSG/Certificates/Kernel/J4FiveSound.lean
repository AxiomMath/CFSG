module

public import Certificates.Data.Kernel.J4Five
public import CFSG.Certificates.Kernel.J4CountSound
public import CFSG.Certificates.Kernel.J4Q.RepQT2B

public section

namespace CFSG.KC.J4Five

open CFSG.KC.J4Count CFSG.KC.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native

theorem orB_eq_or (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem allN_spec {f : Nat → Bool} : ∀ {n : Nat}, allN n f = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    change andB (f n) (allN n f) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact allN_spec h.2 i hi
    · exact h.1

theorem all64_spec {hi : Nat} {f : Nat → Bool} (h : all64 hi f = true) :
    ∀ i < 64 * hi, f i = true := by
  have h' : allN hi (fun h => allN 64 (fun l => f (64 * h + l))) = true := h
  intro i hlt
  have e := Nat.div_add_mod i 64
  have h1 := allN_spec (allN_spec h' (i / 64) (by omega)) (i % 64) (Nat.mod_lt _ (by norm_num))
  rwa [e] at h1

theorem imgN_succ (f : Nat → Nat) (m n : Nat) :
    imgN f m (n + 1) = imgN f m n ||| (if m.testBit n then 1 <<< f n else 0) := by
  change Nat.lor (imgN f m n) (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 (f n))
    (Nat.testBit m n)) = _
  cases m.testBit n <;> rfl

theorem testBit_one_shiftLeft (k y : Nat) : (1 <<< k).testBit y = decide (k = y) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_imgN (f : Nat → Nat) (m y : Nat) :
    ∀ n, (imgN f m n).testBit y = true ↔ ∃ i < n, m.testBit i = true ∧ f i = y
  | 0 => by
    change (0 : Nat).testBit y = true ↔ _
    simp
  | n + 1 => by
    rw [imgN_succ, Nat.testBit_or, Bool.or_eq_true, testBit_imgN f m y n]
    by_cases hb : m.testBit n = true
    · simp only [hb, ↓reduceIte, testBit_one_shiftLeft, decide_eq_true_eq]
      constructor
      · rintro (⟨i, hi, h1, h2⟩ | h)
        · exact ⟨i, by omega, h1, h2⟩
        · exact ⟨n, by omega, hb, h⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inl ⟨i, hi, h1, h2⟩
        · exact Or.inr h2
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, or_false]
      constructor
      · rintro ⟨i, hi, h1, h2⟩
        exact ⟨i, by omega, h1, h2⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, h1, h2⟩
        · exact absurd h1 hb

theorem testBit_imgF (f : Nat → Nat) (m y : Nat) :
    (imgF f m).testBit y = true ↔ ∃ i < 24, m.testBit i = true ∧ f i = y :=
  testBit_imgN f m y 24

theorem imgF_congr {f g : Nat → Nat} (h : ∀ i < 24, f i = g i) (m : Nat) : imgF f m = imgF g m := by
  apply Nat.eq_of_testBit_eq
  intro y
  apply Bool.eq_iff_iff.2
  rw [testBit_imgF, testBit_imgF]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, hi, h1, by rw [← h i hi]; exact h2⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, hi, h1, by rw [h i hi]; exact h2⟩

theorem imgF_zero (f : Nat → Nat) : imgF f 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro y
  apply Bool.eq_iff_iff.2
  rw [testBit_imgF]
  simp

@[expose] def InjS (f : Nat → Nat) : Prop := ∀ i < 24, ∀ j < 24, f i = f j → i = j

theorem testBit_imgF_app {f : Nat → Nat} (hf : InjS f) {i : Nat} (hi : i < 24) (c : Nat) :
    (imgF f c).testBit (f i) = c.testBit i := by
  apply Bool.eq_iff_iff.2
  rw [testBit_imgF]
  constructor
  · rintro ⟨j, hj, h1, h2⟩
    rwa [hf j hj i hi h2] at h1
  · intro h
    exact ⟨i, hi, h, rfl⟩

theorem testBit_imgF_out {f : Nat → Nat} {y : Nat} (hy : ¬ ∃ i < 24, f i = y) (c : Nat) :
    (imgF f c).testBit y = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [testBit_imgF] at h
  obtain ⟨i, hi, -, h2⟩ := h
  exact hy ⟨i, hi, h2⟩

theorem imgF_xor {f : Nat → Nat} (hf : InjS f) (a b : Nat) :
    imgF f (a ^^^ b) = imgF f a ^^^ imgF f b := by
  apply Nat.eq_of_testBit_eq
  intro y
  rw [Nat.testBit_xor]
  by_cases hy : ∃ i < 24, f i = y
  · obtain ⟨i, hi, rfl⟩ := hy
    rw [testBit_imgF_app hf hi, testBit_imgF_app hf hi, testBit_imgF_app hf hi, Nat.testBit_xor]
  · rw [testBit_imgF_out hy, testBit_imgF_out hy, testBit_imgF_out hy]
    rfl

theorem imgF_comp (f : Nat → Nat) {g : Nat → Nat} (hg : ∀ i < 24, g i < 24) (m : Nat) :
    imgF f (imgF g m) = imgF (fun i => f (g i)) m := by
  apply Nat.eq_of_testBit_eq
  intro y
  apply Bool.eq_iff_iff.2
  rw [testBit_imgF, testBit_imgF]
  constructor
  · rintro ⟨j, hj, h1, h2⟩
    rw [testBit_imgF] at h1
    obtain ⟨i, hi, h3, rfl⟩ := h1
    exact ⟨i, hi, h3, h2⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨g i, hg i hi, (testBit_imgF g m (g i)).2 ⟨i, hi, h1, rfl⟩, h2⟩

theorem imgF_id {f : Nat → Nat} (hf : ∀ i < 24, f i = i) {m : Nat} (hm : m < 2 ^ 24) :
    imgF f m = m := by
  apply Nat.eq_of_testBit_eq
  intro y
  apply Bool.eq_iff_iff.2
  rw [testBit_imgF]
  constructor
  · rintro ⟨i, hi, h1, rfl⟩
    rwa [hf i hi]
  · intro h
    have hy : y < 24 := by
      by_contra hy
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num)
        (by omega)))] at h
      exact Bool.false_ne_true h
    exact ⟨y, hy, h, hf y hy⟩

theorem imgF_lt {f : Nat → Nat} (hf : ∀ i < 24, f i < 24) (m : Nat) : imgF f m < 2 ^ 24 := by
  apply Nat.lt_pow_two_of_testBit
  intro y hy
  rw [Bool.eq_false_iff]
  intro h
  rw [testBit_imgF] at h
  obtain ⟨i, hi, -, rfl⟩ := h
  have := hf i hi
  omega

theorem shiftRight_and_one (m i : Nat) : (m >>> i) &&& 1 = if m.testBit i then 1 else 0 := by
  rw [Nat.and_one_is_mod, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ i) with h | h <;> simp [h]

theorem pcN_eq_card (m : Nat) :
    ∀ n, pcN m n = ((Finset.range n).filter fun i => m.testBit i = true).card
  | 0 => rfl
  | n + 1 => by
    change Nat.add (pcN m n) (Nat.land (Nat.shiftRight m n) 1) = _
    change pcN m n + ((m >>> n) &&& 1) = _
    rw [pcN_eq_card m n, shiftRight_and_one, Finset.range_add_one, Finset.filter_insert]
    by_cases hb : m.testBit n = true
    · rw [if_pos hb, if_pos hb, Finset.card_insert_of_notMem (by simp)]
    · rw [if_neg hb, if_neg hb, Nat.add_zero]

theorem bits_imgF {f : Nat → Nat} (hf : ∀ i < 24, f i < 24) (m : Nat) :
    (Finset.range 24).filter (fun y => (imgF f m).testBit y = true) =
      ((Finset.range 24).filter fun i => m.testBit i = true).image f := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, testBit_imgF]
  constructor
  · rintro ⟨-, i, hi, h1, h2⟩
    exact ⟨i, ⟨hi, h1⟩, h2⟩
  · rintro ⟨i, ⟨hi, h1⟩, rfl⟩
    exact ⟨hf i hi, i, hi, h1, rfl⟩

theorem pc_imgF {f : Nat → Nat} (hf : ∀ i < 24, f i < 24) (hi : InjS f) (m : Nat) :
    pcN (imgF f m) 24 = pcN m 24 := by
  rw [pcN_eq_card, pcN_eq_card, bits_imgF hf, Finset.card_image_of_injOn]
  intro a ha b hb e
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
  exact hi a ha.1 b hb.1 e

theorem combo_zero : ∀ B : List Nat, combo B 0 = 0
  | [] => rfl
  | b :: B => by
    rw [combo_cons]
    simp [combo_zero B]

theorem combo_xor : ∀ (B : List Nat) (s t : Nat), combo B s ^^^ combo B t = combo B (s ^^^ t)
  | [], _, _ => by simp [combo_nil]
  | b :: B, s, t => by
    rw [combo_cons, combo_cons, combo_cons, Nat.testBit_xor, Nat.shiftRight_xor_distrib,
      ← combo_xor B]
    cases s.testBit 0 <;> cases t.testBit 0 <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.xor_true, Bool.not_true,
        Bool.not_false, Nat.zero_xor, Nat.xor_zero] <;> ac_nf <;> simp [Nat.xor_self]

variable {B P : List Nat}

theorem inC_iff (hlen : P.length = B.length)
    (hinv : ∀ m < 2 ^ B.length, decode P (combo B m) = m) (a : Nat) :
    inC B P a = true ↔ ∃ m < 2 ^ B.length, combo B m = a := by
  rw [mem_image_iff hlen hinv]
  refine ⟨Nat.eq_of_beq_eq_true, fun h => ?_⟩
  change Nat.beq (combo B (decode P a)) a = true
  rw [h]
  exact Nat.beq_refl a

theorem inC_zero (hlen : P.length = B.length)
    (hinv : ∀ m < 2 ^ B.length, decode P (combo B m) = m) : inC B P 0 = true :=
  (inC_iff hlen hinv 0).2 ⟨0, Nat.two_pow_pos _, combo_zero B⟩

theorem inC_xor (hlen : P.length = B.length)
    (hinv : ∀ m < 2 ^ B.length, decode P (combo B m) = m) {a b : Nat}
    (ha : inC B P a = true) (hb : inC B P b = true) : inC B P (a ^^^ b) = true := by
  obtain ⟨s, hs, rfl⟩ := (inC_iff hlen hinv a).1 ha
  obtain ⟨t, ht, rfl⟩ := (inC_iff hlen hinv b).1 hb
  exact (inC_iff hlen hinv _).2 ⟨s ^^^ t, Nat.xor_lt_two_pow hs ht, (combo_xor B s t).symm⟩

theorem genOK_mem {f : Nat → Nat} : ∀ {L : List Nat}, (List.rec (motive := fun _ => Bool) true
    (fun b _ ih => andB (inC B P (imgF f b)) ih) L) = true → ∀ b ∈ L, inC B P (imgF f b) = true
  | [], _, b, hb => absurd hb List.not_mem_nil
  | x :: L, h, b, hb => by
    change andB (inC B P (imgF f x)) _ = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact genOK_mem h.2 b hb

theorem genOK_rec_congr {f g : Nat → Nat} (h : ∀ i < 24, f i = g i) : ∀ L : List Nat,
    (List.rec (motive := fun _ => Bool) true (fun b _ ih => andB (inC B P (imgF f b)) ih) L) =
      (List.rec (motive := fun _ => Bool) true (fun b _ ih => andB (inC B P (imgF g b)) ih) L)
  | [] => rfl
  | b :: L => by
    change andB (inC B P (imgF f b)) _ = andB (inC B P (imgF g b)) _
    rw [imgF_congr h, genOK_rec_congr h L]

theorem genOK_congr {f g : Nat → Nat} (h : ∀ i < 24, f i = g i) : genOK B P f = genOK B P g :=
  genOK_rec_congr h B

theorem inC_img (hlen : P.length = B.length)
    (hinv : ∀ m < 2 ^ B.length, decode P (combo B m) = m) {f : Nat → Nat} (hf : InjS f)
    (hg : genOK B P f = true) {a : Nat} (ha : inC B P a = true) : inC B P (imgF f a) = true := by
  obtain ⟨m, -, rfl⟩ := (inC_iff hlen hinv a).1 ha
  refine combo_mem (S := fun a => inC B P (imgF f a) = true) ?_ ?_ ?_ m
  · rw [imgF_zero]
    exact inC_zero hlen hinv
  · intro a b ha hb
    rw [imgF_xor hf]
    exact inC_xor hlen hinv ha hb
  · exact genOK_mem hg

theorem invOK_spec (h : invOK B P = true) : ∀ s < 4096, decode P (combo B s) = s := by
  intro s hs
  exact Nat.eq_of_beq_eq_true (all64_spec h s (by omega))

theorem isOct5_rec {z : List Nat} {Fm Tm a : Nat} : ∀ {n : Nat},
    (Nat.rec (motive := fun _ => Bool) false
      (fun j acc => orB (Nat.beq a (Nat.lor Fm (imgF (zPow z j) Tm))) acc) n) = true →
    ∃ j < n, a = Fm ||| imgF (zPow z j) Tm
  | 0, h => absurd h Bool.false_ne_true
  | n + 1, h => by
    change orB (Nat.beq a (Nat.lor Fm (imgF (zPow z n) Tm))) _ = true at h
    rw [orB_eq_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨n, by omega, Nat.eq_of_beq_eq_true h⟩
    · obtain ⟨j, hj, e⟩ := isOct5_rec h
      exact ⟨j, by omega, e⟩

theorem octOK_spec {z : List Nat} {Fm Tm : Nat} (h : octOK B z Fm Tm = true) :
    ∀ s < 4096, pcN (combo B s) 24 = 8 → combo B s &&& Fm = Fm →
      ∃ j < 5, combo B s = Fm ||| imgF (zPow z j) Tm := by
  intro s hs h8 hF
  have k := all64_spec h s (by omega)
  beta_reduce at k
  rw [strictB_eq] at k
  rw [orB_eq_or, Bool.or_eq_true, notB_eq, andB_eq, h8, Nat.beq_refl] at k
  have hF' : Nat.beq (Nat.land (combo B s) Fm) Fm = true := by
    change Nat.beq (combo B s &&& Fm) Fm = true
    rw [hF]
    exact Nat.beq_refl Fm
  rw [hF'] at k
  rcases k with k | k
  · exact absurd k (by decide)
  · exact isOct5_rec k

theorem testBit_maskL (y : Nat) : ∀ L : List Nat, (maskL L).testBit y = true ↔ y ∈ L
  | [] => by
    change (0 : Nat).testBit y = true ↔ _
    simp
  | x :: L => by
    change (1 <<< x ||| maskL L).testBit y = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_one_shiftLeft, testBit_maskL y L,
      decide_eq_true_eq, List.mem_cons, eq_comm]

theorem getN_getD (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getN_getD d l i

theorem getN_map (f : Nat → Nat) : ∀ {l : List Nat} {i : Nat}, i < l.length →
    getN 0 (l.map f) i = f (getN 0 l i)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => getN_map f (l := l) (by simp at h; omega)

theorem zPow_succ (z : List Nat) (k x : Nat) : zPow z (k + 1) x = getN 0 z (zPow z k x) := rfl

theorem zPow_zero (z : List Nat) (x : Nat) : zPow z 0 x = x := rfl

theorem crdOK_spec {z crd L : List Nat} (h : crdOK z crd L = true) :
    ∀ x < 24, getN 0 crd x % 8 < 8 ∧
      zPow z (getN 0 crd x / 8) (getN 0 L (getN 0 crd x % 8)) = x := by
  intro x hx
  have k := allN_spec h x hx
  change andB (Nat.blt (getN 0 crd x % 8) 8)
    (Nat.beq (zPow z (getN 0 crd x / 8) (getN 0 L (getN 0 crd x % 8))) x) = true at k
  rw [andB_eq, Bool.and_eq_true] at k
  exact ⟨Nat.le_of_ble_eq_true k.1, Nat.eq_of_beq_eq_true k.2⟩

theorem fixOK_spec {z Fl : List Nat} (h : fixOK z Fl = true) :
    ∀ x < 24, getN 0 z x < 24 ∧ (getN 0 z x = x ↔ x ∈ Fl) := by
  intro x hx
  have k := allN_spec h x hx
  change andB (Nat.blt (getN 0 z x) 24) (Bool.rec (motive := fun _ => Bool) (notB (List.elem x Fl))
    (List.elem x Fl) (Nat.beq (getN 0 z x) x)) = true at k
  rw [andB_eq, Bool.and_eq_true] at k
  refine ⟨Nat.le_of_ble_eq_true k.1, ?_⟩
  have k2 := k.2
  have he : List.elem x Fl = true ↔ x ∈ Fl := List.elem_iff
  cases hb : Nat.beq (getN 0 z x) x
  · rw [hb] at k2
    change notB (List.elem x Fl) = true at k2
    rw [notB_eq, Bool.not_eq_true'] at k2
    refine ⟨fun e => ?_, fun e => ?_⟩
    · rw [e, Nat.beq_refl] at hb
      exact absurd hb (by decide)
    · rw [he.2 e] at k2
      exact absurd k2 (by decide)
  · rw [hb] at k2
    change List.elem x Fl = true at k2
    exact ⟨fun _ => he.1 k2, fun _ => Nat.eq_of_beq_eq_true hb⟩

theorem sqOK_spec {T0 T1 T2 Y Z : List Nat} (h : sqOK T0 T1 T2 Y Z = true) :
    ∀ x < 24, getN 0 Y (getN 0 T2 x) = getN 0 T0 (getN 0 T1 x) ∧
      getN 0 Z x = getN 0 Y (getN 0 Y x) := by
  intro x hx
  have k := allN_spec h x hx
  change andB (Nat.beq (getN 0 Y (getN 0 T2 x)) (getN 0 T0 (getN 0 T1 x)))
    (Nat.beq (getN 0 Z x) (getN 0 Y (getN 0 Y x))) = true at k
  rw [andB_eq, Bool.and_eq_true] at k
  exact ⟨Nat.eq_of_beq_eq_true k.1, Nat.eq_of_beq_eq_true k.2⟩

theorem mem_perms4 {L : List Nat} {a b c d : Nat} (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L)
    (hd : d ∈ L) (hab : b ≠ a) (hac : c ≠ a) (had : d ≠ a) (hbc : c ≠ b) (hbd : d ≠ b)
    (hcd : d ≠ c) : [a, b, c, d] ∈ perms4 L := by
  simp only [perms4, List.mem_flatMap, List.mem_filter, List.mem_map, bne_iff_ne, ne_eq]
  exact ⟨a, ha, b, ⟨hb, hab⟩, c, ⟨⟨hc, hac⟩, hbc⟩, d, ⟨⟨⟨hd, had⟩, hbd⟩, hcd⟩, rfl⟩

theorem mem_perms4_of {L l : List Nat} (hl : l.length = 4) (hnd : l.Nodup) (hL : ∀ x ∈ l, x ∈ L) :
    l ∈ perms4 L := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, l = [a, b, c, d] := by
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hl
    exact ⟨a, b, c, d, rfl⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  exact mem_perms4 (hL a (by simp)) (hL b (by simp)) (hL c (by simp)) (hL d (by simp))
    (Ne.symm hnd.1.1) (Ne.symm hnd.1.2.1) (Ne.symm hnd.1.2.2) (Ne.symm hnd.2.1.1)
    (Ne.symm hnd.2.1.2) (Ne.symm hnd.2.2.1)

theorem mem_cands {Fl Tl a b : List Nat} (ha : a ∈ perms4 Fl) (hb : b ∈ perms4 Tl) :
    a ++ b ∈ cands Fl Tl := by
  simp only [cands, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, rfl⟩

theorem distB_inner {x : Nat} : ∀ {t : List Nat}, (List.rec (motive := fun _ => Bool) true
    (fun y _ ih2 => andB (notB (Nat.beq x y)) ih2) t) = true → x ∉ t
  | [], _ => List.not_mem_nil
  | y :: t, h => by
    change andB (notB (Nat.beq x y)) _ = true at h
    rw [andB_eq, Bool.and_eq_true, notB_eq, Bool.not_eq_true'] at h
    rw [List.mem_cons, not_or]
    exact ⟨fun e => by rw [e, Nat.beq_refl] at h; exact absurd h.1 (by decide),
      distB_inner h.2⟩

theorem distB_spec : ∀ {l : List Nat}, distB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: t, h => by
    change andB _ (distB t) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    exact List.nodup_cons.2 ⟨distB_inner h.1, distB_spec h.2⟩

theorem idxK_spec (v : Nat) : ∀ {P : List Nat}, idxK v P < P.length → getN 0 P (idxK v P) = v
  | [], h => absurd h (Nat.not_lt_zero _)
  | x :: P, h => by
    cases hb : Nat.beq v x
    · have e : idxK v (x :: P) = Nat.succ (idxK v P) := by
        change Bool.rec (motive := fun _ => Nat) _ _ (Nat.beq v x) = _
        rw [hb]
        rfl
      rw [e] at h ⊢
      exact idxK_spec v (by simpa using h)
    · have e : idxK v (x :: P) = 0 := by
        change Bool.rec (motive := fun _ => Nat) _ _ (Nat.beq v x) = _
        rw [hb]
      rw [e]
      exact (Nat.eq_of_beq_eq_true hb).symm

theorem eqvOK_spec {rm one : Nat} {P G PHI : List Nat} {n g : Nat} (hn : n ≤ P.length)
    (h : eqvOK rm one P G PHI n g = true) :
    ∀ l < g, ∀ i < n, ∃ j < n, vecJ rm (getN 0 P i) (getN one G l) = getN 0 P j ∧
      vecJ rm (getN 0 P (getN 0 PHI i)) (getN one G l) = getN 0 P (getN 0 PHI j) := by
  intro l hl i hi
  have k := allN_spec (allN_spec h l hl) i hi
  change strictB (idxK (vecJ rm (getN 0 P i) (getN one G l)) P) _ = true at k
  rw [strictB_eq, andB_eq, Bool.and_eq_true] at k
  have hj := Nat.le_of_ble_eq_true k.1
  exact ⟨_, hj, (idxK_spec _ (by omega)).symm, Nat.eq_of_beq_eq_true k.2⟩

section Vec

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem vwK_cons (mats invs : List Nat) (l : Int) (w : List Int) (x : Nat) :
    vwK rm one mats invs (l :: w) x = vwK rm one mats invs w (vecJ rm x (letJ one mats invs l)) :=
  strictN_eq _ _

theorem vwK_foldl (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {mats invs : Array (Array V2)}
    {ms is : List Nat}
    (hm : ∀ k, WfA (mats[k]?.getD (idRows ())) ∧ encR (mats[k]?.getD (idRows ())) = getN one ms k)
    (hi : ∀ k, WfA (invs[k]?.getD (idRows ())) ∧ encR (invs[k]?.getD (idRows ())) = getN one is k) :
    ∀ (w : List Int) (acc : Array V2), WfA acc → ∀ {v : V2}, v.wf = true →
      v2N (frApply (frTable (w.foldl (fun acc l => mulRows acc (if 0 < l then mats[l.toNat - 1]?.getD
        (idRows ()) else invs[(-l).toNat - 1]?.getD (idRows ()))) acc)) v) =
        vwK rm one ms is w (v2N (frApply (frTable acc) v))
  | [], acc, _, v, _ => rfl
  | l :: w, acc, hacc, v, hv => by
    obtain ⟨hl1, hl2⟩ := letter_enc hm hi l
    rw [List.foldl_cons, vwK_foldl hK hm hi w _ (wf_mulRows hacc hl1) hv, vwK_cons,
      vec_mulRows hacc hl1 hv, v2N_frApply hK hl1 (wf_frApply hacc v), hl2]

theorem frApply_idRows {v : V2} (hv : v.wf = true) : frApply (frTable (idRows ())) v = v := by
  apply (V2.toVec_inj (wf_frApply wf_idRows v) hv).1
  rw [CFSG.Sporadic.J4.frApply_toVec_eq_vecMul, CFSG.Sporadic.J4.rowsMatrix_idRows,
    Matrix.vecMul_one]

theorem vwK_wordRows (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {mats invs : Array (Array V2)}
    {ms is : List Nat}
    (hm : ∀ k, WfA (mats[k]?.getD (idRows ())) ∧ encR (mats[k]?.getD (idRows ())) = getN one ms k)
    (hi : ∀ k, WfA (invs[k]?.getD (idRows ())) ∧ encR (invs[k]?.getD (idRows ())) = getN one is k)
    (w : List Int) {v : V2} (hv : v.wf = true) :
    v2N (frApply (frTable (CFSG.Sporadic.J4.Native.wordRows mats invs w)) v) =
      vwK rm one ms is w (v2N v) := by
  have h := vwK_foldl hK hm hi w (idRows ()) wf_idRows hv
  rw [frApply_idRows hv] at h
  exact h

end Vec

section Perm

open Equiv

@[expose] def pf (g : Perm (Fin 24)) (i : Nat) : Nat := if h : i < 24 then (g ⟨i, h⟩ : Nat) else 0

theorem pf_fin (g : Perm (Fin 24)) (i : Fin 24) : pf g i = g i := by
  simp [pf, i.isLt]

theorem pf_fin' (g : Perm (Fin 24)) {i : Nat} (hi : i < 24) : pf g i = (g ⟨i, hi⟩ : Nat) := by
  simp [pf, hi]

theorem pf_lt (g : Perm (Fin 24)) {i : Nat} (hi : i < 24) : pf g i < 24 := by
  simp only [pf, hi, ↓reduceDIte]
  exact (g ⟨i, hi⟩).isLt

theorem pf_inj (g : Perm (Fin 24)) : InjS (pf g) := by
  intro i hi j hj e
  simp only [pf, hi, hj, ↓reduceDIte] at e
  exact congrArg Fin.val (g.injective (Fin.ext e))

theorem pf_mul (g h : Perm (Fin 24)) {i : Nat} (hi : i < 24) : pf (g * h) i = pf g (pf h i) := by
  simp only [pf, hi, ↓reduceDIte, (h ⟨i, hi⟩).isLt, Perm.mul_apply]

theorem pf_one {i : Nat} (hi : i < 24) : pf 1 i = i := by
  simp [pf, hi]

theorem pf_inv_pf (g : Perm (Fin 24)) {i : Nat} (hi : i < 24) : pf g⁻¹ (pf g i) = i := by
  rw [← pf_mul _ _ hi, inv_mul_cancel, pf_one hi]

theorem pf_pf_inv (g : Perm (Fin 24)) {i : Nat} (hi : i < 24) : pf g (pf g⁻¹ i) = i := by
  rw [← pf_mul _ _ hi, mul_inv_cancel, pf_one hi]

theorem pf_ext {g h : Perm (Fin 24)} (e : ∀ i < 24, pf g i = pf h i) : g = h := by
  ext i
  rw [← pf_fin, ← pf_fin]
  exact e i i.isLt

theorem genOK_of_mem {f : Nat → Nat} : ∀ {L : List Nat}, (∀ b ∈ L, inC B P (imgF f b) = true) →
    (List.rec (motive := fun _ => Bool) true (fun b _ ih => andB (inC B P (imgF f b)) ih) L) = true
  | [], _ => rfl
  | x :: L, h => by
    change andB (inC B P (imgF f x)) _ = true
    rw [andB_eq, Bool.and_eq_true]
    exact ⟨h x List.mem_cons_self, genOK_of_mem fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

theorem genOK_mul (hlen : P.length = B.length)
    (hinv : ∀ m < 2 ^ B.length, decode P (combo B m) = m) {g h : Perm (Fin 24)}
    (hg : genOK B P (pf g) = true) (hh : genOK B P (pf h) = true) :
    genOK B P (pf (g * h)) = true := by
  rw [genOK_congr (g := fun i => pf g (pf h i)) (fun i hi => pf_mul g h hi)]
  refine genOK_of_mem fun b hb => ?_
  rw [← imgF_comp (pf g) (fun i hi => pf_lt h hi)]
  exact inC_img hlen hinv (pf_inj g) hg (genOK_mem hh b hb)

theorem genOK_closure (hlen : P.length = B.length)
    (hinv : ∀ m < 2 ^ B.length, decode P (combo B m) = m) (hid : genOK B P (fun i => i) = true)
    {S : Set (Perm (Fin 24))} (hS : ∀ x ∈ S, genOK B P (pf x) = true) :
    ∀ g ∈ Subgroup.closure S, genOK B P (pf g) = true := by
  intro g hg
  have hg' : g ∈ (Subgroup.closure S).toSubmonoid := hg
  rw [Subgroup.closure_toSubmonoid_of_finite] at hg'
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx => exact hS x hx
  | one =>
    rw [genOK_congr (g := fun i => i) (fun i hi => pf_one hi)]
    exact hid
  | mul x y _ _ hx hy => exact genOK_mul hlen hinv hx hy

theorem getN_mem' : ∀ {l : List Nat} {i : Nat}, i < l.length → getN 0 l i ∈ l
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: l, i + 1, h => List.mem_cons_of_mem _ (getN_mem' (l := l) (by simp at h; omega))

variable {z crd Fl Tl : List Nat}

theorem zPow_pf {ξ : Perm (Fin 24)} (hz : ∀ i < 24, pf ξ i = getN 0 z i) :
    ∀ (k : Nat) {x : Nat}, x < 24 → zPow z k x = pf (ξ ^ k) x
  | 0, x, hx => by rw [zPow_zero, pow_zero, pf_one hx]
  | k + 1, x, hx => by
    rw [zPow_succ, zPow_pf hz k hx, ← hz _ (pf_lt _ hx), pow_succ', pf_mul _ _ hx]

theorem bld_eq {ξ h : Perm (Fin 24)} (hz : ∀ i < 24, pf ξ i = getN 0 z i)
    (hcrd : crdOK z crd (Fl ++ Tl) = true) (hlen8 : (Fl ++ Tl).length = 8)
    (hlt : ∀ x ∈ Fl ++ Tl, x < 24) (hc : Commute h ξ) {x : Nat} (hx : x < 24) :
    bld z crd ((Fl ++ Tl).map (pf h)) x = pf h x := by
  obtain ⟨hi8, hxe⟩ := crdOK_spec hcrd x hx
  have hmem := getN_mem' (l := Fl ++ Tl) (i := getN 0 crd x % 8) (by omega)
  have hL := hlt _ hmem
  change zPow z (getN 0 crd x / 8) (getN 0 ((Fl ++ Tl).map (pf h)) (getN 0 crd x % 8)) = _
  rw [getN_map _ (by omega), zPow_pf hz _ (pf_lt _ hL), ← pf_mul _ _ hL,
    ((hc.pow_right (getN 0 crd x / 8)).eq).symm, pf_mul _ _ hL, ← zPow_pf hz _ hL, hxe]

theorem card_cent_le (G : Subgroup (Perm (Fin 24))) {n : Nat}
    (hlen : P.length = B.length) (hB : B.length = 12) (hinv : invOK B P = true)
    (hG : ∀ g ∈ G, genOK B P (pf g) = true)
    {ξ : Perm (Fin 24)} (hξ : ξ ∈ G) (hz : ∀ i < 24, pf ξ i = getN 0 z i)
    (hfix : fixOK z Fl = true) (hO : inC B P (maskL Fl ||| maskL Tl) = true)
    (hpc : pcN (maskL Fl ||| maskL Tl) 24 = 8)
    (hoct : octOK B z (maskL Fl) (maskL Tl) = true)
    (hcrd : crdOK z crd (Fl ++ Tl) = true)
    (hcand : candN B P z crd Fl Tl = n)
    (hFl : Fl.length = 4) (hTl : Tl.length = 4) (hd : distB (Fl ++ Tl) = true)
    (hlt : ∀ x ∈ Fl ++ Tl, x < 24) :
    Nat.card ↥(G ⊓ Subgroup.centralizer ({ξ} : Set (Perm (Fin 24)))) ≤ 5 * n := by
  classical
  have hinv' : ∀ m < 2 ^ B.length, decode P (combo B m) = m := fun m hm =>
    invOK_spec hinv m (by rw [hB] at hm; norm_num at hm; omega)
  have hnd : (Fl ++ Tl).Nodup := distB_spec hd
  have hlen8 : (Fl ++ Tl).length = 8 := by rw [List.length_append, hFl, hTl]
  have hltF : ∀ x ∈ Fl, x < 24 := fun x hx => hlt x (List.mem_append_left _ hx)
  have hltT : ∀ x ∈ Tl, x < 24 := fun x hx => hlt x (List.mem_append_right _ hx)
  have hdisj : ∀ x ∈ Fl, x ∉ Tl := fun x hx hx' =>
    (List.nodup_append.1 hnd).2.2 x hx x hx' rfl
  have hF : ∀ x < 24, (pf ξ x = x ↔ x ∈ Fl) := fun x hx => by
    rw [hz x hx]
    exact (fixOK_spec hfix x hx).2
  have hFg : ∀ g : Perm (Fin 24), Commute g ξ → ∀ x ∈ Fl, pf g x ∈ Fl := by
    intro g hc x hx
    have hx24 := hltF x hx
    rw [← hF _ (pf_lt g hx24), ← pf_mul _ _ hx24, ← hc.eq, pf_mul _ _ hx24, (hF x hx24).2 hx]
  set Lst := (cands Fl Tl).filter fun c => genOK B P (bld z crd c) with hLst
  have key : ∀ g ∈ G, Commute g ξ → ∃ j : Fin 5, ∀ t ∈ Tl, pf ((ξ ^ (j : Nat))⁻¹ * g) t ∈ Tl := by
    intro g hgG hc
    set O := maskL Fl ||| maskL Tl with hOdef
    have hgi : Commute g⁻¹ ξ := hc.inv_left
    have hinC := inC_img hlen hinv' (pf_inj g) (hG g hgG) hO
    obtain ⟨s, hs, hsa⟩ := (inC_iff hlen hinv' _).1 hinC
    have h8 : pcN (combo B s) 24 = 8 := by
      rw [hsa, pc_imgF (fun i hi => pf_lt g hi) (pf_inj g), hpc]
    have hbitO : ∀ x, x < 24 → (x ∈ Fl ∨ x ∈ Tl) → (imgF (pf g) O).testBit (pf g x) = true := by
      intro x hx hm
      rw [testBit_imgF_app (pf_inj g) hx, hOdef, Nat.testBit_or, Bool.or_eq_true,
        testBit_maskL, testBit_maskL]
      exact hm
    have hland : combo B s &&& maskL Fl = maskL Fl := by
      apply Nat.eq_of_testBit_eq
      intro y
      rw [Nat.testBit_and]
      cases hy : (maskL Fl).testBit y
      · simp
      · have hyF := (testBit_maskL y Fl).1 hy
        have hy24 := hltF y hyF
        have hy' := hFg g⁻¹ hgi y hyF
        have e := hbitO _ (pf_lt _ hy24) (Or.inl hy')
        rw [pf_pf_inv g hy24] at e
        rw [hsa, e]
        rfl
    have hs' : s < 4096 := by rw [hB] at hs; norm_num at hs; omega
    obtain ⟨j, hj, hje⟩ := octOK_spec hoct s hs' h8 hland
    refine ⟨⟨j, hj⟩, fun t ht => ?_⟩
    have ht24 := hltT t ht
    have e := hbitO t ht24 (Or.inr ht)
    rw [← hsa, hje, Nat.testBit_or, Bool.or_eq_true, testBit_maskL, testBit_imgF] at e
    rcases e with e | ⟨t', ht', hbt, he⟩
    · exact absurd (by rw [← pf_inv_pf g ht24]; exact hFg g⁻¹ hgi _ e) (hdisj t · ht)
    · rw [(testBit_maskL t' Tl)] at hbt
      rw [zPow_pf hz j ht'] at he
      change pf ((ξ ^ j)⁻¹ * g) t ∈ Tl
      rw [pf_mul _ _ ht24, ← he, pf_inv_pf _ ht']
      exact hbt
  have hmemL : ∀ h ∈ G, Commute h ξ → (∀ t ∈ Tl, pf h t ∈ Tl) →
      (Fl ++ Tl).map (pf h) ∈ Lst := by
    intro h hhG hc hT
    rw [hLst, List.mem_filter]
    refine ⟨?_, ?_⟩
    · have hnd' : ((Fl ++ Tl).map (pf h)).Nodup :=
        hnd.map_on fun x hx y hy e => pf_inj h x (hlt x hx) y (hlt y hy) e
      rw [List.map_append] at hnd' ⊢
      refine mem_cands (mem_perms4_of (by rw [List.length_map, hFl]) (List.nodup_append.1 hnd').1
        fun x hx => ?_) (mem_perms4_of (by rw [List.length_map, hTl])
          (List.nodup_append.1 hnd').2.1 fun x hx => ?_)
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hFg h hc y hy
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hT y hy
    · rw [genOK_congr (g := pf h) (fun x hx => bld_eq hz hcrd hlen8 hlt hc hx)]
      exact hG h hhG
  have hinj : ∀ h h' : Perm (Fin 24), Commute h ξ → Commute h' ξ →
      (Fl ++ Tl).map (pf h) = (Fl ++ Tl).map (pf h') → h = h' := by
    intro h h' hc hc' e
    refine pf_ext fun x hx => ?_
    rw [← bld_eq hz hcrd hlen8 hlt hc hx, ← bld_eq hz hcrd hlen8 hlt hc' hx, e]
  have hcomm : ∀ g : ↥(G ⊓ Subgroup.centralizer ({ξ} : Set (Perm (Fin 24)))),
      Commute (g : Perm (Fin 24)) ξ := fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
  choose J hJ using fun g : ↥(G ⊓ Subgroup.centralizer ({ξ} : Set (Perm (Fin 24)))) =>
    key g (Subgroup.mem_inf.1 g.2).1 (hcomm g)
  have hmemG : ∀ g : ↥(G ⊓ Subgroup.centralizer ({ξ} : Set (Perm (Fin 24)))),
      (ξ ^ (J g : Nat))⁻¹ * (g : Perm (Fin 24)) ∈ G := fun g =>
    G.mul_mem (G.inv_mem (G.pow_mem hξ _)) (Subgroup.mem_inf.1 g.2).1
  have hcomm' : ∀ g : ↥(G ⊓ Subgroup.centralizer ({ξ} : Set (Perm (Fin 24)))),
      Commute ((ξ ^ (J g : Nat))⁻¹ * (g : Perm (Fin 24))) ξ := fun g =>
    ((Commute.refl ξ).pow_left _).inv_left.mul_left (hcomm g)
  let Φ : ↥(G ⊓ Subgroup.centralizer ({ξ} : Set (Perm (Fin 24)))) → Fin 5 × ↥Lst.toFinset :=
    fun g => (J g, ⟨(Fl ++ Tl).map (pf ((ξ ^ (J g : Nat))⁻¹ * g)),
      List.mem_toFinset.2 (hmemL _ (hmemG g) (hcomm' g) (hJ g))⟩)
  have hΦ : Function.Injective Φ := by
    intro g g' e
    have e1 : J g = J g' := congrArg Prod.fst e
    have e2 := congrArg (fun p => (p.2 : List Nat)) e
    simp only [Φ] at e2
    rw [e1] at e2
    have e3 := hinj _ _ (e1 ▸ hcomm' g) (hcomm' g') e2
    exact Subtype.ext (mul_left_cancel e3)
  calc Nat.card ↥(G ⊓ Subgroup.centralizer ({ξ} : Set (Perm (Fin 24))))
      ≤ Nat.card (Fin 5 × ↥Lst.toFinset) := Nat.card_le_card_of_injective Φ hΦ
    _ = 5 * Lst.toFinset.card := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card,
          Fintype.card_coe]
    _ ≤ 5 * Lst.length := Nat.mul_le_mul_left _ (List.toFinset_card_le _)
    _ = 5 * n := by rw [← hcand]; rfl

end Perm

end CFSG.KC.J4Five

end
