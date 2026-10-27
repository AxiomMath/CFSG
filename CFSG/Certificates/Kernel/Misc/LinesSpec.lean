module

public import CFSG.Certificates.Kernel.Misc.LinesPerp
public import CFSG.Certificates.Kernel.Misc.LinesGeom
import CFSG.Certificates.Kernel.Misc.LinesAlg
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option exponentiation.threshold 1000

namespace CFSG.KC.Misc.Lines

open CFSG.F4.Native CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46
  CFSG.KC.Misc.Polar CFSG.KS.PK

theorem testBit_recOr (l : List Nat) (q : Nat) :
    (List.rec (motive := fun _ => Nat) 0 (fun p _ ih => Nat.lor ih (Nat.shiftLeft 1 p)) l).testBit q
      = decide (q ∈ l) := by
  induction l with
  | nil => simp
  | cons p t ih =>
    show (Nat.lor (List.rec (motive := fun _ => Nat) 0
      (fun p _ ih => Nat.lor ih (Nat.shiftLeft 1 p)) t) (Nat.shiftLeft 1 p)).testBit q = _
    rw [Nat.lor_eq, Nat.testBit_or, ih]
    have e : Nat.shiftLeft 1 p = 2 ^ p := Nat.one_shiftLeft p
    rw [e, Nat.testBit_two_pow]
    by_cases h : p = q
    · subst h; simp
    · have h' : q ≠ p := fun e => h e.symm
      simp [h, h']

theorem chain_iff (l : List Nat) : ∀ prev,
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun p _ ih prev => andB (Nat.blt prev (Nat.succ p)) (ih (Nat.succ p))) l prev = true) ↔
      (l.Pairwise (· < ·) ∧ ∀ p ∈ l, prev ≤ p) := by
  induction l with
  | nil => intro prev; simp
  | cons p t ih =>
    intro prev
    show andB (Nat.blt prev (Nat.succ p)) (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun p _ ih prev => andB (Nat.blt prev (Nat.succ p)) (ih (Nat.succ p))) t (Nat.succ p))
        = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih, Nat.blt_eq, List.pairwise_cons]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨fun q hq => ?_, h2⟩, ?_⟩
      · have := h3 q hq
        omega
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · omega
        · have := h3 q hq
          omega
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by have := h3 p (List.mem_cons_self); omega, h2, fun q hq => ?_⟩
      have := h1 q hq
      omega

theorem plK_letLN'_gen (k : List Nat → Bool) (l : List Nat) : ∀ acc : List Nat,
    (List.rec (motive := fun _ => List Nat → Bool) (fun acc => k acc.reverse)
      (fun x _ ih acc => letB x fun x => ih (List.cons x acc)) l) acc = k (acc.reverse ++ l) := by
  induction l with
  | nil =>
    intro acc
    simp
  | cons x l ih =>
    intro acc
    refine (letB_eq _ _).trans ?_
    rw [ih]
    simp

theorem plK_letLN'_eq (l : List Nat) (k : List Nat → Bool) : plK.letLN' l k = k l := by
  have := plK_letLN'_gen k l []
  rw [List.reverse_nil, List.nil_append] at this
  exact this

theorem plK_spec {PB : Nat → Nat} {PL : Nat → List Nat} (h : plK PB PL = true) :
    ∀ x < 693, (PL x).length = 181 ∧ (PL x).Pairwise (· < ·) ∧
      ∀ q, (PB x).testBit q = decide (q ∈ PL x) := by
  intro x hx
  unfold plK at h
  rw [allN_lqt_iff] at h
  have h1 := h x hx
  rw [plK_letLN'_eq] at h1
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, lenN_misc_eq] at h1
  obtain ⟨h2, h3, h4⟩ := h1
  refine ⟨h2, ((chain_iff _ _).1 h4).1, fun q => ?_⟩
  rw [← h3, testBit_recOr]

@[expose] def lnP1 (UP PP x y : Nat) : Nat := fd 10 PP (normC (fd 12 UP x ^^^ fd 12 UP y))

@[expose] def lnP2 (UP PP x y : Nat) : Nat :=
  fd 10 PP (normC (fd 12 UP x ^^^ scaleC 2 (fd 12 UP y)))

@[expose] def lnP3 (UP PP x y : Nat) : Nat :=
  fd 10 PP (normC (fd 12 UP x ^^^ scaleC 3 (fd 12 UP y)))

@[expose] def lineL (UP PP x y : Nat) : List Nat :=
  [x, y, lnP1 UP PP x y, lnP2 UP PP x y, lnP3 UP PP x y]

theorem line3_eq (UP PP x y : Nat) :
    line3 UP PP x y = lnP1 UP PP x y + 1024 * (lnP2 UP PP x y + 1024 * lnP3 UP PP x y) := by
  unfold line3
  simp only [letN_eq, at'_eq, normK_eq, scaleK_eq]
  rfl

theorem lnP1_lt (UP PP x y : Nat) : lnP1 UP PP x y < 1024 := fd_lt 10 PP _

theorem lnP2_lt (UP PP x y : Nat) : lnP2 UP PP x y < 1024 := fd_lt 10 PP _

theorem lnP3_lt (UP PP x y : Nat) : lnP3 UP PP x y < 1024 := fd_lt 10 PP _

theorem line3_a (UP PP x y : Nat) : Nat.mod (line3 UP PP x y) 1024 = lnP1 UP PP x y := by
  have h1 := lnP1_lt UP PP x y
  rw [line3_eq]
  have : (lnP1 UP PP x y + 1024 * (lnP2 UP PP x y + 1024 * lnP3 UP PP x y)) % 1024 =
    lnP1 UP PP x y := by omega
  exact this

theorem line3_b (UP PP x y : Nat) :
    Nat.mod (Nat.div (line3 UP PP x y) 1024) 1024 = lnP2 UP PP x y := by
  have h1 := lnP1_lt UP PP x y
  have h2 := lnP2_lt UP PP x y
  rw [line3_eq]
  have : (lnP1 UP PP x y + 1024 * (lnP2 UP PP x y + 1024 * lnP3 UP PP x y)) / 1024 % 1024 =
    lnP2 UP PP x y := by omega
  exact this

theorem line3_c (UP PP x y : Nat) : Nat.div (line3 UP PP x y) 1048576 = lnP3 UP PP x y := by
  have h1 := lnP1_lt UP PP x y
  have h2 := lnP2_lt UP PP x y
  have h3 := lnP3_lt UP PP x y
  rw [line3_eq]
  have : (lnP1 UP PP x y + 1024 * (lnP2 UP PP x y + 1024 * lnP3 UP PP x y)) / 1048576 =
    lnP3 UP PP x y := by omega
  exact this

theorem lineB_testBit (UP PP x y z : Nat) :
    (lineB UP PP x y).testBit z = true ↔ z ∈ lineL UP PP x y := by
  unfold lineB
  rw [letN_eq, line3_a, line3_b, line3_c]
  have sl : ∀ n, Nat.shiftLeft 1 n = 2 ^ n := Nat.one_shiftLeft
  simp only [Nat.lor_eq, sl]
  simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, lineL,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((h | h) | h | h | h) <;> simp [h]
  · rintro (h | h | h | h | h) <;> simp [h]

theorem line5_spec {UP PP x y : Nat} (h : line5 UP PP x y = true) :
    lnP1 UP PP x y < 693 ∧ lnP2 UP PP x y < 693 ∧ lnP3 UP PP x y < 693 ∧
      (lineL UP PP x y).Nodup := by
  unfold line5 at h
  simp only [letB_eq, line3_a, line3_b, line3_c, andB_eq, notB_eq, allL_lqt_iff, Bool.and_eq_true,
    Nat.blt_eq, Bool.not_eq_true', nat_beq_eq_false_iff, List.mem_cons, List.not_mem_nil,
    or_false] at h
  obtain ⟨⟨h1, h2, h3⟩, h4, ⟨h5, h6, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  have a1 := h8 _ (Or.inl rfl)
  have a2 := h8 _ (Or.inr (Or.inl rfl))
  have a3 := h8 _ (Or.inr (Or.inr rfl))
  have hs : ∀ a b : ℕ, a ≠ b → b ≠ a := fun a b h e => h e.symm
  simp [lineL, List.nodup_cons, h4, h5, h6, h7, hs _ _ a1.1, hs _ _ a1.2, hs _ _ a2.1,
    hs _ _ a2.2, hs _ _ a3.1, hs _ _ a3.2]

@[expose] noncomputable def interB (PB : Nat → Nat) (Py : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (Nat.sub (Nat.shiftLeft 1 693) 1)
    (fun w _ ih => Bool.rec (motive := fun _ => Nat) ih (Nat.land ih (PB w)) (bitK Py w)) l

theorem interB_nil (PB : Nat → Nat) (Py : Nat) : interB PB Py [] = 2 ^ 693 - 1 := by
  have e : Nat.shiftLeft 1 693 = 2 ^ 693 := Nat.one_shiftLeft 693
  show Nat.sub (Nat.shiftLeft 1 693) 1 = _
  rw [e]
  rfl

theorem interB_cons (PB : Nat → Nat) (Py w : Nat) (t : List Nat) :
    interB PB Py (w :: t) =
      if bitK Py w = true then interB PB Py t &&& PB w else interB PB Py t := by
  show Bool.rec (motive := fun _ => Nat) (interB PB Py t) (Nat.land (interB PB Py t) (PB w))
    (bitK Py w) = _
  cases bitK Py w <;> rfl

theorem interB_testBit (PB : Nat → Nat) (Py : Nat) (l : List Nat) (z : Nat) :
    (interB PB Py l).testBit z =
      (decide (z < 693) && l.all fun w => !bitK Py w || (PB w).testBit z) := by
  induction l with
  | nil =>
    rw [interB_nil, Nat.testBit_two_pow_sub_one]
    simp
  | cons w t ih =>
    rw [interB_cons, List.all_cons]
    by_cases hb : bitK Py w = true
    · rw [if_pos hb, Nat.testBit_and, ih, hb]
      cases (PB w).testBit z <;> simp [Bool.and_comm]
    · rw [if_neg hb, ih]
      have hb' : bitK Py w = false := by simpa using hb
      rw [hb']
      simp

theorem linesK_spec {UP PP : Nat} {PB : Nat → Nat} {PL : Nat → List Nat}
    (h : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true) :
    ∀ x < 693, ∀ y ∈ PL x, x < y →
      line5 UP PP x y = true ∧ lineB UP PP y x = lineB UP PP x y ∧
      ∀ z, (lineB UP PP x y).testBit z =
        (decide (z < 693) && (PL x).all fun w => !bitK (PB y) w || (PB w).testBit z) := by
  intro x hx y hy hxy
  have hk : x / 33 < 21 := by omega
  have h1 := h (x / 33) hk
  unfold linesK at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (x % 33) (by omega)
  have e : 33 * (x / 33) + x % 33 = x := by omega
  simp only [Nat.add_eq, e, letB_eq, impB_eq, andB_eq, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', allL_lqt_iff, Nat.beq_eq] at h2
  have hxb : Nat.blt x 693 = true := Nat.blt_eq.mpr hx
  rcases h2 with h2 | h2
  · rw [hxb] at h2
    exact absurd h2 (by simp)
  have h3 := h2 y hy
  rcases h3 with h3 | ⟨h4, h5, h6⟩
  · have : ¬ x < y := by
      intro hlt
      have := Nat.blt_eq.mpr hlt
      rw [this] at h3
      exact absurd h3 (by simp)
    exact absurd hxy this
  refine ⟨h4, h5, fun z => ?_⟩
  have h7 : interB PB (PB y) (PL x) = lineB UP PP x y := h6
  rw [← h7, interB_testBit]

@[expose] noncomputable def relB (PB : Nat → Nat) (x y : Nat) : Bool := bitK (PB x) y

theorem relB_iff {UL : List Nat} {UP PP : Nat} {PB : Nat → Nat} (H : Pts UL UP PP)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) {x y : Nat} (hx : x < 693) (hy : y < 693) :
    relB PB x y = true ↔ hermC (UL.getD y 0) (UL.getD x 0) = 0 := by
  have := (perpK_spec hperp x hx).2 y hy
  rwa [H.fd12 y hy, H.fd12 x hx] at this

theorem relB_refl {UL : List Nat} {UP PP : Nat} {PB : Nat → Nat} (H : Pts UL UP PP)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) {x : Nat} (hx : x < 693) :
    relB PB x x = true :=
  (relB_iff H hperp hx hx).2 ((isPt_iff _).1 (H.pt x hx)).2.1

theorem relB_symm {UL : List Nat} {UP PP : Nat} {PB : Nat → Nat} (H : Pts UL UP PP)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) {x y : Nat} (hx : x < 693) (hy : y < 693)
    (h : relB PB x y = true) : relB PB y x = true := by
  rw [relB_iff H hperp hx hy] at h
  rw [relB_iff H hperp hy hx]
  exact (hermC_zero_comm (H.lt y hy) (H.lt x hx)).1 h

theorem testBit_lt_of_perpK {UP : Nat} {PB : Nat → Nat}
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) {p q : Nat} (hp : p < 693)
    (h : (PB p).testBit q = true) : q < 693 := by
  by_contra hq
  have hpb := (perpK_spec hperp p hp).1
  have h2 : 2 ^ 693 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hq)
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hpb h2)] at h
  exact absurd h (by simp)

theorem mem_PL_iff {UP : Nat} {PB : Nat → Nat} {PL : Nat → List Nat}
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true) {p : Nat}
    (hp : p < 693) {q : Nat} : q ∈ PL p ↔ q < 693 ∧ relB PB p q = true := by
  obtain ⟨-, -, hbits⟩ := plK_spec hpl p hp
  have hb := hbits q
  have hr : relB PB p q = (PB p).testBit q := bitK_eq_testBit _ _
  rw [hr]
  constructor
  · intro h
    have h1 : (PB p).testBit q = true := by rw [hb]; simpa using h
    exact ⟨testBit_lt_of_perpK hperp hp h1, h1⟩
  · rintro ⟨-, h⟩
    rw [hb] at h
    simpa using h

theorem relB_deg {UP : Nat} {PB : Nat → Nat} {PL : Nat → List Nat}
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true) {p : Nat}
    (hp : p < 693) :
    ((Finset.range 693).filter fun q : Nat => relB PB p q = true).card = 181 := by
  obtain ⟨hlen, hsort, -⟩ := plK_spec hpl p hp
  have hnd : (PL p).Nodup := hsort.nodup
  have e : ((Finset.range 693).filter fun q : Nat => relB PB p q = true) = (PL p).toFinset := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    rw [mem_PL_iff hperp hpl hp]
  rw [e, List.toFinset_card_of_nodup hnd, hlen]

theorem mem_lineL_iff {UP PP : Nat} {PB : Nat → Nat} {PL : Nat → List Nat}
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true)
    (hl : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true) {x y : Nat} (hx : x < 693)
    (hy : y < 693) (hxy : x < y) (hr : relB PB x y = true) (z : Nat) :
    z ∈ lineL UP PP x y ↔ z < 693 ∧ ∀ w < 693, relB PB x w = true → relB PB y w = true →
      relB PB w z = true := by
  have hyx : y ∈ PL x := (mem_PL_iff hperp hpl hx).2 ⟨hy, hr⟩
  obtain ⟨-, -, hbit⟩ := linesK_spec hl x hx y hyx hxy
  rw [← lineB_testBit, hbit z]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']
  refine and_congr Iff.rfl ?_
  constructor
  · intro h w hw h1 h2
    have := h w ((mem_PL_iff hperp hpl hx).2 ⟨hw, h1⟩)
    rcases this with h3 | h3
    · exact absurd h2 (by rw [relB, h3]; simp)
    · simpa [relB, bitK_eq_testBit] using h3
  · intro h w hw
    obtain ⟨hw1, hw2⟩ := (mem_PL_iff hperp hpl hx).1 hw
    by_cases hb : bitK (PB y) w = true
    · right
      have := h w hw1 hw2 hb
      simpa [relB, bitK_eq_testBit] using this
    · left
      simpa using hb

theorem lineL_symm_iff {UP PP : Nat} {PB : Nat → Nat} {PL : Nat → List Nat}
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true)
    (hl : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true) {x y : Nat} (hx : x < 693)
    (hy : y < 693) (hxy : x < y) (hr : relB PB x y = true) (z : Nat) :
    z ∈ lineL UP PP y x ↔ z ∈ lineL UP PP x y := by
  have hyx : y ∈ PL x := (mem_PL_iff hperp hpl hx).2 ⟨hy, hr⟩
  obtain ⟨-, h5, -⟩ := linesK_spec hl x hx y hyx hxy
  rw [← lineB_testBit, ← lineB_testBit, h5]

theorem nodup_lineL {UP PP : Nat} {PB : Nat → Nat} {PL : Nat → List Nat}
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true)
    (hl : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true) {x y : Nat} (hx : x < 693)
    (hy : y < 693) (hxy : x < y) (hr : relB PB x y = true) : (lineL UP PP x y).Nodup := by
  have hyx : y ∈ PL x := (mem_PL_iff hperp hpl hx).2 ⟨hy, hr⟩
  obtain ⟨h4, -, -⟩ := linesK_spec hl x hx y hyx hxy
  exact (line5_spec h4).2.2.2

theorem mem_lineL_Ln {UL : List Nat} {UP PP : Nat} {PB : Nat → Nat} {PL : Nat → List Nat}
    (H : Pts UL UP PP) (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true)
    (hpl : plK PB PL = true) (hl : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true) {x y : Nat}
    (hx : x < 693) (hy : y < 693) (hne : x ≠ y) (hr : relB PB x y = true) (z : Nat) :
    z ∈ lineL UP PP x y ↔ z ∈ Ln (relB PB) x y := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · rw [mem_lineL_iff hperp hpl hl hx hy h hr z, mem_Ln]
  · have hr' : relB PB y x = true := relB_symm H hperp hx hy hr
    rw [lineL_symm_iff hperp hpl hl hy hx h hr' z, mem_lineL_iff hperp hpl hl hy hx h hr' z,
      Ln_comm (relB PB) x y, mem_Ln]

theorem polarRel_of_kernel {UL : List Nat} {UP PP : Nat} {PB : Nat → Nat} {PL : Nat → List Nat}
    (H : Pts UL UP PP) (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true)
    (hpl : plK PB PL = true) (hl : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true) :
    PolarRel (relB PB) where
  refl x hx := relB_refl H hperp hx
  symm x hx y hy h := relB_symm H hperp hx hy h
  deg p hp := relB_deg hperp hpl hp
  card5 x hx y hy hxy hr := by
    have e : Ln (relB PB) x y = (lineL UP PP x y).toFinset := by
      ext z
      rw [List.mem_toFinset, mem_lineL_Ln H hperp hpl hl hx hy (Nat.ne_of_lt hxy) hr z]
    rw [e, List.toFinset_card_of_nodup (nodup_lineL hperp hpl hl hx hy hxy hr)]
    rfl

theorem testBit_sub_one_of_odd {n : Nat} (h : n.testBit 0 = true) (w : Nat) :
    (n - 1).testBit w = (decide (w ≠ 0) && n.testBit w) := by
  rw [Nat.testBit_zero] at h
  have hn : n % 2 = 1 := by simpa using h
  cases w with
  | zero =>
    rw [Nat.testBit_zero]
    simp
    omega
  | succ k =>
    rw [Nat.testBit_succ, Nat.testBit_succ]
    have : (n - 1) / 2 = n / 2 := by omega
    rw [this]
    simp

theorem twinsK_spec {UL : List Nat} {UP PP : Nat} {PB : Nat → Nat} {PL : Nat → List Nat}
    (H : Pts UL UP PP) (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true)
    (hpl : plK PB PL = true) (ht : twinsK UP PP PB PL = true) :
    ∀ x ∈ PL 0, x ≠ 0 → ∀ y ∈ PL 0, y ≠ 0 → y ≠ x →
      ((∀ w ∈ PL 0, w ≠ 0 → relB PB x w = relB PB y w) ↔ y ∈ lineL UP PP 0 x) := by
  intro x hx hx0 y hy hy0 hyx
  unfold twinsK at ht
  simp only [letB_eq, allL_lqt_iff, impB_eq, andB_eq, notB_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at ht
  have h1 := ht x hx
  rcases h1 with h1 | h1
  · rw [(nat_beq_eq_false_iff _ _).2 hx0] at h1
    exact absurd h1 (by simp)
  have h2 := h1 y hy
  rcases h2 with h2 | h3
  · rw [(nat_beq_eq_false_iff _ _).2 hy0, (nat_beq_eq_false_iff _ _).2 hyx] at h2
    exact absurd h2 (by simp)
  have hz : relB PB 0 0 = true := relB_refl H hperp (by norm_num)
  have hz' : (PB 0).testBit 0 = true := by rwa [relB, bitK_eq_testBit] at hz
  have hD : ∀ w, ((PB 0).sub 1).testBit w = decide (w ≠ 0 ∧ w ∈ PL 0) := by
    intro w
    have e : (PB 0).sub 1 = PB 0 - 1 := rfl
    rw [e, testBit_sub_one_of_odd hz' w, (plK_spec hpl 0 (by norm_num)).2.2 w]
    simp
  have hiff : (Nat.land (PB y) ((PB 0).sub 1) = Nat.land (PB x) ((PB 0).sub 1)) ↔
      ∀ w ∈ PL 0, w ≠ 0 → relB PB x w = relB PB y w := by
    constructor
    · intro h w hw hw0
      have := congrArg (fun n => n.testBit w) h
      simp only [Nat.land_eq, Nat.testBit_and, hD] at this
      simp only [relB, bitK_eq_testBit]
      simpa [hw, hw0] using this.symm
    · intro h
      apply Nat.eq_of_testBit_eq
      intro w
      simp only [Nat.land_eq, Nat.testBit_and, hD]
      by_cases hw : w ≠ 0 ∧ w ∈ PL 0
      · have := h w hw.2 hw.1
        simp only [relB, bitK_eq_testBit] at this
        simp [hw, this]
      · simp [hw]
  rw [← hiff]
  have hLb : bitK (lineB UP PP 0 x) y = true ↔ y ∈ lineL UP PP 0 x := by
    rw [bitK_eq_testBit, lineB_testBit]
  rw [← hLb]
  cases hc : Nat.beq (Nat.land (PB y) ((PB 0).sub 1)) (Nat.land (PB x) ((PB 0).sub 1))
  · rw [hc] at h3
    simp only [Bool.not_eq_true'] at h3
    have : Nat.land (PB y) ((PB 0).sub 1) ≠ Nat.land (PB x) ((PB 0).sub 1) := by
      intro e
      rw [← Nat.beq_eq, hc] at e
      exact absurd e (by simp)
    constructor
    · intro h
      exact absurd h this
    · intro h
      rw [h3] at h
      exact absurd h (by simp)
  · rw [hc] at h3
    have : Nat.land (PB y) ((PB 0).sub 1) = Nat.land (PB x) ((PB 0).sub 1) := by
      rw [← Nat.beq_eq]; exact hc
    exact ⟨fun _ => h3, fun _ => this⟩

theorem anyL_iff' (l : List Nat) (f : Nat → Bool) : anyL l f = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil => simp [anyL]
  | cons x t ih =>
    show orB (f x) (anyL t f) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih]
    simp

theorem land_shiftRight_one' (S n : Nat) :
    Nat.land (Nat.shiftRight S n) 1 = if S.testBit n = true then 1 else 0 := by
  have e : Nat.land (Nat.shiftRight S n) 1 = S / 2 ^ n % 2 := by
    rw [show Nat.land (Nat.shiftRight S n) 1 = (S >>> n) &&& 1 from rfl, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (S / 2 ^ n) with h | h <;> simp [h]

theorem popK_rec_eq (S n : Nat) :
    Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight S i) 1)) n =
      ((Finset.range n).filter fun i : Nat => S.testBit i = true).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    show Nat.add (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight S i) 1)) n)
        (Nat.land (Nat.shiftRight S n) 1) = _
    rw [ih, Finset.range_add_one, Finset.filter_insert, land_shiftRight_one']
    by_cases h : S.testBit n = true
    · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
    · rw [if_neg h, if_neg h]
      rfl

theorem popK_eq (S : Nat) :
    popK S = ((Finset.range 693).filter fun i : Nat => S.testBit i = true).card := by
  unfold popK
  rw [letN_eq]
  exact popK_rec_eq S 693

@[expose] noncomputable def NS (PB : Nat → Nat) (q : Nat) : Finset Nat :=
  (Finset.range 693).filter fun w : Nat => relB PB 0 w = true ∧ relB PB q w = true

theorem mem_NS {PB : Nat → Nat} {q w : Nat} :
    w ∈ NS PB q ↔ w < 693 ∧ relB PB 0 w = true ∧ relB PB q w = true := by
  simp [NS]

@[expose] def t0 (UP PP q : Nat) : Nat := fd 10 PP (normC (tvC (fd 12 UP 0) (fd 12 UP q)))

theorem tv0_eq (UP PP q : Nat) : tv0 UP PP q = t0 UP PP q := by
  unfold tv0 t0
  simp only [at'_eq, normK_eq, tvK_eq]

theorem testBit_land_iff {UP : Nat} {PB : Nat → Nat}
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) {q : Nat} (w : Nat) :
    (Nat.land (PB 0) (PB q)).testBit w = true ↔ w ∈ NS PB q := by
  rw [mem_NS, Nat.land_eq, Nat.testBit_and, Bool.and_eq_true]
  simp only [relB, bitK_eq_testBit]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨testBit_lt_of_perpK hperp (by norm_num) h1, h1, h2⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩

theorem ppK_spec {UP PP : Nat} {PB : Nat → Nat} {PL : Nat → List Nat}
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true)
    (hpl : plK PB PL = true) (hpp : ∀ k < 21, ppK UP PP PB PL (33 * k) 33 = true) :
    ∀ q < 693, relB PB 0 q = false →
      (NS PB q).card = 45 ∧
      (∃ a b, a ∈ NS PB q ∧ b ∈ NS PB q ∧ a ≠ b ∧ relB PB a b = true ∧
        ∃ c, c ∈ lineL UP PP a b ∧ c ≠ a ∧ c ≠ b ∧ c ∈ NS PB q) ∧
      (∀ a ∈ NS PB q, ∀ b ∈ NS PB q, a ≠ b → relB PB a b = true →
        ∃ w ∈ NS PB q, relB PB a w ≠ relB PB b w) ∧
      (∀ q' < 693, relB PB 0 q' = false →
        (∀ w < 693, relB PB 0 w = true → relB PB q' w = relB PB q w) →
        q' = q ∨ q' = t0 UP PP q) := by
  intro q hq hrq
  have hk : q / 33 < 21 := by omega
  have h1 := hpp (q / 33) hk
  unfold ppK at h1
  simp only [letB_eq] at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (q % 33) (by omega)
  have e : 33 * (q / 33) + q % 33 = q := by omega
  simp only [Nat.add_eq, e, impB_eq, andB_eq, orB_eq, notB_eq, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with h2 | ⟨c1, c2, c3, c4⟩
  · have hq' : q.blt 693 = true := Nat.blt_eq.mpr hq
    have : bitK (PB 0) q = false := hrq
    rw [hq', this] at h2
    exact absurd h2 (by simp)
  have hbit : ∀ w, bitK (Nat.land (PB 0) (PB q)) w = true ↔ w ∈ NS PB q := by
    intro w
    rw [bitK_eq_testBit]
    exact testBit_land_iff hperp w
  have hPL0 : ∀ a, a ∈ PL 0 ↔ a < 693 ∧ relB PB 0 a = true := fun a =>
    mem_PL_iff hperp hpl (by norm_num)
  have hNS_PL : ∀ a, a ∈ NS PB q → a ∈ PL 0 := fun a ha => by
    rw [mem_NS] at ha
    exact (hPL0 a).2 ⟨ha.1, ha.2.1⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have h45 : popK (Nat.land (PB 0) (PB q)) = 45 := by simpa using c1
    rw [popK_eq] at h45
    have e : NS PB q = (Finset.range 693).filter fun i : Nat =>
        (Nat.land (PB 0) (PB q)).testBit i = true := by
      ext i
      rw [Finset.mem_filter, Finset.mem_range, testBit_land_iff hperp]
      constructor
      · intro h
        exact ⟨(mem_NS.1 h).1, h⟩
      · exact fun h => h.2
    rw [e]
    exact h45
  ·
    rw [anyL_iff'] at c2
    obtain ⟨a, ha, h1⟩ := c2
    simp only [Bool.and_eq_true] at h1
    obtain ⟨h1a, h1b⟩ := h1
    rw [anyL_iff'] at h1b
    obtain ⟨b, hb, h2⟩ := h1b
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
    obtain ⟨h2b, h2c, h2d⟩ := h2
    have ha693 : a < 693 := ((hPL0 a).1 ha).1
    have hab' : a ≠ b := (nat_beq_eq_false_iff _ _).1 h2c
    have h3 : 3 ≤ popK (Nat.land (lineB UP PP a b) (Nat.land (PB 0) (PB q))) := by
      rwa [Nat.ble_eq] at h2d
    rw [popK_eq] at h3
    refine ⟨a, b, (hbit a).1 h1a, (hbit b).1 h2b, hab',
      ((mem_PL_iff hperp hpl ha693).1 hb).2, ?_⟩
    by_contra hno
    have hsub : ((Finset.range 693).filter fun i : Nat =>
        (Nat.land (lineB UP PP a b) (Nat.land (PB 0) (PB q))).testBit i = true) ⊆ {a, b} := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range, Nat.land_eq, Nat.testBit_and,
        Bool.and_eq_true] at hi
      obtain ⟨-, hi1, hi2⟩ := hi
      have hi1' : i ∈ lineL UP PP a b := (lineB_testBit _ _ _ _ _).1 hi1
      have hi2' : i ∈ NS PB q := (testBit_land_iff hperp i).1 hi2
      by_contra hni
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hni
      exact hno ⟨i, hi1', hni.1, hni.2, hi2'⟩
    have := Finset.card_le_card hsub
    have h4 : ({a, b} : Finset Nat).card ≤ 2 := Finset.card_le_two
    omega
  ·
    intro a ha b hb hab hrab
    rw [allL_lqt_iff] at c3
    have h1 := c3 a (hNS_PL a ha)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with h1 | h1
    · rw [(hbit a).2 ha] at h1
      exact absurd h1 (by simp)
    rw [allL_lqt_iff] at h1
    have ha693 : a < 693 := (mem_NS.1 ha).1
    have hbPL : b ∈ PL a := (mem_PL_iff hperp hpl ha693).2 ⟨(mem_NS.1 hb).1, hrab⟩
    have h2 := h1 b hbPL
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h2
    rcases h2 with h2 | h2
    · rw [(hbit b).2 hb, (nat_beq_eq_false_iff a b).2 hab] at h2
      exact absurd h2 (by simp)
    by_contra hno
    have hno' : ∀ w ∈ NS PB q, relB PB a w = relB PB b w := fun w hw => by
      by_contra h
      exact hno ⟨w, hw, h⟩
    have heq : Nat.land (PB b) (Nat.land (PB 0) (PB q)) =
        Nat.land (PB a) (Nat.land (PB 0) (PB q)) := by
      apply Nat.eq_of_testBit_eq
      intro w
      simp only [Nat.land_eq, Nat.testBit_and]
      by_cases hw : (PB 0).testBit w = true ∧ (PB q).testBit w = true
      · have hwNS : w ∈ NS PB q := (testBit_land_iff hperp w).1 (by simp [hw])
        have := hno' w hwNS
        simp only [relB, bitK_eq_testBit] at this
        simp [this]
      · have hw' : ((PB 0).testBit w && (PB q).testBit w) = false := by
          cases h0 : (PB 0).testBit w <;> cases hq' : (PB q).testBit w <;> simp_all
        rw [hw']
        simp
    rw [← Nat.beq_eq] at heq
    rw [heq] at h2
    exact absurd h2 (by simp)
  ·
    intro q' hq' hr0 hw
    rw [allN_lqt_iff] at c4
    have h1 := c4 q' hq'
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.not_not] at h1
    have heq : Nat.land (PB 0) (PB q') = Nat.land (PB 0) (PB q) := by
      apply Nat.eq_of_testBit_eq
      intro w
      simp only [Nat.land_eq, Nat.testBit_and]
      by_cases h0 : (PB 0).testBit w = true
      · have hw693 : w < 693 := testBit_lt_of_perpK hperp (by norm_num) h0
        have := hw w hw693 (by simpa [relB, bitK_eq_testBit] using h0)
        simp only [relB, bitK_eq_testBit] at this
        simp [h0, this]
      · have : (PB 0).testBit w = false := by simpa using h0
        simp [this]
    rcases h1 with h1 | h1 | h1 | h1
    · have : bitK (PB 0) q' = false := hr0
      rw [this] at h1
      exact absurd h1 (by simp)
    · rw [← Nat.beq_eq] at heq
      rw [heq] at h1
      exact absurd h1 (by simp)
    · exact Or.inl (Nat.eq_of_beq_eq_true h1)
    · exact Or.inr (by rw [← tv0_eq]; exact Nat.eq_of_beq_eq_true h1)

end CFSG.KC.Misc.Lines

end
