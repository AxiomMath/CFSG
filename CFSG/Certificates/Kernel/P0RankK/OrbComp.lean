module

public import CFSG.Certificates.Kernel.P0RankK.OrbForms
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.P0Orb

open CFSG.Monster.B.TwoA.Sp8.P0Rank

@[expose] noncomputable def spanF (bs : List ℕ) : Finset ℕ :=
  (Finset.range (2 ^ bs.length)).image (lAct bs)

theorem lAct_cons (c : ℕ) (cs : List ℕ) (x : ℕ) :
    lAct (c :: cs) x = (if x.testBit 0 then c else 0) ^^^ lAct cs (x / 2) := by
  change Nat.xor (bif Nat.beq (Nat.land x 1) 1 then c else 0) (lAct cs (Nat.shiftRight x 1)) = _
  have e1 : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
  have e2 : Nat.shiftRight x 1 = x / 2 := by
    change x >>> 1 = x / 2
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  rw [e1, e2, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> rfl

theorem lAct_zero : ∀ bs : List ℕ, lAct bs 0 = 0
  | [] => rfl
  | c :: cs => by rw [lAct_cons, lAct_zero cs]; simp

theorem lAct_xor : ∀ (bs : List ℕ) (x y : ℕ), lAct bs (x ^^^ y) = lAct bs x ^^^ lAct bs y
  | [], _, _ => by
    change (0 : ℕ) = 0 ^^^ 0
    rw [Nat.xor_zero]
  | c :: cs, x, y => by
    rw [lAct_cons, lAct_cons, lAct_cons, Nat.testBit_xor, Nat.xor_div_two, lAct_xor cs,
      ite_xor_bool]
    ac_rfl

theorem spanF_xorClosed (bs : List ℕ) : XorClosed (spanF bs) := by
  refine ⟨Finset.mem_image.2 ⟨0, Finset.mem_range.2 (Nat.two_pow_pos _), lAct_zero bs⟩, ?_⟩
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
  refine Finset.mem_image.2 ⟨x ^^^ y, Finset.mem_range.2 ?_, lAct_xor bs x y⟩
  exact Nat.xor_lt_two_pow (Finset.mem_range.1 hx) (Finset.mem_range.1 hy)

theorem spanF_nil : spanF [] = {0} := by
  rw [spanF, List.length_nil, pow_zero, Finset.range_one, Finset.image_singleton]
  rfl

theorem mem_spanF : ∀ (bs : List ℕ), ∀ b ∈ bs, b ∈ spanF bs
  | [], b, hb => absurd hb (by simp)
  | c :: cs, b, hb => by
    rw [spanF, Finset.mem_image]
    rcases List.mem_cons.1 hb with rfl | hb'
    · refine ⟨1, Finset.mem_range.2 (Nat.one_lt_two_pow (by simp)), ?_⟩
      rw [lAct_cons]
      simp [lAct_zero]
    · obtain ⟨y, hy, hyb⟩ := Finset.mem_image.1 (mem_spanF cs b hb')
      refine ⟨2 * y, Finset.mem_range.2 ?_, ?_⟩
      · rw [List.length_cons, pow_succ]
        have := Finset.mem_range.1 hy
        omega
      · rw [lAct_cons, Nat.mul_div_cancel_left y (by decide), hyb]
        simp [Nat.testBit_zero]

structure RepFacts (AT RT BC BU N r : ℕ) : Prop where
  card : (spanF (sbasis (slot RT r))).card = 2 ^ (slot RT r >>> 80)
  ext : ∀ σ < 2 ^ 16, (∀ y ∈ spanF (sbasis (slot RT r)), bet BC y σ = 0) → qf BU σ = 0 →
    σ ∉ spanF (sbasis (slot RT r)) → ∃ lam < 2 ^ 10, ∃ r' < N,
      slot RT r' >>> 80 = slot RT r >>> 80 + 1 ∧ aAct AT lam σ ∈ spanF (sbasis (slot RT r')) ∧
      ∀ y ∈ spanF (sbasis (slot RT r)), aAct AT lam y ∈ spanF (sbasis (slot RT r'))

theorem orb_lAct_mem {S : Finset ℕ} (hS : XorClosed S) :
    ∀ (L : List ℕ), (∀ l ∈ L, l ∈ S) → ∀ x, lAct L x ∈ S
  | [], _, _ => hS.1
  | c :: L, hL, x => by
    rw [lAct_cons]
    refine hS.2 _ ?_ _ (orb_lAct_mem hS L (fun l hl => hL l (List.mem_cons_of_mem _ hl)) _)
    split_ifs
    · exact hL c List.mem_cons_self
    · exact hS.1

theorem orb_lAct_zero : ∀ (L : List ℕ), (∀ l ∈ L, l = 0) → ∀ x, lAct L x = 0
  | [], _, _ => rfl
  | c :: L, hL, x => by
    rw [lAct_cons, orb_lAct_zero L (fun l hl => hL l (List.mem_cons_of_mem _ hl)),
      hL c List.mem_cons_self]
    simp

theorem orb_lAct_map {f : ℕ → ℕ} (hf : ∀ a < 2 ^ 16, ∀ b < 2 ^ 16, f (a ^^^ b) = f a ^^^ f b)
    (h0 : f 0 = 0) : ∀ (L : List ℕ), (∀ l ∈ L, l < 2 ^ 16) → ∀ x, f (lAct L x) = lAct (L.map f) x
  | [], _, _ => h0
  | c :: L, hL, x => by
    have hL' : ∀ l ∈ L, l < 2 ^ 16 := fun l hl => hL l (List.mem_cons_of_mem _ hl)
    have hi : (if x.testBit 0 = true then c else 0) < 2 ^ 16 := by
      split_ifs
      · exact hL c List.mem_cons_self
      · exact Nat.two_pow_pos 16
    rw [List.map_cons, lAct_cons, lAct_cons, hf _ hi _ (CFSG.KC.P0Vis.lAct_lt L hL' _),
      orb_lAct_map hf h0 L hL' (x / 2)]
    congr 1
    split_ifs
    · rfl
    · exact h0

theorem orb_lAct_map' {f : ℕ → ℕ} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (h0 : f 0 = 0) :
    ∀ (L : List ℕ) (x : ℕ), f (lAct L x) = lAct (L.map f) x
  | [], _ => h0
  | c :: L, x => by
    rw [List.map_cons, lAct_cons, lAct_cons, hf, orb_lAct_map' hf h0 L (x / 2)]
    congr 1
    split_ifs
    · rfl
    · exact h0

theorem orb_lAct_append : ∀ (a b : List ℕ) (x : ℕ),
    lAct (a ++ b) x = lAct a x ^^^ lAct b (x / 2 ^ a.length)
  | [], b, x => by
    rw [List.nil_append, List.length_nil, pow_zero, Nat.div_one]
    exact (Nat.zero_xor _).symm
  | c :: a, b, x => by
    rw [List.cons_append, lAct_cons, lAct_cons, orb_lAct_append a b, List.length_cons,
      Nat.div_div_eq_div_mul, ← pow_succ']
    ac_rfl

theorem orb_lAct_mod : ∀ (L : List ℕ) (x : ℕ), lAct L x = lAct L (x % 2 ^ L.length)
  | [], _ => rfl
  | c :: L, x => by
    have h1 : (x % 2 ^ (L.length + 1)).testBit 0 = x.testBit 0 := by
      rw [Nat.testBit_mod_two_pow]
      simp
    have h2 : x % 2 ^ (L.length + 1) / 2 = x / 2 % 2 ^ L.length := by
      rw [pow_succ', Nat.mod_mul_right_div_self]
    rw [List.length_cons, lAct_cons, lAct_cons, h1, h2, ← orb_lAct_mod L]

theorem orb_lAct_two_pow : ∀ (L : List ℕ) (j : ℕ) (hj : j < L.length), lAct L (2 ^ j) = L[j]
  | [], j, hj => absurd hj (by simp)
  | c :: L, 0, _ => by
    rw [lAct_cons]
    simp [lAct_zero]
  | c :: L, j + 1, hj => by
    rw [lAct_cons, pow_succ', Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
      orb_lAct_two_pow L j (by simpa using hj)]
    have hb : (2 * 2 ^ j).testBit 0 = false := by
      rw [Nat.testBit_zero, decide_eq_false_iff_not]
      omega
    rw [hb]
    simp

theorem orb_lAct_pows : ∀ (n y : ℕ), lAct ((List.range n).map (2 ^ ·)) y = y % 2 ^ n
  | 0, y => by
    rw [List.range_zero, List.map_nil, pow_zero, Nat.mod_one]
    rfl
  | n + 1, y => by
    rw [List.range_succ, List.map_append, orb_lAct_append, orb_lAct_pows n, List.length_map,
      List.length_range, List.map_singleton, lAct_cons, Nat.testBit_div_two_pow, Nat.zero_add]
    change y % 2 ^ n ^^^ ((if y.testBit n = true then 2 ^ n else 0) ^^^ 0) = y % 2 ^ (n + 1)
    rw [Nat.xor_zero]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    rcases Nat.lt_trichotomy i n with hin | rfl | hin
    · have h1 : n ≠ i := by omega
      have h2 : i < n + 1 := by omega
      split_ifs <;> simp [hin, h1, h2, Nat.testBit_two_pow]
    · split_ifs with hb <;> simp [hb, Nat.testBit_two_pow]
    · have h1 : n ≠ i := by omega
      have h2 : ¬ i < n + 1 := by omega
      have h3 : ¬ i < n := by omega
      split_ifs <;> simp [h1, h2, h3, Nat.testBit_two_pow]

theorem orb_xor_solve {a b c s : ℕ} (h : a ^^^ b ^^^ c = s) : c = s ^^^ a ^^^ b := by
  subst h
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

theorem orb_qOK {P Q : List ℕ} (h : qOK P Q = true) :
    P.length = 16 ∧ ∀ y < 2 ^ 16, lAct P (lAct Q y % 2 ^ 16) = y := by
  unfold qOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hP, hQ⟩, hj⟩ := h
  have hm : Q.map (lAct P) = (List.range 16).map (2 ^ ·) := by
    apply List.ext_getElem
    · simp [hQ]
    · intro j h1 _
      have hj' : j < Q.length := by simpa using h1
      rw [List.getElem_map, List.getElem_map, List.getElem_range, ← hj j (by omega),
        List.getD_eq_getElem _ _ hj']
  refine ⟨hP, fun y hy => ?_⟩
  have e1 := orb_lAct_mod P (lAct Q y)
  rw [hP] at e1
  rw [← e1, orb_lAct_map' (lAct_xor P) (lAct_zero P), hm, orb_lAct_pows, Nat.mod_eq_of_lt hy]

theorem orb_basis {P Q : List ℕ} (h : qOK P Q = true) :
    Set.InjOn (lAct P) ↑(Finset.range (2 ^ 16)) ∧ ∀ x < 2 ^ 16, lAct P x < 2 ^ 16 := by
  have hsur := (orb_qOK h).2
  have hsub : Finset.range (2 ^ 16) ⊆ (Finset.range (2 ^ 16)).image (lAct P) := fun y hy =>
    Finset.mem_image.2 ⟨lAct Q y % 2 ^ 16, Finset.mem_range.2 (Nat.mod_lt _ (Nat.two_pow_pos 16)),
      hsur y (Finset.mem_range.1 hy)⟩
  have heq : Finset.range (2 ^ 16) = (Finset.range (2 ^ 16)).image (lAct P) :=
    Finset.eq_of_subset_of_card_le hsub Finset.card_image_le
  refine ⟨Finset.card_image_iff.1 (by rw [← heq]), fun x hx => ?_⟩
  have hm : lAct P x ∈ (Finset.range (2 ^ 16)).image (lAct P) :=
    Finset.mem_image_of_mem _ (Finset.mem_range.2 hx)
  rw [← heq] at hm
  exact Finset.mem_range.1 hm

theorem orb_sbasis (s : ℕ) : (sbasis s).length = s >>> 80 ∧ ∀ b ∈ sbasis s, b < 2 ^ 16 := by
  refine ⟨by rw [sbasis, List.length_map, List.length_range]; rfl, fun b hb => ?_⟩
  rw [sbasis, List.mem_map] at hb
  obtain ⟨k, -, rfl⟩ := hb
  have : fld s (16 * k) 65535 ≤ 65535 := Nat.and_le_right
  omega

theorem orb_bet_lAct_zero {BC y : ℕ} (hy : y < 2 ^ 16) (L : List ℕ) (hL16 : ∀ l ∈ L, l < 2 ^ 16)
    (hL : ∀ l ∈ L, bet BC y l = 0) (x : ℕ) : bet BC y (lAct L x) = 0 := by
  rw [orb_lAct_map (f := bet BC y) (fun a ha b hb => p0o_bet_xor_right BC hy ha hb)
    (p0o_bet_zero_right BC hy) L hL16]
  exact orb_lAct_zero _ (fun l hl => by
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    exact hL l0 hl0) x

theorem orb_ts {BC BU : ℕ} {beta : List (List ℕ)} (h : bcOK BC BU beta = true) :
    ∀ (L : List ℕ), (∀ l ∈ L, l < 2 ^ 16) → tsOK BC BU L = true →
      (∀ l ∈ L, qf BU l = 0) ∧ ∀ l ∈ L, ∀ l' ∈ L, bet BC l l' = 0
  | [], _, _ => ⟨fun l hl => absurd hl (by simp), fun l hl => absurd hl (by simp)⟩
  | a :: L, hlt, ht => by
    change (Nat.beq (qf BU a) 0 && L.all (fun b' => Nat.beq (bet BC a b') 0) &&
      tsOK BC BU L) = true at ht
    simp only [Bool.and_eq_true, List.all_eq_true, Nat.beq_eq] at ht
    obtain ⟨⟨hqa, hall⟩, hrest⟩ := ht
    have hLlt : ∀ l ∈ L, l < 2 ^ 16 := fun l hl => hlt l (List.mem_cons_of_mem _ hl)
    have ha := hlt a List.mem_cons_self
    obtain ⟨ihq, ihb⟩ := orb_ts h L hLlt hrest
    refine ⟨fun l hl => ?_, fun l hl l' hl' => ?_⟩
    · rcases List.mem_cons.1 hl with rfl | hl
      · exact hqa
      · exact ihq l hl
    · rcases List.mem_cons.1 hl with rfl | hlL <;> rcases List.mem_cons.1 hl' with rfl | hlL'
      · exact p0o_bet_self h ha
      · exact hall l' hlL'
      · rw [p0o_bet_comm h (hLlt l hlL) ha]
        exact hall l hlL
      · exact ihb l hlL l' hlL'

theorem orb_qf_lAct {BC BU : ℕ} {beta : List (List ℕ)} (h : bcOK BC BU beta = true) :
    ∀ (L : List ℕ), (∀ l ∈ L, l < 2 ^ 16) → (∀ l ∈ L, qf BU l = 0) →
      (∀ l ∈ L, ∀ l' ∈ L, bet BC l l' = 0) → ∀ x, qf BU (lAct L x) = 0
  | [], _, _, _, _ => p0o_qf_zero BU
  | a :: L, hlt, hq, hb, x => by
    have hLlt : ∀ l ∈ L, l < 2 ^ 16 := fun l hl => hlt l (List.mem_cons_of_mem _ hl)
    have ha := hlt a List.mem_cons_self
    have hy : lAct L (x / 2) < 2 ^ 16 := CFSG.KC.P0Vis.lAct_lt L hLlt _
    have hi : (if x.testBit 0 = true then a else 0) < 2 ^ 16 := by
      split_ifs
      · exact ha
      · exact Nat.two_pow_pos 16
    have hqi : qf BU (if x.testBit 0 = true then a else 0) = 0 := by
      split_ifs
      · exact hq a List.mem_cons_self
      · exact p0o_qf_zero BU
    have hbi : bet BC (if x.testBit 0 = true then a else 0) (lAct L (x / 2)) = 0 := by
      split_ifs
      · exact orb_bet_lAct_zero ha L hLlt
          (fun l hl => hb a List.mem_cons_self l (List.mem_cons_of_mem _ hl)) _
      · exact p0o_bet_zero_left BC _
    rw [lAct_cons, p0o_qf_xor h hi hy, hqi, hbi, orb_qf_lAct h L hLlt
      (fun l hl => hq l (List.mem_cons_of_mem _ hl))
      (fun l hl l' hl' => hb l (List.mem_cons_of_mem _ hl) l' (List.mem_cons_of_mem _ hl'))]
    rfl

theorem orb_or_shl (a r : ℕ) (ha : a < 2 ^ 9) : a ||| r <<< 9 = a ^^^ r <<< 9 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases hi : 9 ≤ i
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi))]
    simp
  · simp [hi]

theorem orb_fv_cons (BC b x : ℕ) (bs : List ℕ) :
    fv BC (b :: bs) x = bet BC b x ^^^ fv BC bs x <<< 9 :=
  orb_or_shl _ _ (p0o_bet_lt _ _ _)

theorem orb_fv_eq_zero (BC : ℕ) :
    ∀ (bs : List ℕ) (x : ℕ), fv BC bs x = 0 ↔ ∀ b ∈ bs, bet BC b x = 0
  | [], _ => ⟨fun _ b hb => absurd hb (by simp), fun _ => rfl⟩
  | b :: bs, x => by
    change bet BC b x ||| fv BC bs x <<< 9 = 0 ↔ _
    rw [Nat.or_eq_zero_iff, Nat.shiftLeft_eq, Nat.mul_eq_zero, orb_fv_eq_zero BC bs x,
      List.forall_mem_cons]
    simp

theorem orb_fv_xor (BC : ℕ) : ∀ (bs : List ℕ), (∀ b ∈ bs, b < 2 ^ 16) →
    ∀ x < 2 ^ 16, ∀ y < 2 ^ 16, fv BC bs (x ^^^ y) = fv BC bs x ^^^ fv BC bs y
  | [], _, _, _, _, _ => by
    change (0 : ℕ) = 0 ^^^ 0
    rw [Nat.xor_zero]
  | b :: bs, hbs, x, hx, y, hy => by
    rw [orb_fv_cons, orb_fv_cons, orb_fv_cons,
      orb_fv_xor BC bs (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb')) x hx y hy,
      p0o_bet_xor_right BC (hbs b List.mem_cons_self) hx hy, Nat.shiftLeft_xor_distrib]
    ac_rfl

theorem orb_lAct_testBit_false {p : ℕ} :
    ∀ (fs : List ℕ), (∀ g ∈ fs, g.testBit p = false) → ∀ x, (lAct fs x).testBit p = false
  | [], _, _ => Nat.zero_testBit p
  | f :: fs, h, x => by
    rw [lAct_cons, Nat.testBit_xor,
      orb_lAct_testBit_false fs (fun g hg => h g (List.mem_cons_of_mem _ hg))]
    split_ifs
    · rw [h f List.mem_cons_self]
      rfl
    · rw [Nat.zero_testBit]
      rfl

theorem orb_triOK_zero : ∀ (fs ps : List ℕ), triOK fs ps = true → ∀ x, lAct fs x = 0 →
    x % 2 ^ fs.length = 0
  | [], [], _, x, _ => Nat.mod_one x
  | [], _ :: _, h, _, _ => by simp [triOK] at h
  | _ :: _, [], h, _, _ => by simp [triOK] at h
  | f :: fs, p :: ps, h, x, hx => by
    change (f.testBit p && fs.all (fun g => !g.testBit p) && triOK fs ps) = true at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨hf, hg⟩, ht⟩ := h
    have hg' : ∀ g ∈ fs, g.testBit p = false := fun g hg'' => by simpa using hg g hg''
    rw [lAct_cons] at hx
    have hb := orb_lAct_testBit_false fs hg' (x / 2)
    have hx0 : x.testBit 0 = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rw [if_pos hc] at hx
      have := congrArg (fun v => v.testBit p) hx
      simp only [Nat.testBit_xor, hf, hb, Nat.zero_testBit] at this
      exact absurd this (by decide)
    rw [if_neg (by rw [hx0]; decide), Nat.zero_xor] at hx
    have ih := orb_triOK_zero fs ps ht (x / 2) hx
    have hx2 : x % 2 = 0 := by
      rw [Nat.testBit_zero, decide_eq_false_iff_not] at hx0
      omega
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero ih
    have e : x = 2 * (x / 2) := by omega
    rw [List.length_cons, pow_succ']
    exact Nat.mod_eq_zero_of_dvd ⟨k, by rw [e, hk, Nat.mul_assoc]⟩

theorem orb_redZ_fold : ∀ (B : List ℕ) (y : ℕ), ∃ x < 2 ^ B.length,
    B.foldl (fun y b => Nat.min y (Nat.xor y b)) y = y ^^^ lAct B x
  | [], y => ⟨0, by norm_num, (Nat.xor_zero y).symm⟩
  | b :: B, y => by
    obtain ⟨x', hx', he⟩ := orb_redZ_fold B (Nat.min y (Nat.xor y b))
    rw [List.foldl_cons, he]
    by_cases hle : y ≤ Nat.xor y b
    · have hm : Nat.min y (Nat.xor y b) = y := min_eq_left hle
      have hb : (2 * x').testBit 0 = false := by
        rw [Nat.testBit_zero, decide_eq_false_iff_not]
        omega
      refine ⟨2 * x', ?_, ?_⟩
      · rw [List.length_cons, pow_succ']
        omega
      · rw [lAct_cons, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), hb, hm]
        simp
    · have hm : Nat.min y (Nat.xor y b) = y ^^^ b := min_eq_right (by omega)
      have h1 : (2 * x' + 1) / 2 = x' := by omega
      have h2 : (2 * x' + 1).testBit 0 = true := by
        rw [Nat.testBit_zero, decide_eq_true_iff]
        omega
      refine ⟨2 * x' + 1, ?_, ?_⟩
      · rw [List.length_cons, pow_succ']
        omega
      · rw [lAct_cons, h1, h2, if_pos rfl, hm, Nat.xor_assoc]

theorem orb_redZ_mem {B : List ℕ} {y : ℕ} (h : redZ B y = true) : y ∈ spanF B := by
  obtain ⟨x, hx, he⟩ := orb_redZ_fold B y
  have h0 : B.foldl (fun y b => Nat.min y (Nat.xor y b)) y = 0 := Nat.eq_of_beq_eq_true h
  rw [he] at h0
  have hy : y = lAct B x := by
    have := congrArg (· ^^^ lAct B x) h0
    simpa [Nat.xor_assoc] using this
  exact Finset.mem_image.2 ⟨x, Finset.mem_range.2 hx, hy.symm⟩

theorem orb_fld_gRow (BC x : ℕ) : ∀ (c : List ℕ) (k : ℕ), k < c.length →
    fld (gRow BC c x) (9 * k) 511 = bet BC x (c.getD k 0)
  | [], k, hk => absurd hk (by simp)
  | y :: c, 0, _ => by
    change ((bet BC x y ||| gRow BC c x <<< 9) >>> (9 * 0)) &&& 511 = bet BC x y
    rw [CFSG.KC.P0Vis.or_shl_eq (p0o_bet_lt BC x y), Nat.mul_zero, Nat.shiftRight_zero]
    change (bet BC x y + 2 ^ 9 * gRow BC c x) &&& (2 ^ 9 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (p0o_bet_lt BC x y)]
  | y :: c, k + 1, hk => by
    change ((bet BC x y ||| gRow BC c x <<< 9) >>> (9 * (k + 1))) &&& 511 = bet BC x (c.getD k 0)
    have e : 9 * (k + 1) = 9 + 9 * k := by omega
    have e2 : (bet BC x y + 2 ^ 9 * gRow BC c x) >>> 9 = gRow BC c x := by
      rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 9),
        Nat.div_eq_of_lt (p0o_bet_lt BC x y), Nat.zero_add]
    rw [CFSG.KC.P0Vis.or_shl_eq (p0o_bet_lt BC x y), e, Nat.shiftRight_add, e2]
    exact orb_fld_gRow BC x c k (by simpa using hk)

theorem orb_cEntries_fst (BC BU : ℕ) (c : List ℕ) : (cEntries BC BU c).map Prod.fst = c := by
  apply List.ext_getElem
  · simp [cEntries]
  · intro j h1 h2
    simp only [cEntries, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply]
    exact List.getD_eq_getElem _ _ h2

theorem orb_gwalk_cons (AT RT d : ℕ) (bs : List ℕ) (e : ℕ × ℕ × ℕ × ℕ)
    (E : List (ℕ × ℕ × ℕ × ℕ)) (σ q v : ℕ) (recs : List (ℕ × ℕ)) :
    gwalk AT RT d bs (e :: E) σ q v recs =
      Option.rec (motive := fun _ => Option (List (ℕ × ℕ))) none
        (fun recs' => gwalk AT RT d bs E (Nat.xor σ e.1)
          (Nat.xor (Nat.xor q e.2.1) (fld v e.2.2.2 511)) (Nat.xor v e.2.2.1) recs')
        (gwalk AT RT d bs E σ q v recs) := rfl

theorem orb_gwalk_reach {AT RT d BC BU : ℕ} {bs : List ℕ} {beta : List (List ℕ)}
    (hbc : bcOK BC BU beta = true) :
    ∀ (E : List (ℕ × ℕ × ℕ × ℕ)), (∀ e ∈ E, e.1 < 2 ^ 16 ∧ e.2.1 = qf BU e.1 ∧
      ∀ e' ∈ E, fld e.2.2.1 e'.2.2.2 511 = bet BC e.1 e'.1) →
    ∀ (σ q v : ℕ) (recs l : List (ℕ × ℕ)), σ < 2 ^ 16 → q = qf BU σ →
      (∀ e ∈ E, fld v e.2.2.2 511 = bet BC σ e.1) → gwalk AT RT d bs E σ q v recs = some l →
      ∀ x, ∃ recs' l', leaf AT RT d bs (σ ^^^ lAct (E.map Prod.fst) x)
        (qf BU (σ ^^^ lAct (E.map Prod.fst) x)) recs' = some l'
  | [], _, σ, q, _, recs, l, _, hqσ, _, hg, _ => by
    refine ⟨recs, l, ?_⟩
    change leaf AT RT d bs (σ ^^^ 0) (qf BU (σ ^^^ 0)) recs = some l
    rw [Nat.xor_zero, ← hqσ]
    exact hg
  | e :: E, hE, σ, q, v, recs, l, hσ, hqσ, hv, hg, x => by
    have hE' : ∀ e ∈ E, e.1 < 2 ^ 16 ∧ e.2.1 = qf BU e.1 ∧
        ∀ e' ∈ E, fld e.2.2.1 e'.2.2.2 511 = bet BC e.1 e'.1 := fun e' he' => by
      obtain ⟨a, b, c⟩ := hE e' (List.mem_cons_of_mem _ he')
      exact ⟨a, b, fun e'' he'' => c e'' (List.mem_cons_of_mem _ he'')⟩
    obtain ⟨he1, heq, herow⟩ := hE e List.mem_cons_self
    rw [orb_gwalk_cons] at hg
    rcases hg1 : gwalk AT RT d bs E σ q v recs with _ | recs1
    · rw [hg1] at hg
      cases hg
    rw [hg1] at hg
    change gwalk AT RT d bs E (Nat.xor σ e.1) _ _ recs1 = some l at hg
    rw [List.map_cons, lAct_cons]
    by_cases hx0 : x.testBit 0 = true
    · rw [if_pos hx0, ← Nat.xor_assoc]
      refine orb_gwalk_reach hbc E hE' (σ ^^^ e.1) _ _ recs1 l (Nat.xor_lt_two_pow hσ he1) ?_
        (fun e' he' => ?_) hg (x / 2)
      · rw [p0o_qf_xor hbc hσ he1, hqσ, heq, hv e List.mem_cons_self]
        rfl
      · obtain ⟨he'1, -, -⟩ := hE e' (List.mem_cons_of_mem _ he')
        change ((v ^^^ e.2.2.1) >>> e'.2.2.2) &&& 511 = _
        rw [p0b_g_lin, p0o_bet_xor_left BC hσ he1 he'1]
        exact congrArg₂ (· ^^^ ·) (hv e' (List.mem_cons_of_mem _ he'))
          (herow e' (List.mem_cons_of_mem _ he'))
    · rw [if_neg hx0, Nat.zero_xor]
      exact orb_gwalk_reach hbc E hE' σ q v recs recs1 hσ hqσ
        (fun e' he' => hv e' (List.mem_cons_of_mem _ he')) hg1 (x / 2)

theorem orb_leaf_rec {AT RT d : ℕ} {bs : List ℕ} {σ : ℕ} {recs l : List (ℕ × ℕ)} (hσ : σ ≠ 0)
    (h : leaf AT RT d bs σ 0 recs = some l) : ∃ r, recOK AT RT d bs σ r = true := by
  unfold leaf at h
  have hb : Nat.beq σ 0 = false := by
    cases hh : Nat.beq σ 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hh) hσ
  rw [hb] at h
  cases recs with
  | nil =>
    change (none : Option (List (ℕ × ℕ))) = some l at h
    cases h
  | cons r rest =>
    refine ⟨r, ?_⟩
    change (bif recOK AT RT d bs σ r then some rest else none) = some l at h
    cases hr : recOK AT RT d bs σ r
    · rw [hr] at h
      cases h
    · rfl

theorem orb_core {AT RT BC BU N d : ℕ} {beta : List (List ℕ)} {bs c w Q piv : List ℕ}
    {recs : List (ℕ × ℕ)} (hbc : bcOK BC BU beta = true) (hrt : rtOK RT N = true)
    (hbsl : bs.length = d) (hbs : ∀ b ∈ bs, b < 2 ^ 16) (hts : tsOK BC BU bs = true)
    (hdim : Nat.beq (d + c.length + w.length) 16 = true) (hq : qOK (bs ++ c ++ w) Q = true)
    (hc : c.all (fun x => Nat.beq (fv BC bs x) 0) = true)
    (htri : triOK (w.map (fv BC bs)) piv = true)
    (hwalk : Option.rec (motive := fun _ => Bool) false (fun l => l.isEmpty)
      (gwalk AT RT d bs (cEntries BC BU c) 0 0 0 recs) = true) :
    (spanF bs).card = 2 ^ d ∧ ∀ σ < 2 ^ 16, (∀ y ∈ spanF bs, bet BC y σ = 0) → qf BU σ = 0 →
      σ ∉ spanF bs → ∃ lam < 2 ^ 10, ∃ r' < N, slot RT r' >>> 80 = d + 1 ∧
        aAct AT lam σ ∈ spanF (sbasis (slot RT r')) ∧
        ∀ y ∈ spanF bs, aAct AT lam y ∈ spanF (sbasis (slot RT r')) := by
  have hd16 : d + c.length + w.length = 16 := Nat.eq_of_beq_eq_true hdim
  obtain ⟨hPl, hPQ⟩ := orb_qOK hq
  obtain ⟨hinj, hPlt⟩ := orb_basis hq
  have hP16 : ∀ p ∈ bs ++ c ++ w, p < 2 ^ 16 := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    rw [← orb_lAct_two_pow _ j hj]
    exact hPlt _ (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hc16 : ∀ x ∈ c, x < 2 ^ 16 := fun x hx =>
    hP16 x (List.mem_append_left _ (List.mem_append_right _ hx))
  have hw16 : ∀ x ∈ w, x < 2 ^ 16 := fun x hx => hP16 x (List.mem_append_right _ hx)
  have hcf : ∀ x ∈ c, ∀ b ∈ bs, bet BC b x = 0 := fun x hx =>
    (orb_fv_eq_zero BC bs x).1 (Nat.eq_of_beq_eq_true (List.all_eq_true.1 hc x hx))
  obtain ⟨hsq, hiso⟩ := orb_ts hbc bs hbs hts
  have hlP : ∀ x, lAct (bs ++ c ++ w) x =
      lAct bs x ^^^ lAct c (x / 2 ^ d) ^^^ lAct w (x / 2 ^ (d + c.length)) := by
    intro x
    rw [orb_lAct_append, orb_lAct_append, List.length_append, hbsl]
  refine ⟨?_, ?_⟩
  ·
    have e : ∀ z < 2 ^ d, lAct (bs ++ c ++ w) z = lAct bs z := fun z hz => by
      rw [hlP, Nat.div_eq_of_lt hz,
        Nat.div_eq_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by norm_num) (by omega))),
        lAct_zero, lAct_zero, Nat.xor_zero, Nat.xor_zero]
    have h16 : 2 ^ d ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [spanF, Finset.card_image_of_injOn, Finset.card_range, hbsl]
    intro x hx y hy hxy
    rw [hbsl] at hx hy
    have hx' : x < 2 ^ d := Finset.mem_range.1 (Finset.mem_coe.1 hx)
    have hy' : y < 2 ^ d := Finset.mem_range.1 (Finset.mem_coe.1 hy)
    refine hinj (Finset.mem_coe.2 (Finset.mem_range.2 (lt_of_lt_of_le hx' h16)))
      (Finset.mem_coe.2 (Finset.mem_range.2 (lt_of_lt_of_le hy' h16))) ?_
    rw [e x hx', e y hy']
    exact hxy
  · intro σ hσ hperp hqσ hnot
    obtain ⟨z, hz⟩ : ∃ z, lAct (bs ++ c ++ w) z = σ := ⟨_, hPQ σ hσ⟩
    rw [hlP] at hz
    have hρmem : lAct bs z ∈ spanF bs := orb_lAct_mem (spanF_xorClosed bs) bs (mem_spanF bs) z
    have hρ16 : lAct bs z < 2 ^ 16 := CFSG.KC.P0Vis.lAct_lt bs hbs z
    have hσc16 : lAct c (z / 2 ^ d) < 2 ^ 16 := CFSG.KC.P0Vis.lAct_lt c hc16 _
    have hw0 : lAct w (z / 2 ^ (d + c.length)) = 0 := by
      have hfv : fv BC bs (lAct w (z / 2 ^ (d + c.length))) = 0 := by
        rw [orb_fv_eq_zero]
        intro b hb
        have hb16 := hbs b hb
        rw [orb_xor_solve hz, p0o_bet_xor_right BC hb16 (Nat.xor_lt_two_pow hσ hρ16) hσc16,
          p0o_bet_xor_right BC hb16 hσ hρ16, hperp b (mem_spanF bs b hb),
          orb_bet_lAct_zero hb16 bs hbs (hiso b hb) z,
          orb_bet_lAct_zero hb16 c hc16 (fun x hx => hcf x hx b hb) _]
        rfl
      have hfv0 : fv BC bs 0 = 0 :=
        (orb_fv_eq_zero BC bs 0).2 fun b hb => p0o_bet_zero_right BC (hbs b hb)
      rw [orb_lAct_map (orb_fv_xor BC bs hbs) hfv0 w hw16] at hfv
      have h0 := orb_triOK_zero _ _ htri _ hfv
      rw [List.length_map] at h0
      rw [orb_lAct_mod, h0]
      exact lAct_zero w
    rw [hw0, Nat.xor_zero] at hz
    have hσc : lAct c (z / 2 ^ d) = lAct bs z ^^^ σ := by
      rw [← hz, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    have hσc0 : lAct c (z / 2 ^ d) ≠ 0 := by
      intro h0
      apply hnot
      rw [← hz, h0, Nat.xor_zero]
      exact hρmem
    have hqc : qf BU (lAct c (z / 2 ^ d)) = 0 := by
      rw [hσc, p0o_qf_xor hbc hρ16 hσ, orb_qf_lAct hbc bs hbs hsq hiso z, hqσ, hperp _ hρmem]
      rfl
    rcases hg : gwalk AT RT d bs (cEntries BC BU c) 0 0 0 recs with _ | l
    · rw [hg] at hwalk
      cases hwalk
    have hent : ∀ e ∈ cEntries BC BU c, e.1 < 2 ^ 16 ∧ e.2.1 = qf BU e.1 ∧
        ∀ e' ∈ cEntries BC BU c, fld e.2.2.1 e'.2.2.2 511 = bet BC e.1 e'.1 := by
      intro e he
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
      have hj' := List.mem_range.1 hj
      refine ⟨hc16 _ (by rw [List.getD_eq_getElem _ _ hj']; exact List.getElem_mem _), rfl,
        fun e' he' => ?_⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 he'
      exact orb_fld_gRow BC _ c k (List.mem_range.1 hk)
    have hreach := orb_gwalk_reach (AT := AT) (RT := RT) (d := d) (bs := bs) hbc
      (cEntries BC BU c) hent 0 0 0 recs l (Nat.two_pow_pos 16) (p0o_qf_zero BU).symm
      (fun e _ => by
        rw [p0o_bet_zero_left]
        change (0 >>> e.2.2.2) &&& 511 = 0
        rw [Nat.zero_shiftRight, Nat.zero_and]) hg (z / 2 ^ d)
    rw [orb_cEntries_fst, Nat.zero_xor, hqc] at hreach
    obtain ⟨recs', l', hleaf⟩ := hreach
    obtain ⟨r0, hr0⟩ := orb_leaf_rec hσc0 hleaf
    have hr' : (Nat.blt r0.1 1024 && (Nat.beq (slot RT r0.2 >>> 80) (d + 1) &&
        (redZ (sbasis (slot RT r0.2)) (aAct AT r0.1 (lAct c (z / 2 ^ d))) &&
          bs.all fun b => redZ (sbasis (slot RT r0.2)) (aAct AT r0.1 b)))) = true := hr0
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, List.all_eq_true] at hr'
    obtain ⟨hlam, hdim', hσred, hbred⟩ := hr'
    have hrtl : RT < 2 ^ (96 * N) := by
      have h2 := hrt
      simp only [rtOK, Bool.and_eq_true, Nat.blt_eq] at h2
      exact h2.2
    have hr'N : r0.2 < N := by
      by_contra hge
      have hs0 : slot RT r0.2 = 0 := by
        change (RT >>> (96 * r0.2)) &&& m96 = 0
        rw [Nat.shiftRight_eq_zero _ _ (lt_of_lt_of_le hrtl
          (Nat.pow_le_pow_right (by norm_num) (by omega))), Nat.zero_and]
      rw [hs0, Nat.zero_shiftRight] at hdim'
      omega
    have hspan : ∀ x, aAct AT r0.1 (lAct bs x) ∈ spanF (sbasis (slot RT r0.2)) := fun x => by
      rw [orb_lAct_map (f := aAct AT r0.1) (fun a ha b hb => p0o_aAct_xor AT r0.1 ha hb)
        (p0o_aAct_zero AT r0.1) bs hbs]
      exact orb_lAct_mem (spanF_xorClosed _) _ (fun l hl => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hl
        exact orb_redZ_mem (hbred b hb)) x
    refine ⟨r0.1, lt_of_lt_of_eq hlam (by norm_num), r0.2, hr'N, hdim', ?_, ?_⟩
    · rw [← hz, p0o_aAct_xor AT r0.1 hρ16 hσc16]
      exact (spanF_xorClosed _).2 _ (hspan z) _ (orb_redZ_mem hσred)
    · intro y hy
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
      exact hspan x

theorem repOK_facts {AT RT BC BU N r : ℕ} {beta : List (List ℕ)} {row : Row}
    (hbc : bcOK BC BU beta = true) (hrt : rtOK RT N = true)
    (h : repOK AT RT BC BU r row = true) : RepFacts AT RT BC BU N r := by
  obtain ⟨c, w, Q, piv, recs⟩ := row
  have h' : (tsOK BC BU (sbasis (slot RT r)) &&
      Nat.beq (slot RT r >>> 80 + c.length + w.length) 16 &&
      qOK (sbasis (slot RT r) ++ c ++ w) Q &&
      c.all (fun x => Nat.beq (fv BC (sbasis (slot RT r)) x) 0) &&
      triOK (w.map (fv BC (sbasis (slot RT r)))) piv &&
      Option.rec (motive := fun _ => Bool) false (fun l => l.isEmpty)
        (gwalk AT RT (slot RT r >>> 80) (sbasis (slot RT r)) (cEntries BC BU c) 0 0 0 recs)) =
      true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨hts, hdim⟩, hq⟩, hc⟩, htri⟩, hwalk⟩ := h'
  obtain ⟨hcard, hext⟩ := orb_core hbc hrt (orb_sbasis _).1 (orb_sbasis _).2 hts hdim hq hc htri
    hwalk
  exact ⟨hcard, hext⟩

theorem slot_zero_dim {RT : ℕ} (h0 : slot RT 0 = 0) : sbasis (slot RT 0) = [] := by
  rw [h0]
  rfl

section Induction

variable {AT RT BC BU N : ℕ}
  (hrep : ∀ r < N, RepFacts AT RT BC BU N r) (h0 : slot RT 0 = 0) (hN : 0 < N)
  (hA0 : ∀ x < 2 ^ 16, aAct AT 0 x = x)
  (hAc : ∀ κ < 2 ^ 10, ∀ μ < 2 ^ 10, ∀ x < 2 ^ 16,
    aAct AT κ (aAct AT μ x) = aAct AT (κ ^^^ μ) x)
  (hAlt : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, aAct AT κ x < 2 ^ 16)
  (hAlin : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, ∀ y < 2 ^ 16,
    aAct AT κ (x ^^^ y) = aAct AT κ x ^^^ aAct AT κ y)
  (hAq : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, qf BU x = 0 → qf BU (aAct AT κ x) = 0)
  (hAβ : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, ∀ y < 2 ^ 16,
    bet BC x y = 0 → bet BC (aAct AT κ x) (aAct AT κ y) = 0)
include hrep h0 hN hA0 hAc hAlt hAlin hAq hAβ

theorem orbit_complete : ∀ (n : ℕ) (D : Finset ℕ), D.card = n → XorClosed D →
    (∀ x ∈ D, x < 2 ^ 16) → (∀ x ∈ D, qf BU x = 0) → (∀ x ∈ D, ∀ y ∈ D, bet BC x y = 0) →
    ∃ lam < 2 ^ 10, ∃ r < N, D.image (aAct AT lam) = spanF (sbasis (slot RT r)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D hcard hD hD16 hDq hDβ
  have hinv : ∀ μ < 2 ^ 10, ∀ y < 2 ^ 16, aAct AT μ (aAct AT μ y) = y := fun μ hμ y hy => by
    rw [hAc μ hμ μ hμ y hy, Nat.xor_self, hA0 y hy]
  have hinj : ∀ μ < 2 ^ 10, Set.InjOn (aAct AT μ) (D : Set ℕ) := by
    intro μ hμ x hx y hy hxy
    have := congrArg (aAct AT μ) hxy
    rwa [hinv μ hμ x (hD16 x hx), hinv μ hμ y (hD16 y hy)] at this
  by_cases hz : ∀ x ∈ D, x = 0
  ·
    refine ⟨0, by norm_num, 0, hN, ?_⟩
    rw [slot_zero_dim h0, spanF_nil]
    ext y
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hz x hx, hA0 0 (by norm_num)]
    · rintro rfl
      exact ⟨0, hD.1, hA0 0 (by norm_num)⟩
  simp only [not_forall] at hz
  obtain ⟨v₀, hv₀D, hv₀⟩ := hz
  have hne : D.Nonempty := ⟨v₀, hv₀D⟩
  set v := D.max' hne with hvdef
  have hvD : v ∈ D := Finset.max'_mem D hne
  have hv0 : v ≠ 0 := by
    have := Finset.le_max' D v₀ hv₀D
    omega
  set t := Nat.log2 v
  have hvt : v.testBit t = true := Nat.testBit_log2 hv0
  have hlt : ∀ x ∈ D, x < 2 ^ (t + 1) := fun x hx =>
    lt_of_le_of_lt (Finset.le_max' D x hx) Nat.lt_log2_self
  set D' := D.filter (fun x => x.testBit t = false) with hD'def
  have hD'sub : D' ⊆ D := Finset.filter_subset _ _
  have hD' : XorClosed D' := by
    refine ⟨Finset.mem_filter.2 ⟨hD.1, Nat.zero_testBit t⟩, ?_⟩
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb ⊢
    refine ⟨hD.2 a ha.1 b hb.1, ?_⟩
    rw [Nat.testBit_xor, ha.2, hb.2]
    rfl
  have hvD' : v ∉ D' := by
    rw [Finset.mem_filter]
    rintro ⟨-, h⟩
    rw [hvt] at h
    exact Bool.noConfusion h
  have hsplit : D.filter (fun x => ¬ x.testBit t = false) = D'.image (v ^^^ ·) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hx, hxt⟩
      have hb : (v ^^^ x).testBit t = false := by
        rw [Nat.testBit_xor, hvt]
        cases h : x.testBit t
        · exact absurd h hxt
        · rfl
      refine ⟨v ^^^ x, Finset.mem_filter.2 ⟨hD.2 v hvD x hx, hb⟩, ?_⟩
      rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    · rintro ⟨y, hy, rfl⟩
      rw [Finset.mem_filter] at hy
      refine ⟨hD.2 v hvD y hy.1, ?_⟩
      rw [Nat.testBit_xor, hvt, hy.2]
      simp
  have hcardD : D.card = 2 * D'.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := D) (p := fun x => x.testBit t = false),
      hsplit, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    have he : (D.filter fun x => x.testBit t = false).card = D'.card := rfl
    omega
  have hD'pos : 0 < D'.card := Finset.card_pos.2 ⟨0, hD'.1⟩
  obtain ⟨μ, hμ, r, hr, himg⟩ := ih D'.card (by omega) D' rfl hD'
    (fun x hx => hD16 x (hD'sub hx)) (fun x hx => hDq x (hD'sub hx))
    (fun x hx y hy => hDβ x (hD'sub hx) y (hD'sub hy))
  set R := spanF (sbasis (slot RT r))
  have hv16 := hD16 v hvD
  set w := aAct AT μ v
  have hw16 : w < 2 ^ 16 := hAlt μ hμ v hv16
  have hmemR : ∀ x ∈ D', aAct AT μ x ∈ R := fun x hx => by
    rw [← himg]
    exact Finset.mem_image_of_mem _ hx
  have hRmem : ∀ y ∈ R, ∃ x ∈ D', aAct AT μ x = y := fun y hy => by
    rw [← himg] at hy
    exact Finset.mem_image.1 hy
  have hperp : ∀ y ∈ R, bet BC y w = 0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hRmem y hy
    exact hAβ μ hμ x (hD16 x (hD'sub hx)) v hv16 (hDβ x (hD'sub hx) v hvD)
  have hwq : qf BU w = 0 := hAq μ hμ v hv16 (hDq v hvD)
  have hwR : w ∉ R := by
    intro hw
    obtain ⟨x, hx, hxw⟩ := hRmem w hw
    have := congrArg (aAct AT μ) hxw
    rw [hinv μ hμ x (hD16 x (hD'sub hx)), hinv μ hμ v hv16] at this
    exact hvD' (this ▸ hx)
  obtain ⟨lam, hlam, r', hr', hdim, hlw, hlR⟩ := (hrep r hr).ext w hw16 hperp hwq hwR
  set R' := spanF (sbasis (slot RT r'))
  have hκ : lam ^^^ μ < 2 ^ 10 := Nat.xor_lt_two_pow hlam hμ
  refine ⟨lam ^^^ μ, hκ, r', hr', ?_⟩
  have hsub : D.image (aAct AT (lam ^^^ μ)) ⊆ R' := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hx16 := hD16 x hx
    rw [← hAc lam hlam μ hμ x hx16]
    by_cases hxt : x.testBit t = false
    · exact hlR _ (hmemR x (Finset.mem_filter.2 ⟨hx, hxt⟩))
    · have hx' : v ^^^ x ∈ D' := by
        have : x ∈ D'.image (v ^^^ ·) := by
          rw [← hsplit]
          exact Finset.mem_filter.2 ⟨hx, hxt⟩
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 this
        rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hxe : x = v ^^^ (v ^^^ x) := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hvx16 : v ^^^ x < 2 ^ 16 := Nat.xor_lt_two_pow hv16 hx16
      rw [hxe, hAlin μ hμ v hv16 _ hvx16,
        hAlin lam hlam _ hw16 _ (hAlt μ hμ _ hvx16)]
      exact (spanF_xorClosed _).2 _ hlw _ (hlR _ (hmemR _ hx'))
  refine Finset.eq_of_subset_of_card_le hsub ?_
  have hD'c : (D'.image (aAct AT μ)).card = 2 ^ (slot RT r >>> 80) := by
    rw [himg]
    exact (hrep r hr).card
  rw [Finset.card_image_of_injOn
    (fun x hx y hy h => hinj μ hμ (hD'sub hx) (hD'sub hy) h)] at hD'c
  rw [(hrep r' hr').card, hdim, Finset.card_image_of_injOn (hinj _ hκ), hcardD, hD'c, pow_succ,
    Nat.mul_comm]

end Induction

end CFSG.KC.P0Orb

end
