module

public import Certificates.Data.FzL410Model
public import Certificates.Data.Kernel.FzL410M.Codes
public import CFSG.Certificates.Kernel.FzL410.Norm
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

namespace CFSG.FzL410KM

open Certificates.FzL410 Certificates.FzL410.K Certificates.FzL410.KM CFSG.FzL410K

theorem bE_iff {a b : Bool} : bE a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp [bE, bN]

theorem allL_iff {f : ℕ → Bool} : ∀ {L : List ℕ}, allL L f = true ↔ ∀ x ∈ L, f x = true
  | [] => by simp [allL]
  | x :: L => by
    have e : allL (x :: L) f = bA (f x) (allL L f) := rfl
    rw [e, bA_iff, allL_iff]
    simp

theorem anyL_iff {f : ℕ → Bool} : ∀ {L : List ℕ}, anyL L f = true ↔ ∃ x ∈ L, f x = true
  | [] => by simp [anyL]
  | x :: L => by
    have e : anyL (x :: L) f = bO (f x) (anyL L f) := rfl
    rw [e, bO_iff, anyL_iff]
    simp

theorem inL_iff {L : List ℕ} {v : ℕ} : inL L v = true ↔ v ∈ L := by
  unfold inL
  rw [anyL_iff]
  simp [Nat.beq_eq]

theorem sumR_eq (f : ℕ → ℕ) : ∀ n, sumR n f = ∑ k ∈ Finset.range n, f k
  | 0 => rfl
  | n + 1 => by
    have e : sumR (n + 1) f = f n + sumR n f := rfl
    rw [e, sumR_eq f n, Finset.sum_range_succ, Nat.add_comm]

theorem bit_iff (M k : ℕ) : bit M k = true ↔ M.testBit k = true := by
  have hs : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k
  unfold bit
  rw [hs, Nat.blt_eq]
  constructor
  · intro h
    by_contra hb
    have h0 : Nat.land M (2 ^ k) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      change (M &&& 2 ^ k).testBit i = (0 : ℕ).testBit i
      rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
      by_cases hi : k = i
      · subst hi
        simpa using hb
      · simp [hi]
    omega
  · intro h
    have ht : (M &&& 2 ^ k).testBit k = true := by
      rw [Nat.testBit_and, h, Nat.testBit_two_pow_self]
      rfl
    rcases Nat.eq_zero_or_pos (Nat.land M (2 ^ k)) with h0 | h0
    · change M &&& 2 ^ k = 0 at h0
      rw [h0, Nat.zero_testBit] at ht
      exact absurd ht Bool.false_ne_true
    · exact h0

theorem slices {f : ℕ → Bool} (s len : ℕ) (h : ∀ i < s, ∀ j < len, f (len * i + j) = true) :
    ∀ k < s * len, f k = true := by
  intro k hk
  have hlen : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | h0
    · subst h0
      simp at hk
    · exact h0
  have e : len * (k / len) + k % len = k := Nat.div_add_mod k len
  rw [← e]
  refine h _ ?_ _ (Nat.mod_lt _ hlen)
  rw [Nat.div_lt_iff_lt_mul hlen]
  linarith [Nat.mul_comm s len]

theorem castEq {n : ℕ} {a b : ℕ} (h : a % n = b % n) : (a : ZMod n) = b :=
  (ZMod.natCast_eq_natCast_iff' a b n).2 h

theorem addA_lanes : ∀ k < 64, ∀ l < 64, addA k l % 4 = (k + l) % 4 ∧
    addA k l / 4 % 4 = (k / 4 + l / 4) % 4 ∧ addA k l / 16 % 2 = (k / 16 + l / 16) % 2 ∧
    addA k l / 32 % 2 = (k / 32 + l / 32) % 2 ∧ addA k l < 64 := by decide +kernel

theorem lanes_lt (a b c d : ℕ) (ha : a < 4) (hb : b < 4) (hc : c < 2) (hd : d < 2) :
    Nat.add a (Nat.add (Nat.mul 4 b) (Nat.add (Nat.mul 16 c) (Nat.mul 32 d))) < 64 := by
  simp only [nA, nM]
  omega

theorem addA_lt (k l : ℕ) : addA k l < 64 :=
  lanes_lt _ _ _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))

theorem dec_addA {k l : ℕ} (hk : k < 64) (hl : l < 64) : dec (addA k l) = dec k + dec l := by
  obtain ⟨h1, h2, h3, h4, -⟩ := addA_lanes k hk l hl
  simp only [dec, Prod.mk_add_mk, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Nat.cast_add]
    exact castEq h1
  · rw [← Nat.cast_add]
    exact castEq h2
  · rw [← Nat.cast_add]
    exact castEq h3
  · rw [← Nat.cast_add]
    exact castEq h4

def dV (w : ℕ) : V := ((w : ZMod 2), ((w / 2 : ℕ) : ZMod 2), ((w / 4 : ℕ) : ZMod 2))

def cV (v : V) : ℕ := v.1.val + 2 * v.2.1.val + 4 * v.2.2.val

theorem cV_lt : ∀ v : V, cV v < 8 := by decide
theorem dV_cV : ∀ v : V, dV (cV v) = v := by decide
theorem cV_dV : ∀ w < 8, cV (dV w) = w := by decide

theorem dec_actA : ∀ w < 8, ∀ q < 64, dec (actA w q) = act (dV w) (dec q) := by decide +kernel
theorem actA_lt : ∀ w < 8, ∀ q < 64, actA w q < 64 := by decide +kernel
theorem dV_addV : ∀ v < 8, ∀ w < 8, dV (addV v w) = dV v + dV w := by decide +kernel
theorem addV_lt : ∀ v < 8, ∀ w < 8, addV v w < 8 := by decide +kernel
theorem addV_lt4 : ∀ v < 4, ∀ w < 4, addV v w < 4 := by decide +kernel

theorem actT_eq (h : actOK = true) {w q : ℕ} (hw : w < 8) (hq : q < 64) : actT w q = actA w q :=
  Nat.eq_of_beq_eq_true (allR_iff.1 (allR_iff.1 h w hw) q hq)

def dT (k : ℕ) : TM := (dec (k % 64), dV (k / 64))

def eT (x : TM) : ℕ := cmp x.1 + 64 * cV x.2

theorem eT_lt (x : TM) : eT x < 512 := by
  have := cmp_lt x.1
  have := cV_lt x.2
  unfold eT
  omega

theorem dT_eT (x : TM) : dT (eT x) = x := by
  have h1 := cmp_lt x.1
  have h2 := cV_lt x.2
  have e1 : eT x % 64 = cmp x.1 := by unfold eT; omega
  have e2 : eT x / 64 = cV x.2 := by unfold eT; omega
  unfold dT
  rw [e1, e2, dec_cmp, dV_cV]

theorem eT_dT {k : ℕ} (hk : k < 512) : eT (dT k) = k := by
  change cmp (dec (k % 64)) + 64 * cV (dV (k / 64)) = k
  rw [cmp_dec _ (Nat.mod_lt _ (by norm_num)), cV_dV _ (by omega)]
  omega

theorem dT_inj {k l : ℕ} (hk : k < 512) (hl : l < 512) : dT k = dT l ↔ k = l := by
  constructor
  · intro h
    rw [← eT_dT hk, ← eT_dT hl, h]
  · rintro rfl
    rfl

theorem mulN_eq (m n : ℕ) : mulN m n = addA (m % 64) (actT (m / 64) (n % 64)) +
    64 * addV (m / 64) (n / 64) := rfl

theorem mulN_lt {m n : ℕ} (hm : m < 512) (hn : n < 512) : mulN m n < 512 := by
  have := addA_lt (m % 64) (actT (m / 64) (n % 64))
  have := addV_lt (m / 64) (by omega) (n / 64) (by omega)
  rw [mulN_eq]
  omega

theorem dT_mulN (h : actOK = true) {m n : ℕ} (hm : m < 512) (hn : n < 512) :
    dT (mulN m n) = mulT (dT m) (dT n) := by
  have ha := addA_lt (m % 64) (actT (m / 64) (n % 64))
  have hv := addV_lt (m / 64) (by omega) (n / 64) (by omega)
  have hq := actA_lt (m / 64) (by omega) (n % 64) (Nat.mod_lt _ (by norm_num))
  rw [actT_eq h (by omega) (Nat.mod_lt _ (by norm_num))] at ha
  have e1 : mulN m n % 64 = addA (m % 64) (actA (m / 64) (n % 64)) := by
    rw [mulN_eq, actT_eq h (by omega) (Nat.mod_lt _ (by norm_num))]
    omega
  have e2 : mulN m n / 64 = addV (m / 64) (n / 64) := by
    rw [mulN_eq, actT_eq h (by omega) (Nat.mod_lt _ (by norm_num))]
    omega
  unfold dT mulT
  rw [e1, e2, dec_addA (Nat.mod_lt _ (by norm_num)) hq,
    dec_actA _ (by omega) _ (Nat.mod_lt _ (by norm_num)), dV_addV _ (by omega) _ (by omega)]

def toR (x : TM) : RM := (x.1, (x.2.1, x.2.2.1))

def dR (k : ℕ) : RM := toR (dT k)

theorem dT_lam {k : ℕ} (hk : k < 256) : (dT k).2.2.2 = 0 := by
  have e : k / 64 / 4 = 0 := by omega
  change ((k / 64 / 4 : ℕ) : ZMod 2) = 0
  rw [e]
  rfl

theorem act_R : ∀ a b : ZMod 2, ∀ q : A, act (a, b, 0) q = actR (a, b) q := by decide

theorem toR_mulT {x y : TM} (hx : x.2.2.2 = 0) : toR (mulT x y) = mulR (toR x) (toR y) := by
  obtain ⟨p, a, b, c⟩ := x
  simp only at hx
  subst hx
  simp only [toR, mulT, mulR, act_R, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

theorem toR_inj {x y : TM} (hx : x.2.2.2 = 0) (hy : y.2.2.2 = 0) (h : toR x = toR y) : x = y := by
  obtain ⟨p, a, b, c⟩ := x
  obtain ⟨p', a', b', c'⟩ := y
  simp only [toR, Prod.mk.injEq] at h hx hy
  rw [hx, hy, h.1, h.2.1, h.2.2]

structure Codec {X : Type} (N : ℕ) (d : ℕ → X) (m : X → X → X) (one : X) : Prop where
  pos : 0 < N
  le : N ≤ 512
  surj : ∀ x, ∃ k < N, d k = x
  inj : ∀ {k l}, k < N → l < N → d k = d l → k = l
  mul : ∀ {k l}, k < N → l < N → m (d k) (d l) = d (mulN k l)
  lt : ∀ {k l}, k < N → l < N → mulN k l < N
  one : d 0 = one

theorem codecT (h : actOK = true) : Codec 512 dT mulT oneT where
  pos := by norm_num
  le := le_rfl
  surj x := ⟨eT x, eT_lt x, dT_eT x⟩
  inj hk hl e := (dT_inj hk hl).1 e
  mul hk hl := (dT_mulN h hk hl).symm
  lt hk hl := mulN_lt hk hl
  one := rfl

theorem codecR (h : actOK = true) : Codec 256 dR mulR oneR where
  pos := by norm_num
  le := by norm_num
  surj x := by
    refine ⟨eT (x.1, (x.2.1, x.2.2, 0)), ?_, ?_⟩
    · have := cmp_lt x.1
      have : cV (x.2.1, x.2.2, 0) < 4 := by
        unfold cV
        have := ZMod.val_lt x.2.1
        have := ZMod.val_lt x.2.2
        simp
        omega
      change cmp x.1 + 64 * cV (x.2.1, x.2.2, 0) < 256
      omega
    · unfold dR
      rw [dT_eT]
      rfl
  inj hk hl e := (dT_inj (by omega) (by omega)).1 (toR_inj (dT_lam hk) (dT_lam hl) e)
  mul hk hl := by
    unfold dR
    rw [← toR_mulT (dT_lam hk), dT_mulN h (by omega) (by omega)]
  lt {k l} hk hl := by
    have := addA_lt (k % 64) (actT (k / 64) (l % 64))
    have := addV_lt4 (k / 64) (by omega) (l / 64) (by omega)
    rw [mulN_eq]
    omega
  one := rfl

namespace Codec

variable {X : Type} {N : ℕ} {d : ℕ → X} {m : X → X → X} {one : X}

theorem forall_iff (C : Codec N d m one) {P : X → Prop} : (∀ x, P x) ↔ ∀ k < N, P (d k) := by
  constructor
  · intro h k _
    exact h _
  · intro h x
    obtain ⟨k, hk, rfl⟩ := C.surj x
    exact h k hk

theorem eq_iff (C : Codec N d m one) {k l : ℕ} (hk : k < N) (hl : l < N) : d k = d l ↔ k = l :=
  ⟨C.inj hk hl, fun e => e ▸ rfl⟩

theorem beq_iff (C : Codec N d m one) {k l : ℕ} (hk : k < N) (hl : l < N) :
    Nat.beq k l = true ↔ d k = d l := by
  rw [Nat.beq_eq, C.eq_iff hk hl]

theorem comm_iff (C : Codec N d m one) {k l : ℕ} (hk : k < N) (hl : l < N) :
    commN k l = true ↔ m (d k) (d l) = m (d l) (d k) := by
  unfold commN
  rw [C.mul hk hl, C.mul hl hk, C.beq_iff (C.lt hk hl) (C.lt hl hk)]

theorem card_eq (C : Codec N d m one) [Fintype X] (P : X → Prop) [DecidablePred P] (f : ℕ → Bool)
    (hf : ∀ k < N, f k = true ↔ P (d k)) : (Finset.univ.filter P).card = cntR N f := by
  rw [cntR_eq]
  symm
  refine Finset.card_bij (fun k _ => d k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hk ⊢
    exact (hf k hk.1).1 hk.2
  · intro k hk l hl e
    simp only [Finset.mem_filter, Finset.mem_range] at hk hl
    exact C.inj hk.1 hl.1 e
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := C.surj x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨k, by simp [hk, (hf k hk).2 hx], rfl⟩

theorem sum_eq (C : Codec N d m one) [Fintype X] (F : X → ℕ) (g : ℕ → ℕ)
    (hg : ∀ k < N, g k = F (d k)) : ∑ x, F x = sumR N g := by
  rw [sumR_eq]
  symm
  refine Finset.sum_bij (fun k _ => d k) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro k hk l hl e
    exact C.inj (Finset.mem_range.1 hk) (Finset.mem_range.1 hl) e
  · intro x _
    obtain ⟨k, hk, rfl⟩ := C.surj x
    exact ⟨k, Finset.mem_range.2 hk, rfl⟩
  · intro k hk
    exact hg k (Finset.mem_range.1 hk)

theorem ordGo (C : Codec N d m one) [DecidableEq X] {x : ℕ} (hx : x < N) :
    ∀ (f : ℕ) {r : ℕ}, r < N → ∀ n, cOrdGo m one (d x) f (d r) n = ordGoN x f r n := by
  intro f
  induction f with
  | zero => intro r _ n; rfl
  | succ f ih =>
    intro r hr n
    have e : ordGoN x (f + 1) r n = Bool.rec (ordGoN x f (mulN r x) (Nat.succ n)) n (Nat.beq r 0) :=
      rfl
    rw [e]
    simp only [cOrdGo]
    have h0 : d r = one ↔ Nat.beq r 0 = true := by
      rw [← C.one, C.beq_iff hr C.pos]
    by_cases hr0 : d r = one
    · rw [if_pos hr0, h0.1 hr0]
    · rw [if_neg hr0, C.mul hr hx, ih (C.lt hr hx)]
      have : Nat.beq r 0 = false := by
        cases hb : Nat.beq r 0
        · rfl
        · exact absurd (h0.2 hb) hr0
      rw [this]

theorem ord (C : Codec N d m one) [DecidableEq X] {O : ℕ} (hO : ordOK O = true) {x : ℕ}
    (hx : x < N) : cOrd m one (d x) = ordT O x := by
  rw [Nat.eq_of_beq_eq_true (allR_iff.1 hO x (lt_of_lt_of_le hx C.le))]
  exact C.ordGo hx 32 hx 1

theorem c1_eq (C : Codec N d m one) [Fintype X] [DecidableEq X] {O : ℕ} (hO : ordOK O = true)
    {x : ℕ} (hx : x < N) : c1 m one (d x) = c1N O N x := by
  unfold c1 cRound c1N
  congr 1
  refine C.sum_eq _ _ fun k hk => ?_
  rw [C.mul hx hk, C.ord hO hk, C.ord hO (C.lt hx hk)]
  rfl

theorem sep (C : Codec N d m one) [Fintype X] [DecidableEq X] {O : ℕ} (hO : ordOK O = true)
    {CI CO : List ℕ} (hd : disjB CI CO = true) {P : X → Prop} {pr : ℕ → Bool}
    (hpr : ∀ k < N, pr k = true ↔ P (d k))
    (hc : ∀ k < N, colOK CI CO (pr k) (c1N O N k) = true) :
    ∀ a b : X, c1 m one a = c1 m one b → (P a ↔ P b) := by
  have key : ∀ k < N, (P (d k) → c1N O N k ∈ CI) ∧ (¬ P (d k) → c1N O N k ∈ CO) := by
    intro k hk
    have h := hc k hk
    unfold colOK at h
    constructor
    · intro hp
      rw [(hpr k hk).2 hp] at h
      exact inL_iff.1 h
    · intro hp
      have : pr k = false := by
        cases e : pr k
        · rfl
        · exact absurd ((hpr k hk).1 e) hp
      rw [this] at h
      exact inL_iff.1 h
  have hd' := allL_iff.1 hd
  have no : ∀ c, c ∈ CI → c ∈ CO → False := fun c h1 h2 =>
    (bN_iff.1 (hd' c h1)) (inL_iff.2 h2)
  intro a b hab
  obtain ⟨k, hk, rfl⟩ := C.surj a
  obtain ⟨l, hl, rfl⟩ := C.surj b
  rw [C.c1_eq hO hk, C.c1_eq hO hl] at hab
  constructor
  · intro hp
    by_contra hq
    have h1 := (key k hk).1 hp
    have h2 := (key l hl).2 hq
    rw [← hab] at h2
    exact no _ h1 h2
  · intro hq
    by_contra hp
    have h1 := (key l hl).1 hq
    have h2 := (key k hk).2 hp
    rw [hab] at h2
    exact no _ h1 h2

end Codec

theorem charS_iff {O N : ℕ} {CI CO : List ℕ} {pr : ℕ → Bool} {lo len : ℕ} :
    charS O N CI CO pr lo len = true ↔
      ∀ j < len, colOK CI CO (pr (lo + j)) (c1N O N (lo + j)) = true :=
  allR_iff

theorem inR_iff : ∀ k < 512, (inR (dT k) ↔ inRN k = true) := by decide +kernel
theorem inQ_iff : ∀ k < 512, (inQ (dT k) ↔ inQN k = true) := by decide +kernel
theorem inP_iff : ∀ k < 512, (inP (dT k) ↔ inPN k = true) := by decide +kernel
theorem inZ_iff : ∀ k < 512, (inZ (dT k) ↔ zN k = true) := by decide +kernel
theorem EA_iff : ∀ p < 64, (EA (dec p) ↔ eAN p = true) := by decide +kernel
theorem FA_iff : ∀ p < 64, (FA (dec p) ↔ fAN p = true) := by decide +kernel
theorem ZA_iff : ∀ p < 64, (ZA (dec p) ↔ zN p = true) := by decide +kernel
theorem x2_iff : ∀ p < 64, ((2 : ℕ) • dec p = 0 ↔ x2N p = true) := by decide +kernel
theorem inPR_iff : ∀ k < 256, ((dR k).2 = 0 ↔ inPN k = true) := by decide +kernel

theorem eE_eq : ∀ a b : ZMod 4, eE a b = dT (a.val + 4 * b.val) := by decide
theorem eE_dT : ∀ j < 16, ∃ a b : ZMod 4, eE a b = dT j := by
  intro j hj
  refine ⟨(j : ZMod 4), ((j / 4 : ℕ) : ZMod 4), ?_⟩
  revert j
  decide
theorem eE_lt (a b : ZMod 4) : a.val + 4 * b.val < 16 := by
  have := ZMod.val_lt a
  have := ZMod.val_lt b
  omega
theorem zE_dT : ∀ j : ℕ, j < 4 → zE (j : ZMod 2) ((j / 2 : ℕ) : ZMod 2) = dT (zcN j) := by decide
theorem zcN_lt : ∀ j < 4, zcN j < 512 := by decide
theorem tM_eq : tM = dT 64 := rfl
theorem tsM_eq : tsM = dT 192 := rfl
theorem mulN_192 : ∀ j < 16, mulN j 192 = 192 + j := by decide +kernel

theorem commT (h : actOK = true) {k l : ℕ} (hk : k < 512) (hl : l < 512) :
    commN k l = true ↔ mulT (dT k) (dT l) = mulT (dT l) (dT k) :=
  (codecT h).comm_iff hk hl

theorem act_zero (q : A) : act 0 q = q := by simp [act, ap]

theorem mul_eE (a b : ZMod 4) (y x : TM) :
    mulT (mulT (eE a b) y) x = (((a, b, 0, 0) : A) + (mulT y x).1, (mulT y x).2) := by
  simp only [mulT, eE, act_zero, zero_add, add_assoc]

theorem rqRow_iff (x y : TM) :
    RQRow x y ↔ (mulT x y).2 = (mulT y x).2 ∧ (mulT x y).1.2.2 = (mulT y x).1.2.2 := by
  unfold RQRow
  simp only [mul_eE]
  generalize mulT x y = z
  generalize mulT y x = w
  constructor
  · rintro ⟨a, b, e⟩
    rw [e]
    simp
  · rintro ⟨h1, h2⟩
    refine ⟨z.1.1 - w.1.1, z.1.2.1 - w.1.2.1, ?_⟩
    obtain ⟨⟨z1, z2, z3⟩, zv⟩ := z
    obtain ⟨⟨w1, w2, w3⟩, wv⟩ := w
    simp only at h1 h2
    subst h1 h2
    simp

def rp (c : ZMod 2 × ZMod 2) : ℕ := c.1.val + 2 * c.2.val

theorem rp_dec : ∀ p < 64, rp (dec p).2.2 = p / 16 := by decide
theorem rp_inj : ∀ c c' : ZMod 2 × ZMod 2, rp c = rp c' → c = c' := by decide

theorem rqC_iff {u w : ℕ} (hu : u < 512) (hw : w < 512) :
    rqC u w = true ↔ (dT u).2 = (dT w).2 ∧ (dT u).1.2.2 = (dT w).1.2.2 := by
  have hu': u % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hw' : w % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have e1 : (dT u).2 = (dT w).2 ↔ u / 64 = w / 64 := by
    constructor
    · intro h
      have := congrArg cV h
      simp only [dT] at this
      rwa [cV_dV _ (by omega), cV_dV _ (by omega)] at this
    · intro h
      simp only [dT, h]
  have e2 : (dT u).1.2.2 = (dT w).1.2.2 ↔ u % 64 / 16 = w % 64 / 16 := by
    simp only [dT]
    constructor
    · intro h
      rw [← rp_dec _ hu', ← rp_dec _ hw', h]
    · intro h
      exact rp_inj _ _ (by rw [rp_dec _ hu', rp_dec _ hw', h])
  rw [e1, e2]
  unfold rqC
  rw [bA_iff, Nat.beq_eq, Nat.beq_eq]
  exact Iff.rfl

theorem comm_pe_iff (a : A) (i : TM) : mulT (pe a) i = mulT i (pe a) ↔ act i.2 a = a := by
  simp only [mulT, pe, act_zero, zero_add, add_zero, Prod.mk.injEq, and_true]
  constructor
  · intro h
    have := h.symm
    rw [add_comm] at this
    exact add_right_cancel this
  · intro h
    rw [h, add_comm]

theorem act_dT (h : actOK = true) {k p : ℕ} (hk : k < 512) (hp : p < 64) :
    act (dT k).2 (dec p) = dec (actA (k / 64) p) := (dec_actA _ (by omega) _ hp).symm

theorem fix_iff (h : actOK = true) {k p : ℕ} (hk : k < 512) (hp : p < 64) :
    act (dT k).2 (dec p) = dec p ↔ Nat.beq (actA (k / 64) p) p = true := by
  rw [act_dT h hk hp, Nat.beq_eq]
  constructor
  · intro e
    rw [← cmp_dec _ (actA_lt _ (by omega) _ hp), e, cmp_dec _ hp]
  · intro e
    rw [e]

theorem forallA {P : A → Prop} : (∀ a, P a) ↔ ∀ p < 64, P (dec p) :=
  ⟨fun h p _ => h _, fun h a => dec_cmp a ▸ h _ (cmp_lt a)⟩

theorem centOf_iff (h : actOK = true) {k : ℕ} (hk : k < 512) (pr : A → Prop) [DecidablePred pr]
    (prN : ℕ → Bool) (hpr : ∀ p < 64, pr (dec p) ↔ prN p = true) :
    CentOf (dT k) pr ↔ centOfN (k / 64) prN = true := by
  unfold CentOf centOfN
  rw [allR_iff, forallA]
  refine forall₂_congr fun p hp => ?_
  rw [bE_iff, comm_pe_iff, fix_iff h hk hp, hpr p hp]

theorem centX_iff (h : actOK = true) {k : ℕ} (hk : k < 512) :
    CentX (dT k) ↔ centXN (k / 64) = true := by
  unfold CentX centXN
  rw [allR_iff, forallA]
  refine forall₂_congr fun p hp => ?_
  rw [bI_iff, comm_pe_iff, fix_iff h hk hp, x2_iff p hp]

section Facts

variable (hA : actOK = true)
include hA

theorem sqZ (hc : sqzB = true) : SqZ := by
  unfold SqZ
  rw [(codecT hA).forall_iff]
  intro k hk hr
  have := bI_iff.1 (allR_iff.1 hc k hk) ((inR_iff k hk).1 hr)
  rw [← dT_mulN hA hk hk]
  exact (inZ_iff _ (mulN_lt hk hk)).2 this

theorem rQ (h0 : rqS 0 64 = true) (h1 : rqS 64 64 = true) (h2 : rqS 128 64 = true)
    (h3 : rqS 192 64 = true) (h4 : rqS 256 256 = true) : RQ := by
  have all : ∀ x < 512, inRN x = true → ∀ y < 512, inQN y = true →
      rqC (mulN x y) (mulN y x) = true := by
    intro x hx hr y hy hq
    have key : ∀ lo len, rqS lo len = true → lo ≤ x → x < lo + len →
        rqC (mulN x y) (mulN y x) = true := by
      intro lo len hs h1 h2
      have := bI_iff.1 (allR_iff.1 hs (x - lo) (by omega))
      rw [nA, Nat.add_sub_cancel' h1] at this
      exact bI_iff.1 (allR_iff.1 (this hr) y hy) hq
    by_cases c0 : x < 64
    · exact key 0 64 h0 (by omega) (by omega)
    by_cases c1 : x < 128
    · exact key 64 64 h1 (by omega) (by omega)
    by_cases c2 : x < 192
    · exact key 128 64 h2 (by omega) (by omega)
    by_cases c3 : x < 256
    · exact key 192 64 h3 (by omega) (by omega)
    · exact key 256 256 h4 (by omega) (by omega)
  unfold RQ RQRow2
  rw [(codecT hA).forall_iff]
  intro x hx hr
  rw [(codecT hA).forall_iff]
  intro y hy hq
  rw [rqRow_iff, ← dT_mulN hA hx hy, ← dT_mulN hA hy hx]
  exact (rqC_iff (mulN_lt hx hy) (mulN_lt hy hx)).1
    (all x hx ((inR_iff x hx).1 hr) y hy ((inQ_iff y hy).1 hq))

theorem qC (hc : qcB = true) : QC := by
  unfold QC
  rw [(codecT hA).forall_iff]
  intro k hk hr
  have h := bE_iff.1 (bI_iff.1 (allR_iff.1 hc k hk) ((inR_iff k hk).1 hr))
  rw [inQ_iff k hk, ← h, allR_iff]
  unfold CentE
  constructor
  · intro hE j hj
    obtain ⟨a, b, e⟩ := eE_dT j hj
    rw [commT hA hk (by omega), ← e]
    exact hE a b
  · intro hE a b
    rw [eE_eq]
    exact (commT hA hk (by have := eE_lt a b; omega)).1 (hE _ (eE_lt a b))

theorem eF (hc : efB = true) : EF := by
  unfold EF
  rw [forallA]
  intro p hp he hf
  have := bI_iff.1 (bI_iff.1 (allR_iff.1 hc p hp) ((EA_iff p hp).1 he)) ((FA_iff p hp).1 hf)
  exact (ZA_iff p hp).2 this

theorem centP (hc : centPB = true) : CentP := by
  unfold CentP
  rw [(codecT hA).forall_iff]
  intro k hk hr hp
  have h := bI_iff.1 (bI_iff.1 (allR_iff.1 hc k hk) ((inR_iff k hk).1 hr))
    (bN_iff.2 fun e => hp ((inP_iff k hk).2 e))
  rcases bO_iff.1 h with h | h
  · exact Or.inl ((centOf_iff hA hk EA eAN EA_iff).2 h)
  rcases bO_iff.1 h with h | h
  · exact Or.inr (Or.inl ((centOf_iff hA hk FA fAN FA_iff).2 h))
  · exact Or.inr (Or.inr ((centX_iff hA hk).2 h))

theorem invF (hc : invFB = true) : InvF := by
  unfold InvF InvRow
  rw [(codecT hA).forall_iff]
  intro k hk hr hp hii hF
  have h1 := bI_iff.1 (allR_iff.1 hc k hk) ((inR_iff k hk).1 hr)
  have h2 := bI_iff.1 h1 (bN_iff.2 fun e => hp ((inP_iff k hk).2 e))
  have h3 := bI_iff.1 h2 (by
    rw [Nat.beq_eq, ← dT_inj (mulN_lt hk hk) (by norm_num), dT_mulN hA hk hk]
    exact hii)
  have h4 := bI_iff.1 h3 ((centOf_iff hA hk FA fAN FA_iff).1 hF)
  obtain ⟨j, hj, e⟩ := anyR_iff.1 h4
  obtain ⟨a, b, ea⟩ := eE_dT j hj
  refine ⟨a, b, ?_⟩
  rw [Nat.beq_eq] at e
  rw [e, dT_mulN hA (by omega) (by norm_num), ea, tsM_eq]

theorem cardS {t n : ℕ} (htl : t < 512) (ht : dT t = tM) (hn : n = 128)
    (hc : cardSB t n = true) : CardS := by
  unfold cardSB at hc
  have e := (codecT hA).card_eq inS (fun k => commN k t) fun k hk => by
    rw [commT hA hk htl, ht]
    rfl
  unfold CardS
  rw [e, ← hn]
  exact Nat.eq_of_beq_eq_true hc

theorem fusAt (i M x y : ℕ) (hi : i < 512) (hx : x < 512) (hy : y < 512)
    (hc : fusB i M x y = true) : FusAt (dT i) := by
  obtain ⟨hm, hc⟩ := bA_iff.1 hc
  obtain ⟨hcard, hc⟩ := bA_iff.1 hc
  obtain ⟨hsq, hc⟩ := bA_iff.1 hc
  obtain ⟨hz, hcls⟩ := bA_iff.1 hc
  have hcr : ∀ k < 512, crN i k = true ↔ CR (dT i) (dT k) := by
    intro k hk
    unfold crN CR
    rw [bA_iff, inR_iff k hk, commT hA hk hi]
  have hM : ∀ k < 512, bit M k = true ↔ CR (dT i) (dT k) := by
    intro k hk
    rw [← hcr k hk]
    exact bE_iff.1 (allR_iff.1 hm k hk)
  have hCR : ∀ c : TM, CR (dT i) c ↔ ∃ k < 512, dT k = c ∧ bit M k = true := by
    intro c
    obtain ⟨k, hk, rfl⟩ := (codecT hA).surj c
    constructor
    · intro h
      exact ⟨k, hk, rfl, (hM k hk).2 h⟩
    · rintro ⟨l, hl, e, hb⟩
      rw [← e]
      exact (hM l hl).1 hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(codecT hA).card_eq _ (bit M) hM]
    exact Nat.eq_of_beq_eq_true hcard
  · unfold sqPairN at hsq
    obtain ⟨h1, h2, h3, h4, h5⟩ : crN i x = true ∧ crN i y = true ∧ _ ∧ _ ∧ _ := by
      simpa only [bA_iff] using hsq
    refine ⟨dT x, dT y, (hcr x hx).1 h1, (hcr y hy).1 h2, ?_, ?_, ?_⟩
    · intro e
      apply bN_iff.1 h3
      rw [Nat.beq_eq, ← dT_inj (mulN_lt hx hx) (by norm_num), dT_mulN hA hx hx]
      exact e
    · intro e
      apply bN_iff.1 h4
      rw [Nat.beq_eq, ← dT_inj (mulN_lt hy hy) (by norm_num), dT_mulN hA hy hy]
      exact e
    · intro e
      apply bN_iff.1 h5
      rw [Nat.beq_eq, ← dT_inj (mulN_lt hx hx) (mulN_lt hy hy), dT_mulN hA hx hx,
        dT_mulN hA hy hy]
      exact e
  · rw [(codecT hA).card_eq _ (zcrN M)]
    · exact Nat.eq_of_beq_eq_true hz
    · intro z hzl
      unfold zcrN ZCR
      rw [bA_iff, hM z hzl, allR_iff]
      refine and_congr_right fun _ => ?_
      rw [(codecT hA).forall_iff]
      refine forall₂_congr fun c hc => ?_
      rw [bI_iff, hM c hc, commT hA hzl hc]
  · unfold ClsAll ClsZ
    rw [(codecT hA).forall_iff]
    intro r hr hrR
    obtain ⟨j, hj, e⟩ := anyR_iff.1 (bI_iff.1 (allR_iff.1 hcls r hr) ((inR_iff r hr).1 hrR))
    refine ⟨(j : ZMod 2), ((j / 2 : ℕ) : ZMod 2), ?_⟩
    have hz := zcN_lt j hj
    rw [Nat.beq_eq] at e
    rw [zE_dT j hj, ← dT_mulN hA hr hi, ← dT_mulN hA hi hz,
      ← dT_mulN hA (mulN_lt hi hz) hr, e]

theorem fusAll
    (ht : ∃ M, fusB 64 M 1 4 = true)
    (hs : ∀ j < 16, ∃ M, fusB (192 + j) M 17 36 = true) : FusAll := by
  obtain ⟨M, hM⟩ := ht
  refine ⟨tM_eq ▸ fusAt hA 64 M 1 4 (by norm_num) (by norm_num) (by norm_num) hM, ?_⟩
  intro a b
  unfold FusTS
  have hj := eE_lt a b
  obtain ⟨M, hM⟩ := hs _ hj
  rw [eE_eq, tsM_eq, ← dT_mulN hA (by omega) (by norm_num), mulN_192 _ hj]
  exact fusAt hA _ M 17 36 (by omega) (by norm_num) (by norm_num) hM

theorem sLem (KS : ℕ) (D : List ℕ) (hc : slOK KS D = true) : SLem := by
  obtain ⟨hKS, hc⟩ := bA_iff.1 hc
  obtain ⟨hD, hc⟩ := bA_iff.1 hc
  obtain ⟨hall, hpairs⟩ := bA_iff.1 hc
  have hS : ∀ x < 512, bit KS x = true ↔ inS (dT x) := by
    intro x hx
    rw [bE_iff.1 (allR_iff.1 hKS x hx), commT hA hx (by norm_num)]
    unfold inS
    rw [tM_eq]
  have hent : ∀ a < 512, inS (dT a) → mulT (dT a) (dT a) = oneT → dT a ≠ oneT →
      ∃ e ∈ D, e % 512 = a := by
    intro a ha h1 h2 h3
    have hinv : invSN KS a = true := by
      unfold invSN
      rw [bA_iff, bA_iff, hS a ha, bN_iff, Nat.beq_eq, Nat.beq_eq,
        ← dT_inj (mulN_lt ha ha) (by norm_num), dT_mulN hA ha ha]
      refine ⟨h1, h2, fun e => h3 ?_⟩
      rw [e]
      rfl
    obtain ⟨e, he, ee⟩ := anyL_iff.1 (bI_iff.1 (allR_iff.1 hall a ha) hinv)
    exact ⟨e, he, Nat.eq_of_beq_eq_true ee⟩
  have hmask : ∀ e ∈ D, ∀ x < 512, (e / 512).testBit x = true ↔
      inS (dT x) ∧ mulT (dT x) (dT (e % 512)) = mulT (dT (e % 512)) (dT x) := by
    intro e he x hx
    have h1 : bit (e / 512) x = true ↔ bA (bit KS x) (commN x (e % 512)) = true :=
      bE_iff.1 (allR_iff.1 (allL_iff.1 hD e he) x hx)
    rw [← bit_iff, h1, bA_iff, hS x hx, commT hA hx (Nat.mod_lt _ (by norm_num))]
  unfold SLem SLRow
  rw [(codecT hA).forall_iff]
  intro ka hka
  rw [(codecT hA).forall_iff]
  intro kb hkb hSa hSb hia hib hna hnb hab hcomm hcard _ _
  obtain ⟨e, he, rfl⟩ := hent ka hka hSa hia hna
  obtain ⟨f, hf, rfl⟩ := hent kb hkb hSb hib hnb
  have hp := bI_iff.1 (bI_iff.1 (allL_iff.1 (allL_iff.1 hpairs e he) f hf)
    (bN_iff.2 fun h => hab (by
      have e' : e % 512 = f % 512 := Nat.eq_of_beq_eq_true h
      rw [e'])))
    ((commT hA (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))).2 hcomm)
  set K := Nat.land (e / 512) (f / 512)
  have hK : ∀ x < 512, bit K x = true ↔ CS (dT (e % 512)) (dT (f % 512)) (dT x) := by
    intro x hx
    rw [bit_iff]
    change ((e / 512) &&& (f / 512)).testBit x = true ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true, hmask e he x hx, hmask f hf x hx]
    unfold CS
    constructor
    · rintro ⟨⟨h1, h2⟩, -, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h1, h3⟩
  have hcnt : (Finset.univ.filter (CS (dT (e % 512)) (dT (f % 512)))).card = cntR 512 (bit K) :=
    (codecT hA).card_eq _ _ hK
  have hp' : bO (Nat.blt K two256) (bN (Nat.beq (cntR 512 (bit K)) 64)) = true := hp
  rcases bO_iff.1 hp' with hlt | hne
  · have e256 : two256 = 2 ^ 256 := by norm_num [two256]
    have hK256 : K < 2 ^ 256 := by
      rw [← e256]
      simpa [Nat.blt_eq] using hlt
    unfold InCR
    rw [(codecT hA).forall_iff]
    intro x hx hcs
    rw [inR_iff x hx]
    by_contra hxr
    have hx256 : 256 ≤ x := by
      by_contra h'
      exact hxr (by simp [inRN, Nat.blt_eq]; omega)
    have hb := (bit_iff K x).1 ((hK x hx).2 hcs)
    have hlt' : K < 2 ^ x := lt_of_lt_of_le hK256 (Nat.pow_le_pow_right (by norm_num) hx256)
    rw [Nat.testBit_lt_two_pow hlt'] at hb
    exact Bool.false_ne_true hb
  · have h64 : cntR 512 (bit K) = 64 := by rw [← hcnt, hcard]
    exact absurd (by rw [Nat.beq_eq]; exact h64) (bN_iff.1 hne)

end Facts

theorem modelFacts (hA : actOK = true) {O : ℕ} (hO : ordOK O = true)
    {CI CO PI PO : List ℕ} (hdR : disjB CI CO = true) (hdP : disjB PI PO = true)
    (hR : ∀ k < 512, colOK CI CO (inRN k) (c1N O 512 k) = true)
    (hP : ∀ k < 256, colOK PI PO (inPN k) (c1N O 256 k) = true)
    (hsq : sqzB = true) (hrq : RQ) (hqc : qcB = true) (hef : efB = true) (hcp : centPB = true)
    (hinv : invFB = true) (hfus : FusAll) (hcs : CardS) (hsl : SLem) : ModelFacts :=
  ⟨(codecT hA).sep hO hdR (fun k hk => (inR_iff k hk).symm) hR,
    (codecR hA).sep hO hdP (fun k hk => (inPR_iff k hk).symm) hP,
    sqZ hA hsq, hrq, qC hA hqc, eF hA hef, centP hA hcp, invF hA hinv, hfus, hcs, hsl⟩

end CFSG.FzL410KM

end
