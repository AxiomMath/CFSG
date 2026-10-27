module

public import Certificates.Data.Kernel.CosetLog
public import CFSG.Certificates.PresentationLetters
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

namespace CFSG.KC.CLog

open CFSG.Certificates.CosetEnumeration CFSG.KC.Enum CFSG.KS.PEnum CFSG.KS.Row

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bAndE (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIfE (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem nIfE (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem aOf_lt (e : Nat) : aOf e < 16384 := by
  change (e >>> 2) &&& 16383 < 16384
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem bOf_lt (e : Nat) : bOf e < 16384 := by
  change (e >>> 20) &&& 16383 < 16384
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem kindOf_lt (e : Nat) : kindOf e < 4 := by
  change e &&& 3 < 4
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem stK_eq (q p : Nat) : stK q p = q * 256 + p := by
  change q <<< 8 + p = _
  rw [Nat.shiftLeft_eq]

theorem stK_q {q p : Nat} (hp : p < 256) : Nat.shiftRight (stK q p) (nat_lit 8) = q := by
  rw [stK_eq]
  change (q * 256 + p) >>> 8 = q
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem stK_p {q p : Nat} (hp : p < 256) : Nat.land (stK q p) (nat_lit 255) = p := by
  rw [stK_eq]
  change (q * 256 + p) &&& (2 ^ 8 - 1) = p
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem failK_eq : failK = 1073741824 := rfl

theorem xor1 : ∀ c < 16, Nat.xor c 1 = invCode c := by decide

noncomputable def prodR {G : Type} [Group G] (F : ℕ → G) : ℕ → G
  | 0 => 1
  | n + 1 => prodR F n * F n

section Prod

variable {G : Type} [Group G]

theorem prodR_zero (F : ℕ → G) : prodR F 0 = 1 := rfl

theorem prodR_succ (F : ℕ → G) (n : ℕ) : prodR F (n + 1) = prodR F n * F n := rfl

theorem prodR_congr {F F' : ℕ → G} : ∀ {n : ℕ}, (∀ i < n, F i = F' i) → prodR F n = prodR F' n
  | 0, _ => rfl
  | n + 1, h => by
    rw [prodR_succ, prodR_succ, prodR_congr (fun i hi => h i (by omega)), h n (by omega)]

theorem prodR_succ' (F : ℕ → G) : ∀ n : ℕ, prodR F (n + 1) = F 0 * prodR (fun i => F (i + 1)) n
  | 0 => by simp [prodR]
  | n + 1 => by rw [prodR_succ, prodR_succ' F n, prodR_succ, mul_assoc]

theorem prodR_rev (F : ℕ → G) : ∀ n : ℕ, prodR (fun i => (F (n - 1 - i))⁻¹) n = (prodR F n)⁻¹
  | 0 => by simp [prodR]
  | n + 1 => by
    rw [prodR_succ', prodR_succ, mul_inv_rev]
    have e : (fun i => (F (n + 1 - 1 - (i + 1)))⁻¹) = fun i => (F (n - 1 - i))⁻¹ := by
      funext i
      congr 2
      omega
    rw [e, prodR_rev F n]
    congr 2

theorem prodR_rot {f : ℕ → G} {n : ℕ} (hn : 0 < n) (h : prodR f n = 1) :
    ∀ k, prodR (fun p => f ((k + p) % n)) n = 1
  | 0 => by
    rw [← h]
    exact prodR_congr (fun i hi => by rw [Nat.zero_add, Nat.mod_eq_of_lt hi])
  | k + 1 => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have ih := prodR_rot hn h k
    rw [prodR_succ'] at ih
    have hX := eq_inv_of_mul_eq_one_right ih
    rw [prodR_succ]
    have e1 : prodR (fun p => f ((k + 1 + p) % (n' + 1))) n' =
        prodR (fun i => f ((k + (i + 1)) % (n' + 1))) n' :=
      prodR_congr (fun i _ => by rw [Nat.add_assoc, Nat.add_comm 1 i])
    have e2 : (k + 1 + n') % (n' + 1) = (k + 0) % (n' + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 n', Nat.add_mod_right]
      rfl
    rw [e1, hX, e2, inv_mul_cancel]

end Prod

theorem wordK_go {G : Type} [Group G] (gen : ℕ → G) {m P n : ℕ} : ∀ (w : List ℕ) (j : ℕ),
    (List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j n)
      (fun c _ ih j => bAnd(Nat.blt c (Nat.mul (nat_lit 2) m),
        bAnd(Nat.beq (pg (nat_lit 4) (nat_lit 15) P j) c, strictB (Nat.succ j) ih))) w) j = true →
    j + w.length = n ∧ (∀ i < w.length, pg 4 15 P (j + i) < 2 * m) ∧
      (w.map gen).prod = prodR (fun i => gen (pg 4 15 P (j + i))) w.length
  | [], j, h => by
    simp only [Nat.beq_eq] at h
    exact ⟨by simpa using h, fun i hi => absurd hi (by simp), rfl⟩
  | c :: w, j, h => by
    simp only [sB, bAndE, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨hc, hp, hr⟩ := h
    obtain ⟨h1, h2, h3⟩ := wordK_go gen w (Nat.succ j) hr
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_, ?_⟩
    · rcases i with _ | i
      · rw [Nat.add_zero, hp]
        exact hc
      · have := h2 i (by simpa using hi)
        rwa [Nat.succ_add, ← Nat.add_succ] at this
    · rw [List.map_cons, List.prod_cons, h3, List.length_cons, prodR_succ', Nat.add_zero, hp]
      congr 2
      funext i
      rw [Nat.succ_add, ← Nat.add_succ]

theorem relsK_go {m nR : ℕ} {RL RN : ℕ → ℕ} : ∀ (rels : List (List ℕ)) (i : ℕ),
    (List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i nR)
      (fun w _ ih i => bAnd(Nat.blt (nat_lit 0) (RN i), bAnd(Nat.blt (RN i) (nat_lit 255),
        bAnd(wordK m w (RL i) (RN i), strictB (Nat.succ i) ih)))) rels) i = true →
    ∀ r, i ≤ r → r < nR → ∃ w ∈ rels, 0 < RN r ∧ RN r < 255 ∧ wordK m w (RL r) (RN r) = true
  | [], i, h, r, h1, h2 => by
    simp only [Nat.beq_eq] at h
    omega
  | w :: rels, i, h, r, h1, h2 => by
    simp only [sB, bAndE, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨ha, hb, hc, hd⟩ := h
    rcases Nat.lt_or_ge i r with hir | hir
    · obtain ⟨w', hw', h'⟩ := relsK_go rels (Nat.succ i) hd r hir h2
      exact ⟨w', List.mem_cons_of_mem _ hw', h'⟩
    · have : r = i := by omega
      subst this
      exact ⟨w, List.mem_cons_self, ha, hb, hc⟩

theorem mask_mem : ∀ (subs : List ℕ) (x : ℕ),
    Nat.testBit (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) c) ih) subs) x = true → x ∈ subs
  | [], x, h => by simp at h
  | c :: subs, x, h => by
    change Nat.testBit ((1 <<< c) ||| (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) c) ih) subs)) x = true at h
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [decide_eq_true_eq] at h
      subst h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mask_mem subs x h)

theorem subsK_mem {m SM x : ℕ} {subs : List ℕ} (h : subsK m subs SM = true)
    (hx : fl SM x 1 = 1) : x ∈ subs := by
  unfold subsK at h
  simp only [bAndE, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨_, h⟩ := h
  apply mask_mem subs x
  rw [← h, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  have : fl SM x 1 = SM / 2 ^ x % 2 := by
    change (SM >>> x) &&& (2 ^ 1 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_one]
  rw [← this, hx]

theorem letK_lo {RL RN : ℕ → ℕ} {W x off p : ℕ} (ho : Nat.land W 3 < 2) :
    letK RL RN W x off p = if Nat.land W 3 = 0 then
      pg 4 15 (RL (fl W 8 255)) ((fl W 2 63 + (p + off)) % RN (fl W 8 255))
    else Nat.xor (pg 4 15 (RL (fl W 8 255))
      (RN (fl W 8 255) - 1 - (fl W 2 63 + (p + off)) % RN (fl W 8 255))) 1 := by
  unfold letK
  simp only [sN, nIfE, Nat.blt_eq, Nat.beq_eq]
  rw [ite_eq_left ho]
  rfl

theorem letK_hi {RL RN : ℕ → ℕ} {W x off p : ℕ} (ho : ¬ Nat.land W 3 < 2) :
    letK RL RN W x off p =
      if Nat.land W 3 = 2 then (if p = 0 then Nat.xor x 1 else x) else x := by
  unfold letK
  simp only [sN, nIfE, Nat.blt_eq, Nat.beq_eq]
  rw [ite_eq_right ho]

theorem factK_spec {m nR NC SM : ℕ} {RL RN FD FS FW SD DT : ℕ → ℕ} {t : ℕ}
    (h : factK m nR NC SM RL RN FD FS FW SD DT t = true) :
    0 < aOf (fdK FD t) ∧ aOf (fdK FD t) < NC ∧ 0 < bOf (fdK FD t) ∧ bOf (fdK FD t) < NC ∧
    xOf (fdK FD t) < 2 * m ∧ (Nat.land (r32 FW t) 3 < 2 → fl (r32 FW t) 8 255 < nR) ∧
    ruleK SM RL RN FD FS SD DT t (fdK FD t) (r32 FW t) = true := by
  unfold factK rangeK at h
  simp only [sB, bAndE] at h
  simp only [bIfE, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun ho => ?_, h7⟩
  rw [ite_eq_left ho, Nat.blt_eq] at h6
  exact h6

theorem rule0 {SM : ℕ} {RL RN FD FS SD DT : ℕ → ℕ} {t e W : ℕ}
    (h : ruleK SM RL RN FD FS SD DT t e W = true) (hk : kindOf e = 0) :
    2 ≤ bOf e ∧ r32 DT (bOf e) = t ∧ (aOf e = 1 ∨ r32 DT (aOf e) < t) := by
  unfold ruleK at h
  simp only [sB, bAndE] at h
  simp only [bIfE, Nat.blt_eq, Nat.beq_eq] at h
  rw [ite_eq_left hk] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨h1, h2, h3, _⟩ := h
  refine ⟨h1, h2, ?_⟩
  by_cases ha : aOf e = 1
  · exact Or.inl ha
  · rw [ite_eq_right ha, Nat.blt_eq] at h3
    exact Or.inr h3

theorem rule1 {SM : ℕ} {RL RN FD FS SD DT : ℕ → ℕ} {t e W : ℕ}
    (h : ruleK SM RL RN FD FS SD DT t e W = true) (hk : kindOf e = 1) :
    aOf e = 1 ∧ bOf e = 1 ∧ fl SM (xOf e) 1 = 1 := by
  unfold ruleK at h
  simp only [sB, bAndE] at h
  simp only [bIfE, Nat.blt_eq, Nat.beq_eq] at h
  rw [ite_eq_right (by omega), ite_eq_left hk] at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem rule2 {SM : ℕ} {RL RN FD FS SD DT : ℕ → ℕ} {t e W : ℕ}
    (h : ruleK SM RL RN FD FS SD DT t e W = true) (hk : kindOf e = 2) :
    (Nat.land W 3 < 2 ∧ letK RL RN W (xOf e) 0 0 = xOf e ∧
      walkOK FD FS SD (letK RL RN W (xOf e) 1) t (bOf e) (aOf e) (RN (fl W 8 255) - 1) = true) ∨
    (Nat.land W 3 = 3 ∧ walkOK FD FS SD (letK RL RN W (xOf e) 0) t (aOf e) (bOf e) 1 = true) := by
  unfold ruleK at h
  simp only [sB, bAndE] at h
  simp only [bIfE, Nat.blt_eq, Nat.beq_eq] at h
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hk] at h
  by_cases ho : Nat.land W 3 < 2
  · rw [ite_eq_left ho] at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    exact Or.inl ⟨ho, h.1, h.2⟩
  · rw [ite_eq_right ho] at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    exact Or.inr h

theorem rule3 {SM : ℕ} {RL RN FD FS SD DT : ℕ → ℕ} {t e W : ℕ}
    (h : ruleK SM RL RN FD FS SD DT t e W = true) (hk : kindOf e = 3) :
    walkOK FD FS SD (letK RL RN W (xOf e) 0) t (aOf e) (bOf e)
      (if Nat.land W 3 < 2 then RN (fl W 8 255) else if Nat.land W 3 = 2 then 2 else 0) = true := by
  unfold ruleK at h
  simp only [sB, bAndE] at h
  simp only [bIfE, nIfE, Nat.blt_eq, Nat.beq_eq] at h
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)] at h
  exact h

theorem defK_spec {NF : ℕ} {FD DT : ℕ → ℕ} {b : ℕ} (h : defK NF FD DT b = true) (hb : 2 ≤ b) :
    r32 DT b < NF ∧ kindOf (fdK FD (r32 DT b)) = 0 ∧ bOf (fdK FD (r32 DT b)) = b := by
  unfold defK at h
  simp only [sB, bAndE] at h
  simp only [bIfE, Nat.blt_eq] at h
  rw [ite_eq_right (by omega)] at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

noncomputable def repF {G : Type} [Group G] (gen : ℕ → G) (FD DT : ℕ → ℕ) : ℕ → ℕ → G
  | 0, _ => 1
  | n + 1, c => if c < 2 then 1 else
      repF gen FD DT n (aOf (fdK FD (r32 DT c))) * gen (xOf (fdK FD (r32 DT c)))

section Rep

variable {G : Type} [Group G] (gen : ℕ → G) {FD DT : ℕ → ℕ} {NC : ℕ}

theorem repF_one : ∀ n, repF gen FD DT n 1 = 1
  | 0 => rfl
  | n + 1 => by simp [repF]

theorem repF_stable
    (hdef : ∀ c, 2 ≤ c → c < NC → aOf (fdK FD (r32 DT c)) = 1 ∨
      (2 ≤ aOf (fdK FD (r32 DT c)) ∧ aOf (fdK FD (r32 DT c)) < NC ∧
        r32 DT (aOf (fdK FD (r32 DT c))) < r32 DT c)) :
    ∀ n c, (c = 1 ∨ (2 ≤ c ∧ c < NC ∧ r32 DT c < n)) → ∀ k,
      repF gen FD DT (n + k) c = repF gen FD DT n c
  | n, _, Or.inl rfl, k => by rw [repF_one, repF_one]
  | 0, c, Or.inr ⟨_, _, h⟩, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, c, Or.inr ⟨h1, h2, h3⟩, k => by
    rw [Nat.add_right_comm]
    simp only [repF, ite_eq_right (show ¬ c < 2 by omega)]
    congr 1
    apply repF_stable hdef n
    rcases hdef c h1 h2 with ha | ⟨ha1, ha2, ha3⟩
    · exact Or.inl ha
    · exact Or.inr ⟨ha1, ha2, by omega⟩

end Rep

section Walk

variable {G : Type} [Group G] (gen : ℕ → G) (H : Subgroup G) (rep : ℕ → G) (FD SD : ℕ → ℕ)

def HoldsF (f : ℕ) : Prop :=
  if kindOf (fdK FD f) = 3 then rep (aOf (fdK FD f)) * (rep (bOf (fdK FD f)))⁻¹ ∈ H
  else rep (aOf (fdK FD f)) * gen (xOf (fdK FD f)) * (rep (bOf (fdK FD f)))⁻¹ ∈ H

def WInv (u : ℕ) (L : ℕ → ℕ) (S : ℕ) : Prop :=
  S = failK ∨ ∃ q p, S = stK q p ∧ p < 256 ∧ rep u * prodR (fun i => gen (L i)) p * (rep q)⁻¹ ∈ H

variable {gen H rep FD SD}

theorem step_inv {t : ℕ} (hH : ∀ f < t, HoldsF gen H rep FD f)
    (hx : ∀ f < t, gen (Nat.xor (xOf (fdK FD f)) 1) = (gen (xOf (fdK FD f)))⁻¹)
    {u : ℕ} {L : ℕ → ℕ} (s : ℕ) {S : ℕ} (hS : WInv gen H rep u L S) :
    WInv gen H rep u L (stepK FD SD L t s S) := by
  rcases hS with rfl | ⟨q, p, rfl, hp, hm⟩
  · left
    unfold stepK
    simp only [nIfE, Nat.beq_eq, ↓reduceIte]
  · unfold stepK
    simp only [sN, stK_q hp, stK_p hp]
    simp only [bAndE, nIfE, Nat.beq_eq, Nat.blt_eq, Bool.and_eq_true]
    split_ifs with h0 h1 h2 h3 h4 h5 h6 h7 h8 <;> try (left; rfl)
    all_goals right
    ·
      have hf := hH _ h1
      unfold HoldsF at hf
      rw [ite_eq_left h2, ← h4] at hf
      exact ⟨_, p, rfl, hp, by simpa [mul_assoc] using H.mul_mem hm hf⟩
    ·
      have hf := hH _ h1
      unfold HoldsF at hf
      rw [ite_eq_left h2, ← h5] at hf
      exact ⟨_, p, rfl, hp, by simpa [mul_assoc] using H.mul_mem hm (H.inv_mem hf)⟩
    ·
      have hf := hH _ h1
      unfold HoldsF at hf
      obtain ⟨hp1, hq, hl⟩ := h7
      rw [ite_eq_right h2, ← hq, ← hl] at hf
      refine ⟨_, p + 1, rfl, by omega, ?_⟩
      rw [prodR_succ]
      simpa [mul_assoc] using H.mul_mem hm hf
    ·
      have hf := hH _ h1
      unfold HoldsF at hf
      obtain ⟨hp1, hq, hl⟩ := h8
      rw [ite_eq_right h2, ← hq] at hf
      refine ⟨_, p + 1, rfl, by omega, ?_⟩
      rw [prodR_succ, hl, hx _ h1]
      simpa [mul_assoc] using H.mul_mem hm (H.inv_mem hf)

theorem walk_gen {t u : ℕ} {L : ℕ → ℕ}
    (hstep : ∀ s S, WInv gen H rep u L S → WInv gen H rep u L (stepK FD SD L t s S))
    (g : ℕ → ℕ) : ∀ j S, WInv gen H rep u L S → WInv gen H rep u L
      (Nat.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
        (fun j ih S => strictN (stepK FD SD L t (g j) S) ih) j S) := by
  intro j
  induction j with
  | zero => exact fun S h => h
  | succ j ih =>
    intro S h
    have e : Nat.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
        (fun j ih S => strictN (stepK FD SD L t (g j) S) ih) (j + 1) S =
      strictN (stepK FD SD L t (g j) S) (Nat.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
        (fun j ih S => strictN (stepK FD SD L t (g j) S) ih) j) := rfl
    rw [e, sN]
    exact ih _ (hstep _ _ h)

theorem walkOK_spec {FS : ℕ → ℕ} {t u v n : ℕ} {L : ℕ → ℕ}
    (hstep : ∀ s S, WInv gen H rep u L S → WInv gen H rep u L (stepK FD SD L t s S))
    (h : walkOK FD FS SD L t u v n = true) (hn : n < 256) (hv : v < 16384) :
    rep u * prodR (fun i => gen (L i)) n * (rep v)⁻¹ ∈ H := by
  unfold walkOK at h
  simp only [sB, bAndE, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨_, h2⟩ := h
  have hw : WInv gen H rep u L (walkK FD SD L t (r32 FS t) (Nat.sub (r32 FS (Nat.succ t))
      (r32 FS t)) (stK u (nat_lit 0))) :=
    walk_gen hstep (fun j => Nat.sub (Nat.add (r32 FS t) (Nat.sub (r32 FS (Nat.succ t))
      (r32 FS t))) (Nat.succ j)) (Nat.sub (r32 FS (Nat.succ t)) (r32 FS t)) (stK u (nat_lit 0))
      (Or.inr ⟨u, 0, rfl, by omega, by simp [prodR]⟩)
  rw [h2] at hw
  rcases hw with hf | ⟨q, p, he, hp, hm⟩
  · rw [stK_eq, failK_eq] at hf
    omega
  · rw [stK_eq, stK_eq] at he
    obtain ⟨rfl, rfl⟩ : q = v ∧ p = n := by omega
    exact hm

end Walk

theorem rel_rot {G : Type} [Group G] (gen : ℕ → G) {m : ℕ} {RL RN : ℕ → ℕ} {W x : ℕ}
    (hinv' : ∀ c < 2 * m, gen (Nat.xor c 1) = (gen c)⁻¹) (ho : Nat.land W 3 < 2)
    (hpos : 0 < RN (fl W 8 255))
    (hlet : ∀ i < RN (fl W 8 255), pg 4 15 (RL (fl W 8 255)) i < 2 * m)
    (hrel : prodR (fun i => gen (pg 4 15 (RL (fl W 8 255)) i)) (RN (fl W 8 255)) = 1) :
    prodR (fun p => gen (letK RL RN W x 0 p)) (RN (fl W 8 255)) = 1 := by
  simp only [letK_lo ho, Nat.add_zero]
  by_cases h0 : Nat.land W 3 = 0
  · simp only [ite_eq_left h0]
    exact prodR_rot (f := fun i => gen (pg 4 15 (RL (fl W 8 255)) i)) hpos hrel _
  · simp only [ite_eq_right h0]
    refine prodR_rot (f := fun i => gen (Nat.xor (pg 4 15 (RL (fl W 8 255))
      (RN (fl W 8 255) - 1 - i)) 1)) hpos ?_ _
    rw [← inv_one, ← hrel, ← prodR_rev]
    exact prodR_congr (fun i hi => hinv' _ (hlet _ (by omega)))

theorem emptyRel_fact : factK 1 1 2 0 (fun _ => 0) (fun _ => 0) (fun _ => 1048582) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 = true := by
  quickRfl

theorem emptyRel_head :
    Bool.not (hdK 1 1 1 0 0 0 [[]] [] (fun _ => 0) (fun _ => 0) (fun _ => 1048582)) = true := by
  quickRfl

public section

theorem clogK_sound {m nR NC NF FIN SM z : Nat} {rels : List (List Nat)} {subs : List Nat}
    {RL RN FD FS FW SD DT : Nat → Nat}
    (hh : hdK m nR NF FIN SM z rels subs RL RN FD = true)
    (hd : ∀ b < NC, defK NF FD DT b = true)
    (hf : ∀ t < NF, factK m nR NC SM RL RN FD FS FW SD DT t = true)
    (G : Type) [Group G] (gen : ℕ → G) (hinv : ∀ x < 2 * m, gen (invCode x) = (gen x)⁻¹)
    (hrels : ∀ r ∈ rels, evalWord gen r = 1) :
    gen z ∈ Subgroup.closure (gen '' {c | c ∈ subs}) := by
  unfold hdK at hh
  simp only [sB, bAndE, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at hh
  obtain ⟨hm8, hR, hS, hz, hFIN, hk, ha, hb, hx⟩ := hh
  set H := Subgroup.closure (gen '' {c | c ∈ subs}) with hHdef
  have hinv' : ∀ c < 2 * m, gen (Nat.xor c 1) = (gen c)⁻¹ := fun c hc => by
    rw [xor1 c (by omega)]
    exact hinv c hc
  have hrel : ∀ r < nR, 0 < RN r ∧ RN r < 255 ∧ (∀ i < RN r, pg 4 15 (RL r) i < 2 * m) ∧
      prodR (fun i => gen (pg 4 15 (RL r) i)) (RN r) = 1 := by
    intro r hr
    obtain ⟨w, hw, h1, h2, h3⟩ := relsK_go rels 0 hR r (Nat.zero_le _) hr
    obtain ⟨e1, e2, e3⟩ := wordK_go gen w 0 h3
    simp only [Nat.zero_add] at e1 e2 e3
    refine ⟨h1, h2, fun i hi => e2 i (by omega), ?_⟩
    rw [← e1, ← e3]
    exact hrels w hw
  have hfs : ∀ t < NF, _ := fun t ht => factK_spec (hf t ht)
  have hdef : ∀ c, 2 ≤ c → c < NC → r32 DT c < NF ∧ kindOf (fdK FD (r32 DT c)) = 0 ∧
      bOf (fdK FD (r32 DT c)) = c ∧ (aOf (fdK FD (r32 DT c)) = 1 ∨
        (2 ≤ aOf (fdK FD (r32 DT c)) ∧ aOf (fdK FD (r32 DT c)) < NC ∧
          r32 DT (aOf (fdK FD (r32 DT c))) < r32 DT c)) := by
    intro c hc1 hc2
    obtain ⟨d1, d2, d3⟩ := defK_spec (hd c hc2) hc1
    obtain ⟨f1, f2, -, -, -, -, f7⟩ := hfs _ d1
    obtain ⟨-, -, r3⟩ := rule0 f7 d2
    refine ⟨d1, d2, d3, ?_⟩
    rcases r3 with r3 | r3
    · exact Or.inl r3
    · by_cases ha1 : aOf (fdK FD (r32 DT c)) = 1
      · exact Or.inl ha1
      · exact Or.inr ⟨by omega, f2, r3⟩
  let rep : ℕ → G := repF gen FD DT NF
  have hrep1 : rep 1 = 1 := repF_one gen NF
  have hstab := repF_stable gen (NC := NC) (fun c h1 h2 => (hdef c h1 h2).2.2.2)
  have hrepdef : ∀ c, 2 ≤ c → c < NC →
      rep c = rep (aOf (fdK FD (r32 DT c))) * gen (xOf (fdK FD (r32 DT c))) := by
    intro c hc1 hc2
    obtain ⟨d1, -, -, d4⟩ := hdef c hc1 hc2
    have e1 : rep c = repF gen FD DT (r32 DT c + 1) c := by
      have := hstab (r32 DT c + 1) c (Or.inr ⟨hc1, hc2, by omega⟩) (NF - (r32 DT c + 1))
      rw [Nat.add_sub_cancel' (by omega)] at this
      exact this
    have e2 : rep (aOf (fdK FD (r32 DT c))) =
        repF gen FD DT (r32 DT c) (aOf (fdK FD (r32 DT c))) := by
      have := hstab (r32 DT c) (aOf (fdK FD (r32 DT c))) d4 (NF - r32 DT c)
      rw [Nat.add_sub_cancel' (by omega)] at this
      exact this
    rw [e1, e2]
    simp only [repF, ite_eq_right (show ¬ c < 2 by omega)]
  have hall : ∀ t < NF, HoldsF gen H rep FD t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
    intro ht
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfs t ht
    have hstep : ∀ (u : ℕ) (L : ℕ → ℕ) s S, WInv gen H rep u L S →
        WInv gen H rep u L (stepK FD SD L t s S) := fun u L s S h =>
      step_inv (fun f hft => ih f hft (by omega))
        (fun f hft => hinv' _ (hfs f (by omega)).2.2.2.2.1) s h
    have hk4 := kindOf_lt (fdK FD t)
    unfold HoldsF
    interval_cases hkk : kindOf (fdK FD t)
    ·
      rw [ite_eq_right (by omega)]
      obtain ⟨r1, r2, -⟩ := rule0 f7 hkk
      have := hrepdef _ r1 f4
      rw [r2] at this
      rw [this, mul_inv_cancel]
      exact H.one_mem
    ·
      rw [ite_eq_right (by omega)]
      obtain ⟨r1, r2, r3⟩ := rule1 f7 hkk
      rw [r1, r2, hrep1, one_mul, inv_one, mul_one]
      exact Subgroup.subset_closure ⟨_, subsK_mem hS r3, rfl⟩
    ·
      rw [ite_eq_right (by omega)]
      rcases rule2 f7 hkk with ⟨ho, hl0, hw⟩ | ⟨ho, hw⟩
      · obtain ⟨p1, p2, p3, p4⟩ := hrel _ (f6 ho)
        have hfull := rel_rot gen (x := xOf (fdK FD t)) hinv' ho p1 p3 p4
        obtain ⟨n', hn'⟩ : ∃ n', RN (fl (r32 FW t) 8 255) = n' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos p1).symm⟩
        rw [hn', prodR_succ', hl0] at hfull
        have hX := eq_inv_of_mul_eq_one_right hfull
        have hwm := walkOK_spec (hstep _ _) hw (by omega) (aOf_lt _)
        rw [hn', Nat.add_sub_cancel] at hwm
        have e : prodR (fun i => gen (letK RL RN (r32 FW t) (xOf (fdK FD t)) 1 i)) n' =
            prodR (fun i => gen (letK RL RN (r32 FW t) (xOf (fdK FD t)) 0 (i + 1))) n' :=
          prodR_congr (fun i _ => by rw [letK_lo ho, letK_lo ho, Nat.add_zero])
        rw [e, hX] at hwm
        simpa [mul_assoc] using H.inv_mem hwm
      · have hwm := walkOK_spec (hstep _ _) hw (by omega) (bOf_lt _)
        rw [prodR_succ, prodR_zero, one_mul, letK_hi (by omega), ite_eq_right (by omega)] at hwm
        exact hwm
    ·
      rw [ite_eq_left rfl]
      have hw := rule3 f7 hkk
      by_cases ho : Nat.land (r32 FW t) 3 < 2
      · rw [ite_eq_left ho] at hw
        obtain ⟨p1, p2, p3, p4⟩ := hrel _ (f6 ho)
        have hwm := walkOK_spec (hstep _ _) hw (by omega) (bOf_lt _)
        rw [rel_rot gen hinv' ho p1 p3 p4, mul_one] at hwm
        exact hwm
      · rw [ite_eq_right ho] at hw
        by_cases h2 : Nat.land (r32 FW t) 3 = 2
        · rw [ite_eq_left h2] at hw
          have hwm := walkOK_spec (hstep _ _) hw (by omega) (bOf_lt _)
          rw [prodR_succ, prodR_succ, prodR_zero, one_mul, letK_hi ho, letK_hi ho, ite_eq_left h2,
            ite_eq_left h2, ite_eq_left rfl, ite_eq_right (by omega), hinv' _ f5, inv_mul_cancel, mul_one] at hwm
          exact hwm
        · rw [ite_eq_right h2] at hw
          have hwm := walkOK_spec (hstep _ _) hw (by omega) (bOf_lt _)
          rw [prodR_zero, mul_one] at hwm
          exact hwm
  have hfin := hall FIN hFIN
  unfold HoldsF at hfin
  rw [ite_eq_right (by omega), ha, hb, hx, hrep1, one_mul, inv_one, mul_one] at hfin
  exact hfin

end

end CFSG.KC.CLog
