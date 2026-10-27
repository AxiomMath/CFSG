module

public import Certificates.Data.Kernel.PopF
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.PopF

open CFSG.KC.Loop CFSG.KC.PopF

@[expose] def DS (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % 2 ^ w + DS w n (x / 2 ^ w)

@[expose] def BD (w c : Nat) : Nat → Nat → Prop
  | 0, _ => True
  | n + 1, x => x % 2 ^ w ≤ c ∧ BD w c n (x / 2 ^ w)

@[expose] def MM (w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ (2 * w) * MM w n + (2 ^ w - 1)

@[expose] def stp (w n x : Nat) : Nat := (x &&& MM w n) + ((x >>> w) &&& MM w n)

theorem land_split {s a c : Nat} (ha : a < 2 ^ s) (hc : c < 2 ^ s) (b d : Nat) :
    (2 ^ s * b + a) &&& (2 ^ s * d + c) = 2 ^ s * (b &&& d) + (a &&& c) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow a hc), Nat.testBit_and, Nat.testBit_and]
  split <;> rfl

theorem pow_two_mul (w : Nat) : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by
  rw [Nat.two_mul, Nat.pow_add]

theorem low_lt (w : Nat) : 2 ^ w - 1 < 2 ^ (2 * w) := by
  have h1 : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 0 < 2 ^ w := Nat.two_pow_pos w
  omega

theorem land_MM_succ (w n x : Nat) :
    x &&& MM w (n + 1) = 2 ^ (2 * w) * (x / 2 ^ (2 * w) &&& MM w n) + x % 2 ^ w := by
  have hx := Nat.div_add_mod x (2 ^ (2 * w))
  have hm : x % 2 ^ (2 * w) < 2 ^ (2 * w) := Nat.mod_lt _ (Nat.two_pow_pos _)
  conv_lhs => rw [← hx]
  rw [MM, land_split hm (low_lt w), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem stp_zero (w x : Nat) : stp w 0 x = 0 := by
  simp [stp, MM]

theorem stp_succ (w n x : Nat) :
    stp w (n + 1) x = 2 ^ (2 * w) * stp w n (x / 2 ^ (2 * w)) + (x % 2 ^ w + x / 2 ^ w % 2 ^ w) := by
  unfold stp
  rw [land_MM_succ, Nat.shiftRight_eq_div_pow, land_MM_succ, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ w) (2 ^ (2 * w))]
  ring

theorem stp_spec {w c : Nat} (hc : 2 * c < 2 ^ (2 * w)) :
    ∀ n x, BD w c (2 * n) x →
      DS (2 * w) n (stp w n x) = DS w (2 * n) x ∧ BD (2 * w) (2 * c) n (stp w n x) ∧
        stp w n x < 2 ^ (2 * w * n)
  | 0, x, _ => by
    rw [stp_zero]
    exact ⟨rfl, trivial, by simp⟩
  | n + 1, x, h => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring] at h ⊢
    obtain ⟨h0, h1, h2⟩ := h
    have e : x / 2 ^ w / 2 ^ w = x / 2 ^ (2 * w) := by rw [Nat.div_div_eq_div_mul, ← pow_two_mul]
    rw [e] at h2
    obtain ⟨i1, i2, i3⟩ := stp_spec hc n _ h2
    have hs : x % 2 ^ w + x / 2 ^ w % 2 ^ w < 2 ^ (2 * w) := by omega
    have hp : 0 < 2 ^ (2 * w) := Nat.two_pow_pos _
    have m1 : stp w (n + 1) x % 2 ^ (2 * w) = x % 2 ^ w + x / 2 ^ w % 2 ^ w := by
      rw [stp_succ, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
    have m2 : stp w (n + 1) x / 2 ^ (2 * w) = stp w n (x / 2 ^ (2 * w)) := by
      rw [stp_succ, Nat.mul_add_div hp, Nat.div_eq_of_lt hs, Nat.add_zero]
    refine ⟨?_, ?_, ?_⟩
    · simp only [DS]
      rw [m1, m2, i1, e]
      ring
    · simp only [BD]
      rw [m1, m2]
      exact ⟨by omega, i2⟩
    · rw [stp_succ]
      have : stp w n (x / 2 ^ (2 * w)) + 1 ≤ 2 ^ (2 * w * n) := i3
      calc 2 ^ (2 * w) * stp w n (x / 2 ^ (2 * w)) + (x % 2 ^ w + x / 2 ^ w % 2 ^ w)
          < 2 ^ (2 * w) * (stp w n (x / 2 ^ (2 * w)) + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        _ ≤ 2 ^ (2 * w) * 2 ^ (2 * w * n) := Nat.mul_le_mul_left _ this
        _ = 2 ^ (2 * w * (n + 1)) := by rw [← Nat.pow_add]; ring_nf

theorem onesF_eq (n : Nat) : onesF n = 2 ^ n - 1 := by
  unfold onesF
  rw [show Nat.shiftLeft 1 n = 1 <<< n from rfl, Nat.one_shiftLeft]
  rfl

@[expose] def GS (w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ (2 * w) * GS w n + 1

theorem GS_mul (w : Nat) : ∀ n, GS w n * (2 ^ (2 * w) - 1) = 2 ^ (2 * w * n) - 1
  | 0 => by simp [GS]
  | n + 1 => by
    have ih := GS_mul w n
    simp only [GS]
    rw [show 2 * w * (n + 1) = 2 * w + 2 * w * n by ring, Nat.pow_add]
    obtain ⟨p, hp⟩ : ∃ p, 2 ^ (2 * w) = p + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)).symm⟩
    obtain ⟨q, hq⟩ : ∃ q, 2 ^ (2 * w * n) = q + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)).symm⟩
    rw [hp, hq] at ih ⊢
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [show (p + 1) * (q + 1) = (p * q + p + q) + 1 by ring, Nat.add_sub_cancel, ← ih]
    ring

theorem GS_low (w : Nat) : ∀ n, GS w n * (2 ^ w - 1) = MM w n
  | 0 => by simp [GS, MM]
  | n + 1 => by
    simp only [GS, MM]
    rw [← GS_low w n]
    ring

theorem lowM_eq {k n : Nat} : lowM (2 * 2 ^ k * n) k = MM (2 ^ k) n := by
  unfold lowM
  have e1 : Nat.shiftLeft 2 k = 2 * 2 ^ k := by
    rw [show Nat.shiftLeft 2 k = 2 <<< k from rfl, Nat.shiftLeft_eq, Nat.mul_comm]
  have e2 : Nat.shiftLeft 1 k = 2 ^ k := by
    rw [show Nat.shiftLeft 1 k = 1 <<< k from rfl, Nat.one_shiftLeft]
  rw [e1, e2, onesF_eq, onesF_eq, onesF_eq]
  have hpos : 0 < 2 ^ (2 * 2 ^ k) - 1 := by
    have : 2 ≤ 2 ^ (2 * 2 ^ k) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (2 * 2 ^ k) := Nat.pow_le_pow_right (by decide) (by have := Nat.two_pow_pos k; omega)
    omega
  have hd : (2 ^ (2 * 2 ^ k * n) - 1) / (2 ^ (2 * 2 ^ k) - 1) = GS (2 ^ k) n :=
    Nat.div_eq_of_eq_mul_left hpos (GS_mul _ n).symm
  change (2 ^ (2 * 2 ^ k * n) - 1) / (2 ^ (2 * 2 ^ k) - 1) * (2 ^ 2 ^ k - 1) = _
  rw [hd, GS_low]

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem runF_succ (W n i x : Nat) : runF W (n + 1) i x = runF W n (i + 1) (stepF W i x) :=
  strictN_eq _ _

theorem stepF_eq {k n : Nat} (x : Nat) : stepF (2 * 2 ^ k * n) k x = stp (2 ^ k) n x := by
  unfold stepF
  rw [lowM_eq]
  have e2 : Nat.shiftLeft 1 k = 2 ^ k := by
    rw [show Nat.shiftLeft 1 k = 1 <<< k from rfl, Nat.one_shiftLeft]
  rw [e2]
  rfl

theorem BD_one (m : Nat) : ∀ x, BD 1 1 m x := by
  induction m with
  | zero => intro x; trivial
  | succ m ih =>
    intro x
    exact ⟨by have := Nat.mod_lt x (by decide : 2 > 0); simp only [Nat.pow_one]; omega, ih _⟩

theorem DS_one (m : Nat) : ∀ y, DS 1 m y = ((List.range m).filter y.testBit).length := by
  induction m with
  | zero => intro y; rfl
  | succ m ih =>
    intro y
    rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have e : (y.testBit ∘ Nat.succ) = (y / 2).testBit := by
      funext i
      rw [Function.comp_apply, Nat.testBit_div_two]
    rw [e]
    simp only [DS, Nat.pow_one]
    rw [ih, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one y with h | h
    · simp [h]
    · simp [h]
      omega

theorem runF_spec {L C : Nat} :
    ∀ n i x, i + n = L → DS (2 ^ i) (2 ^ (L - i)) x = C → BD (2 ^ i) (2 ^ i) (2 ^ (L - i)) x →
      (0 < i → x < 2 ^ 2 ^ L) → runF (2 ^ L) n i x % 2 ^ 2 ^ L = C ∧ (0 < L → runF (2 ^ L) n i x < 2 ^ 2 ^ L)
  | 0, i, x, hn, hD, _, hb => by
    have hi : i = L := by omega
    subst hi
    simp only [Nat.sub_self, Nat.pow_zero] at hD
    change x % 2 ^ 2 ^ i + 0 = C at hD
    exact ⟨by rw [← hD]; rfl, fun h => hb h⟩
  | n + 1, i, x, hn, hD, hB, _ => by
    rw [runF_succ]
    have hL : 2 ^ (L - i) = 2 * 2 ^ (L - (i + 1)) := by
      rw [show L - i = L - (i + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hW : 2 ^ L = 2 * 2 ^ i * 2 ^ (L - (i + 1)) := by
      rw [show L = i + 1 + (L - (i + 1)) by omega, Nat.pow_add, Nat.pow_succ]
      rw [show i + 1 + (L - (i + 1)) - (i + 1) = L - (i + 1) by omega]
      ring
    have hw : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
    have hc : 2 * 2 ^ i < 2 ^ (2 * 2 ^ i) := by
      rw [← hw]
      exact Nat.pow_lt_pow_right (by decide) Nat.lt_two_pow_self
    rw [hL] at hD hB
    obtain ⟨s1, s2, s3⟩ := stp_spec hc _ x hB
    refine runF_spec n (i + 1) _ (by omega) ?_ ?_ ?_
    · rw [hW, stepF_eq, hw, s1, hD]
    · rw [hW, stepF_eq, hw]
      exact s2
    · intro _
      rw [hW, stepF_eq]
      exact s3

theorem pcF_eq {L : Nat} (hL : 0 < L) (y : Nat) :
    pcF L y = ((List.range (2 ^ L)).filter y.testBit).length := by
  have e : Nat.shiftLeft 1 L = 2 ^ L := by
    rw [show Nat.shiftLeft 1 L = 1 <<< L from rfl, Nat.one_shiftLeft]
  have h := runF_spec (L := L) (C := ((List.range (2 ^ L)).filter y.testBit).length) L 0 y
    (by omega) (by rw [Nat.pow_zero, Nat.sub_zero]; exact DS_one _ y)
    (by rw [Nat.pow_zero]; exact BD_one _ y) (fun h => absurd h (Nat.lt_irrefl 0))
  unfold pcF
  rw [e]
  change runF (2 ^ L) L 0 y = _
  rw [← h.1, Nat.mod_eq_of_lt (h.2 hL)]

end CFSG.KS.PopF

end
