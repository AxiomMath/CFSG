module

public import CFSG.Certificates.Kernel.LocalCompOps3Snd.Bridge
public import Certificates.Data.Kernel.LocalComp.Replay
import all CFSG.Certificates.Kernel.LocalQT.Steps

public section

namespace CFSG.KC.LocalComp.Ops3Snd

open CFSG.KC.LQT CFSG.KS.Ord CFSG.SectionRank CFSG.SectionRank.Native CFSG.KC.LocalComp.Replay
open scoped Matrix

structure Vals (c : Lay) (Vk P : ℕ → ℕ) (N : ℕ) : Prop where
  hc : c.ok = true
  hp : c.p = 3
  hN : N ≤ 1048576
  canon : ∀ n, (n < N ∨ n < 3) → Canon c.p c.d c.w (Vk n)
  step : StepsTo (stepOK c Vk P) N
  two : mat3 c (Vk 2) = 1

theorem vals_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {LA LB : List Char}
    {Vk P : ℕ → ℕ} {N : ℕ} (hN : N ≤ 1048576) (hA : decOK c (Vk 0) LA = true)
    (hB : decOK c (Vk 1) LB = true) (h1 : Vk 2 = c.ONE) (hs : StepsTo (stepOK c Vk P) N) :
    Vals c Vk P N := by
  refine ⟨hc, hp, hN, ?_, hs, ?_⟩
  · intro n hn
    rcases hn with hn | hn
    · exact (SecS.vals_sound c hc hA hB h1 hs n hn).1
    · rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
      · exact (mat3_decode c hc hp hA).1
      · exact (mat3_decode c hc hp hB).1
      · rw [h1]
        exact (mat3_one c hc hp).1
  · rw [h1]
    exact (mat3_one c hc hp).2

theorem land_add_shift {a b : ℕ} (ha : a < 1048576) :
    Nat.land (a + 1048576 * b) 1048575 = a ∧ Nat.shiftRight (a + 1048576 * b) 20 = b := by
  have h20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  have hl : Nat.land (a + 1048576 * b) 1048575 = (a + 1048576 * b) % 2 ^ 20 := by
    change (a + 1048576 * b) &&& (2 ^ 20 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  have hs : Nat.shiftRight (a + 1048576 * b) 20 = (a + 1048576 * b) / 2 ^ 20 := by
    change (a + 1048576 * b) >>> 20 = _
    rw [Nat.shiftRight_eq_div_pow]
  rw [h20] at hl hs
  constructor
  · rw [hl]
    omega
  · rw [hs]
    omega

theorem stepOK_of_pair {c : Lay} {Vk P : ℕ → ℕ} {n a b : ℕ} (h : stepOK c Vk P n = true)
    (hP : P n = a + 1048576 * b) (ha : a < 1048576) :
    a < n ∧ b < n ∧ Vk n = c.mul (Vk a) (Vk b) := by
  obtain ⟨h1, h2, h3⟩ : Nat.land (P n) 1048575 < n ∧ Nat.shiftRight (P n) 20 < n ∧
      Vk n = c.mul (Vk (Nat.land (P n) 1048575)) (Vk (Nat.shiftRight (P n) 20)) := by
    unfold stepOK at h
    simp only [SecS.strictB_eq] at h
    obtain ⟨ha', h⟩ := SecS.andT h
    obtain ⟨hb', h⟩ := SecS.andT h
    exact ⟨Nat.blt_eq.mp ha', Nat.blt_eq.mp hb', Nat.eq_of_beq_eq_true h⟩
  rw [hP] at h1 h2 h3
  rw [(land_add_shift (b := b) ha).1] at h1 h3
  rw [(land_add_shift (b := b) ha).2] at h2 h3
  exact ⟨h1, h2, h3⟩

theorem stepOK_spec {c : Lay} {Vk P : ℕ → ℕ} {n : ℕ} (h : stepOK c Vk P n = true) :
    Nat.land (P n) 1048575 < n ∧ Nat.shiftRight (P n) 20 < n ∧
      Vk n = c.mul (Vk (Nat.land (P n) 1048575)) (Vk (Nat.shiftRight (P n) 20)) := by
  unfold stepOK at h
  simp only [SecS.strictB_eq] at h
  obtain ⟨ha, h⟩ := SecS.andT h
  obtain ⟨hb, h⟩ := SecS.andT h
  exact ⟨Nat.blt_eq.mp ha, Nat.blt_eq.mp hb, Nat.eq_of_beq_eq_true h⟩

theorem expoK_spec {c : Lay} {Vk P : ℕ → ℕ} {N : ℕ} (hV : Vals c Vk P N) (a : ℕ) :
    ∀ (f t : ℕ), (t < N ∨ t ≤ 2) → expoK P a f t < expoFail →
      mat3 c (Vk t) = mat3 c (Vk a) ^ expoK P a f t := by
  intro f
  induction f with
  | zero =>
    intro t _ h
    rw [expoK] at h
    exact absurd h (lt_irrefl _)
  | succ f ih =>
    intro t ht h
    rw [expoK] at h ⊢
    by_cases h1 : t = a
    · rw [if_pos h1] at h ⊢
      rw [h1, pow_one]
    · rw [if_neg h1] at h ⊢
      by_cases h2 : t = 2
      · rw [if_pos h2] at h ⊢
        rw [h2, hV.two, pow_zero]
      · rw [if_neg h2] at h ⊢
        by_cases h3 : t < 2
        · rw [if_pos h3] at h
          exact absurd h (lt_irrefl _)
        · rw [if_neg h3] at h ⊢
          have ht3 : 3 ≤ t := by omega
          have htN : t < N := by
            rcases ht with h' | h' <;> omega
          have hst : stepOK c Vk P t = true := hV.step t ht3 htN
          obtain ⟨ha, hb, hVt⟩ := stepOK_spec hst
          have hcA : Canon c.p c.d c.w (Vk (Nat.land (P t) 1048575)) :=
            hV.canon (Nat.land (P t) 1048575) (Or.inl (by omega))
          have hcB : Canon c.p c.d c.w (Vk (Nat.shiftRight (P t) 20)) :=
            hV.canon (Nat.shiftRight (P t) 20) (Or.inl (by omega))
          obtain ⟨-, hmul⟩ := mat3_mul c hV.hc hV.hp hcA hcB
          have ihA := ih (Nat.land (P t) 1048575) (Or.inl (by omega)) (by omega)
          have ihB := ih (Nat.shiftRight (P t) 20) (Or.inl (by omega)) (by omega)
          rw [hVt, hmul, ihA, ihB, ← pow_add]


end CFSG.KC.LocalComp.Ops3Snd

end
