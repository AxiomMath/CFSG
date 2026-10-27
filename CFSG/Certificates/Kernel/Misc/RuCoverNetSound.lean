module

public import Certificates.Data.Kernel.Misc.RuCoverNet
public import CFSG.Certificates.Kernel.YModel.ChainSem
public import CFSG.Certificates.Kernel.Misc.Coset.ActPermSound
public import Mathlib.Algebra.Order.Ring.Star
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.Misc.RuCoverNet

open CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.YModel
  CFSG.KC.YModel.Sem CFSG.KC.YModel.Sch CFSG.KC.YModel.Chain CFSG.KC.MiscCoset

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem line_succ (A : Nat → Nat) (c m : Nat) :
    line A c (m + 1) = line A c m ||| (A (m * 6 + c) <<< (32 * m)) := by
  have e : line A c (m + 1) = strictN (line A c m) (fun a => Nat.lor a
      (Nat.shiftLeft (A (Nat.add (Nat.mul m (nat_lit 6)) c)) (Nat.mul (nat_lit 32) m))) := rfl
  rw [e, strictN_eq']
  rfl

theorem line_spec (A : Nat → Nat) (c : Nat) : ∀ m, (∀ i < m, A (i * 6 + c) < 2 ^ 32) →
    line A c m < 2 ^ (32 * m) ∧ ∀ i < m, fieldAt 32 (line A c m) i = A (i * 6 + c)
  | 0, _ => ⟨by simp [line], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | m + 1, hA => by
    obtain ⟨hlt, hf⟩ := line_spec A c m fun i hi => hA i (by omega)
    have hv := hA m (by omega)
    have hle : ∀ t, 32 * m ≤ t → line A c m < 2 ^ t := fun t ht =>
      lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) ht)
    rw [line_succ]
    refine ⟨?_, fun i hi => ?_⟩
    · apply Nat.or_lt_two_pow (hle _ (by omega))
      rw [Nat.shiftLeft_eq, show 32 * (m + 1) = 32 + 32 * m by ring, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right hv (Nat.two_pow_pos _)
    · apply Nat.eq_of_testBit_eq
      intro j
      rw [testBit_fieldAt, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hj : j < 32
      · by_cases him : i < m
        · have h1 : ¬ (32 * i + j ≥ 32 * m) := by omega
          rw [← hf i him, testBit_fieldAt]
          simp [hj, h1]
        · have e : i = m := by omega
          rw [e, Nat.testBit_lt_two_pow (hle (32 * m + j) (by omega))]
          simp [hj]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hA i hi) (Nat.pow_le_pow_right (by norm_num)
          (by omega : 32 ≤ j)))]
        simp [hj]

theorem F_field {A : Nat → Nat} {c : Nat} (hA : ∀ i < 16240, A (i * 6 + c) < 2 ^ 32) (i : Nat)
    (hi : i < 16240) : fieldAt 32 (F A c) i = A (i * 6 + c) :=
  (line_spec A c 16240 hA).2 i hi

theorem letter_perm {A : Nat → Nat} {N : Nat → Nat} {σ : Fin 3 → Equiv.Perm (Fin 16240)}
    (hA : Act.Rep A 3 16240 σ)
    (h : ∀ g < 3, letOK 14 16240 (F A (Nat.add (Nat.mul 2 g) 1)) (N g) = true) (g : Fin 3) :
    Good 14 16240 (N g) ∧ netPerm 14 16240 (N g) = (σ g)⁻¹ := by
  obtain ⟨hn, hv, hf, hfix⟩ := letOK_spec (by norm_num) (h g.val g.2)
  have hG : Good 14 16240 (N g) := ⟨hn, hv, hfix⟩
  have e2 : ∀ i, i * 6 + Nat.add (Nat.mul 2 g.val) 1 = i * (3 + 3) + (2 * g.val + 1) := by
    intro i
    rfl
  have hb : ∀ i < 16240, A (i * 6 + Nat.add (Nat.mul 2 g.val) 1) < 2 ^ 32 := fun i hi => by
    rw [e2, (hA g ⟨i, hi⟩).2]
    exact lt_trans ((σ g)⁻¹ ⟨i, hi⟩).2 (by norm_num)
  refine ⟨hG, Equiv.ext fun x => Fin.ext ?_⟩
  rw [netPerm_apply hG, ← hf x.val x.2, F_field hb x.val x.2, e2]
  exact (hA g x).2

theorem chain_spec {k n w m E : Nat} {T WP WL : Nat → Nat} (hn : n ≤ 2 ^ k) (hm : 0 < m)
    (hT : ∀ c < m, Good k n (T c)) (hw : ∀ i < E, wordOK k w m T WP WL i = true) :
    ∀ j < m + E, Good k n (T j) ∧
      ∀ i, j = m + i → netPerm k n (T j) = cpermL k n T (codesL w (WP i) (WL i)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjm : j < m
    · exact ⟨hT j hjm, fun i e => by omega⟩
    · obtain ⟨i, rfl⟩ : ∃ i, j = m + i := ⟨j - m, by omega⟩
      have hi : i < E := by omega
      have hcodes := codesOK_spec _ _ (wordOK_spec (hw i hi)).2.1
      have hg : CodesGood k n T (codesL w (WP i) (WL i)) := fun x hx => by
        obtain ⟨-, h2⟩ := hcodes x hx
        generalize x >>> 1 = y at h2 ⊢
        exact (ih _ (by omega) (by omega)).1
      obtain ⟨hG, hp⟩ := word_good hn (hw i hi) hg
      refine ⟨hG, fun i' e => ?_⟩
      obtain rfl : i' = i := by omega
      exact hp

end CFSG.KC.Misc.RuCoverNet

end
