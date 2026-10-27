module

public import Certificates.Data.Kernel.L34Cov.T1

public section

namespace CFSG.KC.L34Cov

open Subgroup CFSG.KC.L34W

section Group

variable {G : Type*} [Group G]

theorem mul_spec_of_gens (x : ℕ → G) (m : ℕ → ℕ → ℕ) (z : ℕ → ℕ → G) (gs : List ℕ)
    (hz : ∀ a b, z a b ∈ center G) (hx0 : x 0 = 1)
    (hlt : ∀ k < 64, ∀ l < 64, m k l < 64)
    (hzero : ∀ k < 64, m k 0 = k ∧ z k 0 = 1)
    (hcol : ∀ k < 64, ∀ g ∈ gs, x k * x g = x (m k g) * z k g)
    (has : ∀ k < 64, ∀ l < 64, ∀ g ∈ gs, m (m k l) g = m k (m l g) ∧
      z k l * z (m k l) g = z k (m l g) * z l g)
    (hreach : ∀ S : ℕ → Prop, S 0 → (∀ l < 64, S l → ∀ g ∈ gs, S (m l g)) → ∀ l < 64, S l) :
    ∀ k < 64, ∀ l < 64, x k * x l = x (m k l) * z k l := by
  have hc : ∀ a b (y : G), z a b * y = y * z a b := fun a b y => (mem_center_iff.1 (hz a b) y).symm
  intro k hk l hl
  revert k
  refine hreach (fun l => ∀ k < 64, x k * x l = x (m k l) * z k l) ?_ ?_ l hl
  · intro k hk
    rw [hx0, (hzero k hk).1, (hzero k hk).2]
  · intro l hl ih g hg k hk
    have h1 := hcol l hl g hg
    have h2 := ih k hk
    have h3 := hcol (m k l) (hlt k hk l hl) g hg
    obtain ⟨e1, e2⟩ := has k hk l hl g hg
    have hxl : x (m l g) = x l * x g * (z l g)⁻¹ := by rw [h1]; group
    calc x k * x (m l g) = x k * x l * x g * (z l g)⁻¹ := by rw [hxl]; group
      _ = x (m k l) * x g * z k l * (z l g)⁻¹ := by rw [h2, mul_assoc (x (m k l)), hc k l, ← mul_assoc]
      _ = x (m (m k l) g) * (z k l * z (m k l) g) * (z l g)⁻¹ := by
        rw [h3, mul_assoc (x _) (z _ _), ← hc k l (z (m k l) g), mul_assoc]
      _ = x (m k (m l g)) * z k (m l g) := by rw [e1, e2]; group

end Group

theorem testBit_imgBits {T : ℕ → ℕ} {l x : ℕ} (h : (imgBits T l).testBit x = true) :
    ∃ g ∈ [1, 2, 16, 20], ent T l g / 48 = x := by
  unfold imgBits at h
  change ((1 <<< (ent T l 1 / 48) ||| 1 <<< (ent T l 2 / 48)) |||
    (1 <<< (ent T l 16 / 48) ||| 1 <<< (ent T l 20 / 48))).testBit x = true at h
  simp only [Nat.testBit_lor, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
    decide_eq_true_eq] at h
  rcases h with (h | h) | (h | h) <;> exact ⟨_, by simp, h⟩

theorem testBit_stepM {T : ℕ → ℕ} {M x : ℕ} (h : (stepM T M).testBit x = true) :
    M.testBit x = true ∨ ∃ l < 64, M.testBit l = true ∧ ∃ g ∈ [1, 2, 16, 20], ent T l g / 48 = x := by
  unfold stepM at h
  suffices H : ∀ (L : List ℕ) (acc : ℕ), (∀ l ∈ L, l < 64) →
      (L.foldl (fun acc l => cond (M.testBit l) (acc ||| imgBits T l) acc) acc).testBit x = true →
      acc.testBit x = true ∨ ∃ l < 64, M.testBit l = true ∧ ∃ g ∈ [1, 2, 16, 20], ent T l g / 48 = x by
    rcases H _ M (fun l hl => List.mem_range.1 hl) h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  intro L
  induction L with
  | nil => intro acc _ h; exact Or.inl h
  | cons l L ih =>
    intro acc hL h
    rw [List.foldl_cons] at h
    rcases ih _ (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')) h with h' | h'
    · cases hb : M.testBit l
      · rw [hb, cond_false] at h'
        exact Or.inl h'
      · rw [hb, cond_true, Nat.testBit_lor, Bool.or_eq_true] at h'
        rcases h' with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨l, hL l List.mem_cons_self, hb, testBit_imgBits h'⟩
    · exact Or.inr h'

theorem reach_of_reachM {T : ℕ → ℕ} (S : ℕ → Prop) (h0 : S 0)
    (hstep : ∀ l < 64, S l → ∀ g ∈ [1, 2, 16, 20], S (ent T l g / 48)) :
    ∀ n x, (reachM T n).testBit x = true → S x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have : x = 0 := by
      rw [reachM, Nat.testBit_one_eq_true_iff_self_eq_zero] at hx
      exact hx
    rw [this]
    exact h0
  | succ n ih =>
    intro x hx
    rw [reachM] at hx
    rcases testBit_stepM hx with h | ⟨l, hl, hb, g, hg, rfl⟩
    · exact ih x h
    · exact hstep l hl (ih l hb) g hg

theorem reach_all {T : ℕ → ℕ} {n : ℕ} (h : reachM T n = 2 ^ 64 - 1) (S : ℕ → Prop) (h0 : S 0)
    (hstep : ∀ l < 64, S l → ∀ g ∈ [1, 2, 16, 20], S (ent T l g / 48)) :
    ∀ l < 64, S l := by
  intro l hl
  refine reach_of_reachM S h0 hstep n l ?_
  rw [h, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hl

end CFSG.KC.L34Cov

end
