module

public import Certificates.Data.Kernel.SporSch.Co1RankCoord
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.KS.SporSch.Co1RankRC

open CFSG.KC.Loop CFSG.KC.Co1RankCoord

@[expose] def rowV (W A t : ℕ) : Fin W → ZMod 2 := fun j => if A.testBit (W * t + j) then 1 else 0

@[expose] noncomputable def rk (r W A : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun t : Fin r => rowV W A t))

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem mask_eq (n : ℕ) : CFSG.KC.Co1RankCoord.mask n = 2 ^ n - 1 := by
  change (1 <<< n) - 1 = _
  rw [Nat.one_shiftLeft]

theorem testBit_split {n X Y : ℕ} (hY : Y < 2 ^ n) (j : ℕ) :
    (2 ^ n * X + Y).testBit j = if j < n then Y.testBit j else X.testBit (j - n) := by
  have e : 2 ^ n * X + Y = (X <<< n) ||| Y := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hY, Nat.shiftLeft_eq, mul_comm]
  rw [e, Nat.testBit_or, Nat.testBit_shiftLeft]
  split_ifs with h
  · simp [show ¬ j ≥ n by omega]
  · have : Y.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hY (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [this, show j ≥ n by omega]

@[expose] def rep (W : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => 2 ^ W * rep W r + 1

theorem rep_mul (W : ℕ) : ∀ r, (2 ^ W - 1) * rep W r = 2 ^ (W * r) - 1
  | 0 => by simp [rep]
  | r + 1 => by
    have ih := rep_mul W r
    have h1 : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (W * r) := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ (W * (r + 1)) := Nat.one_le_two_pow
    rw [rep]
    zify [h1, h2, h3] at ih ⊢
    rw [Nat.mul_succ, pow_add]
    push_cast
    linear_combination (2 : ℤ) ^ W * ih

theorem div_mask {r W : ℕ} (hW : 0 < W) :
    Nat.div (CFSG.KC.Co1RankCoord.mask (Nat.mul r W)) (CFSG.KC.Co1RankCoord.mask W) = rep W r := by
  have hpos : 0 < 2 ^ W - 1 := by
    have := Nat.one_lt_two_pow (n := W) (by omega)
    omega
  change CFSG.KC.Co1RankCoord.mask (r * W) / CFSG.KC.Co1RankCoord.mask W = _
  rw [mask_eq, mask_eq]
  refine Nat.div_eq_of_eq_mul_left hpos ?_
  rw [mul_comm (rep W r), rep_mul, mul_comm]

theorem testBit_rep {W : ℕ} (hW : 0 < W) : ∀ r j,
    (rep W r).testBit j = decide (j < W * r ∧ j % W = 0)
  | 0, j => by simp [rep]
  | r + 1, j => by
    rw [rep, testBit_split (Nat.one_lt_two_pow (by omega)) j]
    split_ifs with h
    · rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow, Nat.mod_eq_of_lt h]
      have : j < W * (r + 1) := lt_of_lt_of_le h (Nat.le_mul_of_pos_right W (by omega))
      by_cases hj : j = 0
      · simp [hj, hW]
      · simp [hj, Ne.symm hj]
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
      rw [testBit_rep hW r, Nat.add_sub_cancel_left, Nat.add_mod_left, Nat.mul_succ]
      simp only [decide_eq_decide]
      omega

theorem lowBit {C : ℕ} (hC : C ≠ 0) :
    ∃ a, Nat.xor C (Nat.land C (Nat.sub C 1)) = 2 ^ a ∧ C.testBit a = true := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hC
  obtain ⟨q, rfl⟩ := hm
  have h0 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hlt : 2 ^ a < 2 ^ (a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have e1 : 2 ^ a * (2 * q + 1) = 2 ^ (a + 1) * q + 2 ^ a := by ring
  have e2 : 2 ^ a * (2 * q + 1) - 1 = 2 ^ (a + 1) * q + (2 ^ a - 1) := by
    rw [e1]
    omega
  refine ⟨a, Nat.eq_of_testBit_eq fun j => ?_, ?_⟩
  · change (2 ^ a * (2 * q + 1) ^^^ (2 ^ a * (2 * q + 1) &&& (2 ^ a * (2 * q + 1) - 1))).testBit j = _
    rw [Nat.testBit_xor, Nat.testBit_and, e2, e1, testBit_split hlt, testBit_split (by omega),
      Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
    split_ifs with h
    · rcases lt_trichotomy j a with h' | rfl | h'
      · simp [h', show a ≠ j by omega]
      · simp
      · simp [show a ≠ j by omega, show ¬ j < a by omega]
    · simp [show a ≠ j by omega]
  · rw [e1, testBit_split hlt, if_pos (by omega), Nat.testBit_two_pow_self]

theorem testBit_mul_sparse {W m : ℕ} (hW : 0 < W) (hm : m < 2 ^ W) :
    ∀ C, (∀ j, C.testBit j = true → j % W = 0) → ∀ j,
      (C * m).testBit j = (C.testBit (W * (j / W)) && m.testBit (j % W)) := by
  intro C
  induction C using Nat.strong_induction_on with
  | _ C ih =>
  intro hC j
  rcases Nat.eq_zero_or_pos C with rfl | hpos
  · simp
  have hc0 : C % 2 ^ W = if C.testBit 0 then 1 else 0 := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_mod_two_pow]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · split_ifs with h0 <;> simp [h0, hW]
    · have : (decide (i < W) && C.testBit i) = false := by
        by_cases hiW : i < W
        · cases hb : C.testBit i
          · simp
          · have := hC i hb
            rw [Nat.mod_eq_of_lt hiW] at this
            omega
        · simp [hiW]
      rw [this]
      have h1 : Nat.testBit 1 i = false := by
        rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
        exact decide_eq_false (by omega)
      split_ifs <;> simp [h1]
  have hq : C / 2 ^ W < C := Nat.div_lt_self hpos (Nat.one_lt_two_pow (by omega))
  have hC' : ∀ j, (C / 2 ^ W).testBit j = true → j % W = 0 := by
    intro j hj
    rw [Nat.testBit_div_two_pow] at hj
    have := hC _ hj
    rwa [Nat.add_mod_right] at this
  have hlow : C % 2 ^ W * m < 2 ^ W := by
    rw [hc0]
    split_ifs <;> simp [hm, Nat.two_pow_pos]
  have e : C * m = 2 ^ W * (C / 2 ^ W * m) + C % 2 ^ W * m := by
    conv_lhs => rw [← Nat.div_add_mod C (2 ^ W)]
    ring
  rw [e, testBit_split hlow]
  split_ifs with h
  · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, mul_zero, hc0]
    split_ifs with h0 <;> simp [h0]
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
    rw [Nat.add_sub_cancel_left, ih _ hq hC' i, Nat.testBit_div_two_pow,
      show W + i = i + W * 1 by ring, Nat.add_mul_div_left _ _ hW, Nat.add_mul_mod_self_left]
    congr 2

@[expose] def Z (r W n A : ℕ) : Prop := ∀ t < r, ∀ j, n ≤ j → j < W → A.testBit (W * t + j) = false

theorem rk_zero {r W A : ℕ} (h : Z r W 0 A) : rk r W A = 0 := by
  rw [rk, Submodule.span_eq_bot.2, finrank_bot]
  rintro _ ⟨t, rfl⟩
  funext j
  simp [rowV, h t t.2 j (Nat.zero_le _) j.2]

theorem rk_fin_zero (r A : ℕ) : rk r 0 A = 0 :=
  Nat.eq_zero_of_le_zero ((Submodule.finrank_le _).trans (by simp))

theorem div_mod_row {W t j : ℕ} (hj : j < W) : (W * t + j) / W = t ∧ (W * t + j) % W = j := by
  have hW : 0 < W := by omega
  refine ⟨?_, ?_⟩
  · rw [add_comm, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hj, zero_add]
  · rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

theorem rk_step {r W k t0 : ℕ} (A A' : ℕ) (hk : k < W) (ht0 : t0 < r)
    (hb0 : A.testBit (W * t0 + k) = true)
    (hrow : ∀ t < r, ∀ j < W, A'.testBit (W * t + j) =
      (A.testBit (W * t + j) ^^ (A.testBit (W * t + k) && A.testBit (W * t0 + j)))) :
    rk r W A = rk r W A' + 1 ∧ ∀ t < r, A'.testBit (W * t + k) = false := by
  set v : Fin r → Fin W → ZMod 2 := fun t => rowV W A t with hv
  set v' : Fin r → Fin W → ZMod 2 := fun t => rowV W A' t with hv'
  have hbit : ∀ t < r, A'.testBit (W * t + k) = false := by
    intro t ht
    rw [hrow t ht k hk, hb0]
    cases A.testBit (W * t + k) <;> rfl
  refine ⟨?_, hbit⟩
  set u := v ⟨t0, ht0⟩
  set b : Fin r → ZMod 2 := fun t => v t ⟨k, hk⟩
  have hvv : ∀ t, v t = v' t + b t • u := by
    intro t
    funext j
    simp only [hv, hv', b, u, rowV, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hrow t t.2 j j.2]
    cases A.testBit (W * t + j) <;> cases A.testBit (W * t + k) <;>
      cases A.testBit (W * t0 + j) <;> decide
  have hv'k : ∀ t, v' t ⟨k, hk⟩ = 0 := by
    intro t
    simp [hv', rowV, hbit t t.2]
  have huk : u ⟨k, hk⟩ = 1 := by simp [u, hv, rowV, hb0]
  have hu0 : u ≠ 0 := fun h => by
    have := congrFun h ⟨k, hk⟩
    rw [huk] at this
    exact one_ne_zero this
  set S' := Submodule.span (ZMod 2) (Set.range v')
  set T := Submodule.span (ZMod 2) {u}
  have hsup : Submodule.span (ZMod 2) (Set.range v) = S' ⊔ T := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      rw [hvv t]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨t, rfl⟩))
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    · refine sup_le ?_ ?_
      · rw [Submodule.span_le]
        rintro _ ⟨t, rfl⟩
        have : v' t = v t + b t • u := by
          rw [hvv t, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
        rw [this]
        exact Submodule.add_mem _ (Submodule.subset_span ⟨t, rfl⟩)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨t0, ht0⟩, rfl⟩))
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.subset_span ⟨⟨t0, ht0⟩, rfl⟩
  have hker : S' ≤ LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin W => ZMod 2)
      ⟨k, hk⟩) := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact hv'k t
  have hinf : S' ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx2
    have := hker hx1
    rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.smul_apply, huk, smul_eq_mul, mul_one] at this
    rw [this, zero_smul]
    exact Submodule.zero_mem _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : Module.finrank (ZMod 2) ↥(S' ⊔ T) + Module.finrank (ZMod 2) ↥(S' ⊓ T) =
      Module.finrank (ZMod 2) S' + Module.finrank (ZMod 2) T :=
    Submodule.finrank_sup_add_finrank_inf_eq _ _
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hu0] at e
  change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) =
    Module.finrank (ZMod 2) S' + 1
  rw [hsup, e]

theorem loop_eq {r W F R : ℕ} (hW : 0 < W) (hF : F = CFSG.KC.Co1RankCoord.mask W) (hR : R = rep W r) :
    ∀ n, n ≤ W → ∀ A acc, Z r W n A →
      Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ r => r)
        (fun k ih A r => strictN (Nat.land (Nat.shiftRight A k) R) fun C =>
          Bool.rec (motive := fun _ => Nat)
            (strictN (Nat.xor C (Nat.land C (Nat.sub C 1))) fun lo =>
              strictN (Nat.land (Nat.div A lo) F) fun m =>
              strictN (Nat.xor A (Nat.mul C m)) fun A' => ih A' (Nat.succ r))
            (ih A r) (Nat.beq C 0)) n A acc = acc + rk r W A
  | 0, _, A, acc, hz => by
    rw [rk_zero hz]
    rfl
  | n + 1, hn, A, acc, hz => by
    have hC : ∀ j, (Nat.land (Nat.shiftRight A n) R).testBit j =
        (A.testBit (n + j) && decide (j < W * r ∧ j % W = 0)) := by
      intro j
      rw [hR]
      change ((A >>> n) &&& rep W r).testBit j = _
      rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_rep hW]
    have hCt : ∀ t < r, (Nat.land (Nat.shiftRight A n) R).testBit (W * t) =
        A.testBit (W * t + n) := by
      intro t ht
      rw [hC, add_comm n]
      have : W * t < W * r := Nat.mul_lt_mul_of_pos_left ht hW
      simp [this]
    first
      | rw [Nat.rec_add_one (motive := fun _ => ℕ → ℕ → ℕ)]
      | simp only [Nat.rec_add_one]
    rw [strictN_eq]
    cases hb : Nat.beq (Nat.land (Nat.shiftRight A n) R) 0
    · dsimp only
      have hC0 : Nat.land (Nat.shiftRight A n) R ≠ 0 := fun h => by
        rw [h] at hb
        exact absurd hb (by decide)
      obtain ⟨a, hlo, ha⟩ := lowBit hC0
      rw [strictN_eq, hlo, strictN_eq, strictN_eq]
      rw [hC] at ha
      obtain ⟨ha1, ha2, ha3⟩ : A.testBit (n + a) = true ∧ a < W * r ∧ a % W = 0 := by
        simpa using ha
      set t0 := a / W
      have hat : a = W * t0 := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ha3)).symm
      have ht0 : t0 < r := (Nat.div_lt_iff_lt_mul hW).2 (by rw [mul_comm]; exact ha2)
      set C := Nat.land (Nat.shiftRight A n) R
      set m := Nat.land (Nat.div A (2 ^ a)) F
      have hmb : ∀ j, m.testBit j = (A.testBit (W * t0 + j) && decide (j < W)) := by
        intro j
        change ((A / 2 ^ a) &&& F).testBit j = _
        rw [Nat.testBit_and, Nat.testBit_div_two_pow, hF, mask_eq, Nat.testBit_two_pow_sub_one,
          hat, add_comm j]
      have hm : m < 2 ^ W := by
        have hF' : F < 2 ^ W := by
          rw [hF, mask_eq]
          exact Nat.sub_lt (Nat.two_pow_pos W) Nat.one_pos
        exact Nat.and_lt_two_pow _ hF'
      have hsp : ∀ j, C.testBit j = true → j % W = 0 := by
        intro j hj
        rw [hC] at hj
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
        exact hj.2.2
      obtain ⟨hst, hclr⟩ := rk_step (r := r) (W := W) (k := n) (t0 := t0) A (Nat.xor A (Nat.mul C m)) (by omega)
        ht0 (by rw [add_comm, ← hat]; exact ha1) (by
          intro t ht j hj
          change (A ^^^ C * m).testBit (W * t + j) = _
          obtain ⟨e1, e2⟩ := div_mod_row (t := t) hj
          rw [Nat.testBit_xor, testBit_mul_sparse hW hm C hsp, e1, e2, hCt t ht, hmb,
            decide_eq_true hj, Bool.and_true])
      have hz' : Z r W n (Nat.xor A (Nat.mul C m)) := by
        intro t ht j hj1 hj2
        rcases Nat.lt_or_eq_of_le hj1 with h | rfl
        · obtain ⟨e1, e2⟩ := div_mod_row (t := t) hj2
          change (A ^^^ C * m).testBit (W * t + j) = false
          rw [Nat.testBit_xor, testBit_mul_sparse hW hm C hsp, e1, e2, hCt t ht,
            hz t ht j h hj2, hmb, hz t0 ht0 j h hj2]
          simp
        · exact hclr t ht
      rw [loop_eq hW hF hR n (by omega) _ (acc + 1) hz', hst]
      omega
    · dsimp only
      have hC0 : Nat.land (Nat.shiftRight A n) R = 0 := Nat.eq_of_beq_eq_true hb
      have hz' : Z r W n A := by
        intro t ht j hj1 hj2
        rcases Nat.lt_or_eq_of_le hj1 with h | rfl
        · exact hz t ht j h hj2
        · rw [← hCt t ht, hC0, Nat.zero_testBit]
      exact loop_eq hW hF hR n (by omega) A acc hz'

theorem rankRC_eq (r W A : ℕ) : rankRC r W A = rk r W A := by
  unfold rankRC
  rw [strictN_eq, strictN_eq]
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · rw [rk_fin_zero]
    rfl
  · rw [loop_eq hW rfl (div_mask hW) W le_rfl A 0 (fun _ _ j h1 h2 => absurd h2 (by omega)),
      zero_add]

theorem span_eq_top_of_rk {r W A : ℕ} (h : rk r W A = W) :
    Submodule.span (ZMod 2) (Set.range fun t : Fin r => rowV W A t) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun]
  exact h

theorem rankRC_eq_rank (r W A : ℕ) :
    rankRC r W A = (Matrix.of fun (t : Fin r) (j : Fin W) => rowV W A t j).rank := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rankRC_eq]
  refine Eq.trans ?_ (Matrix.rank_eq_finrank_span_row _).symm
  rfl

end CFSG.KS.SporSch.Co1RankRC

end
