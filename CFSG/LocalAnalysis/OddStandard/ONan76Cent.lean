module

public import CFSG.LocalAnalysis.OddStandard.ONan76P
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.OddStandard.ONan76

section Coord

variable {n : ℕ}

theorem actS_add (p q : Vec n) : actS (p + q) = actS p + actS q := by
  ext <;> simp only [actS, Prod.fst_add, Prod.snd_add] <;> ring

theorem actT_add (p q : Vec n) : actT (p + q) = actT p + actT q := by
  ext <;> simp only [actT, Prod.fst_add, Prod.snd_add] <;> ring

theorem act_add (i e : ℕ) (p q : Vec n) : act i e (p + q) = act i e p + act i e q := by
  simp only [act]
  induction e with
  | zero =>
    simp only [Function.iterate_zero, id]
    induction i generalizing p q with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, actS_add]
  | succ e ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, actT_add]

theorem act_zero (i e : ℕ) : act i e (0 : Vec n) = 0 := by
  have h := act_add i e (0 : Vec n) 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

theorem nsmul_two_pow_pred (p : Vec n) :
    (2 ^ (n - 1) : ℕ) • p = ((2 : ZMod (2 ^ n)) ^ (n - 1) * p.1,
      (2 : ZMod (2 ^ n)) ^ (n - 1) * p.2.1, (2 : ZMod (2 ^ n)) ^ (n - 1) * p.2.2) := by
  ext <;> simp [nsmul_eq_mul]

theorem fix_pair_four {i e i' e' : ℕ} (hi : i < 4) (he : e < 2) (hi' : i' < 4) (he' : e' < 2)
    (hτ : e = 1 ∨ i = 2) (hτ' : e' = 1 ∨ i' = 2) (hne : ¬ (i = i' ∧ e = e')) {p : Vec n}
    (h : act i e p = p) (h' : act i' e' p = p) : 4 • p = 0 := by
  obtain ⟨a, b, c⟩ := p
  simp only [Prod.smul_mk, Prod.mk_eq_zero, nsmul_eq_mul, Nat.cast_ofNat]
  interval_cases i <;> interval_cases e <;> interval_cases i' <;> interval_cases e' <;>
    first
    | omega
    | (simp only [act_00, act_10, act_20, act_30, act_01, act_11, act_21, act_31, actS, actT,
        Prod.mk.injEq] at h h'
       refine ⟨?_, ?_, ?_⟩ <;> grind)

theorem fix_pair {i e i' e' : ℕ} (hi : i < 4) (he : e < 2) (hi' : i' < 4) (he' : e' < 2)
    (hτ : e = 1 ∨ i = 2) (hτ' : e' = 1 ∨ i' = 2) (hne : ¬ (i = i' ∧ e = e')) :
    (∀ p : Vec n, act i e p = p → act i' e' p = p → p + p = 0) ∨
    (∀ p : Vec n, act i e p = p → act i' e' p = p → 4 * p.1 = 0 ∧ p = (p.1, 2 * p.1, -p.1)) := by
  interval_cases i <;> interval_cases e <;> interval_cases i' <;> interval_cases e' <;>
    first
    | omega
    | (left
       rintro ⟨a, b, c⟩ h h'
       simp only [act_00, act_10, act_20, act_30, act_01, act_11, act_21, act_31, actS, actT,
         Prod.mk.injEq, Prod.mk_add_mk, Prod.mk_eq_zero] at h h' ⊢
       and_intros <;> first | trivial | grind)
    | (right
       rintro ⟨a, b, c⟩ h h'
       simp only [act_00, act_10, act_20, act_30, act_01, act_11, act_21, act_31, actS, actT,
         Prod.mk.injEq] at h h' ⊢
       and_intros <;> first | trivial | grind)

theorem fix_order_four {i : ℕ} (hi : i = 1 ∨ i = 3) {p : Vec n} (h : act i 0 p = p) :
    p.2.1 = 0 ∧ p.2.2 = p.1 := by
  obtain ⟨a, b, c⟩ := p
  rcases hi with rfl | rfl <;>
    simp only [act_10, act_30, actS, Prod.mk.injEq] at h ⊢ <;>
    refine ⟨?_, ?_⟩ <;> grind

theorem two_mul_eq_zero_vec (hn : 1 ≤ n) (q : Vec n) (hq : q + q = 0) :
    (q.1 = 0 ∨ q.1 = 2 ^ (n - 1)) ∧ (q.2.1 = 0 ∨ q.2.1 = 2 ^ (n - 1)) ∧
      (q.2.2 = 0 ∨ q.2.2 = 2 ^ (n - 1)) := by
  have h2 : ∀ x : ZMod (2 ^ n), x + x = 0 → x = 0 ∨ x = 2 ^ (n - 1) := fun x hx =>
    (two_mul_eq_zero_iff hn x).1 (by rw [two_mul]; exact hx)
  have h1 := congrArg Prod.fst hq
  have h' := congrArg (fun r : Vec n => r.2.1) hq
  have h'' := congrArg (fun r : Vec n => r.2.2) hq
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at h1 h' h''
  exact ⟨h2 _ h1, h2 _ h', h2 _ h''⟩

theorem inv_data_t (hn : 2 ≤ n) :
    ∃ u₁ u₂ r₁ r₂ : Vec n,
      act 0 1 u₁ = u₁ ∧ act 0 1 u₂ = u₂ ∧ u₂ + u₂ = 0 ∧ u₂ ≠ 0 ∧
      (2 ^ (n - 1) : ℕ) • u₁ ≠ 0 ∧ (2 ^ (n - 1) : ℕ) • u₁ ≠ u₂ ∧
      act 0 1 r₁ - r₁ = (2 ^ (n - 1) : ℕ) • u₁ ∧ act 0 1 r₂ - r₂ = u₂ ∧
      ∀ q, act 0 1 q = q → q + q = 0 →
        q = 0 ∨ q = (2 ^ (n - 1) : ℕ) • u₁ ∨ q = u₂ ∨ q = (2 ^ (n - 1) : ℕ) • u₁ + u₂ := by
  have hn1 : 1 ≤ n := by omega
  set ε : ZMod (2 ^ n) := 2 ^ (n - 1) with hεdef
  set δ : ZMod (2 ^ n) := 2 ^ (n - 2) with hδdef
  have hε0 : ε ≠ 0 := two_pow_pred_ne_zero hn1
  have hεε : ε + ε = 0 := two_pow_pred_add_self hn1
  have hδδ : δ + δ = ε := by
    rw [hδdef, hεdef, ← two_mul, ← pow_succ']
    congr 1
    omega
  have key := two_mul_eq_zero_vec (n := n) hn1
  refine ⟨(1, 0, -1), (0, ε, 0), (ε, 0, 0), (0, δ, 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rintro ⟨a, b, c⟩ hq hq2
       obtain ⟨ha, hb, hc⟩ := key _ hq2
       simp only [act_20, act_01, act_11, act_21, act_31, actS, actT, Prod.mk.injEq] at hq
       rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
         simp only [nsmul_two_pow_pred, Prod.mk_add_mk, Prod.mk.injEq, Prod.mk_eq_zero,
           mul_one, mul_zero, mul_neg] <;> grind)
    | (simp only [act_20, act_01, act_11, act_21, act_31, actS, actT, nsmul_two_pow_pred,
         Prod.mk.injEq, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk_eq_zero, ne_eq, mul_one,
         mul_zero, mul_neg]
       and_intros <;> first | trivial | grind)

theorem inv_data_st (hn : 2 ≤ n) :
    ∃ u₁ u₂ r₁ r₂ : Vec n,
      act 1 1 u₁ = u₁ ∧ act 1 1 u₂ = u₂ ∧ u₂ + u₂ = 0 ∧ u₂ ≠ 0 ∧
      (2 ^ (n - 1) : ℕ) • u₁ ≠ 0 ∧ (2 ^ (n - 1) : ℕ) • u₁ ≠ u₂ ∧
      act 1 1 r₁ - r₁ = (2 ^ (n - 1) : ℕ) • u₁ ∧ act 1 1 r₂ - r₂ = u₂ ∧
      ∀ q, act 1 1 q = q → q + q = 0 →
        q = 0 ∨ q = (2 ^ (n - 1) : ℕ) • u₁ ∨ q = u₂ ∨ q = (2 ^ (n - 1) : ℕ) • u₁ + u₂ := by
  have hn1 : 1 ≤ n := by omega
  set ε : ZMod (2 ^ n) := 2 ^ (n - 1) with hεdef
  set δ : ZMod (2 ^ n) := 2 ^ (n - 2) with hδdef
  have hε0 : ε ≠ 0 := two_pow_pred_ne_zero hn1
  have hεε : ε + ε = 0 := two_pow_pred_add_self hn1
  have hδδ : δ + δ = ε := by
    rw [hδdef, hεdef, ← two_mul, ← pow_succ']
    congr 1
    omega
  have key := two_mul_eq_zero_vec (n := n) hn1
  refine ⟨(1, -1, 0), (0, ε, ε), (ε, 0, 0), (0, -δ, δ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rintro ⟨a, b, c⟩ hq hq2
       obtain ⟨ha, hb, hc⟩ := key _ hq2
       simp only [act_20, act_01, act_11, act_21, act_31, actS, actT, Prod.mk.injEq] at hq
       rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
         simp only [nsmul_two_pow_pred, Prod.mk_add_mk, Prod.mk.injEq, Prod.mk_eq_zero,
           mul_one, mul_zero, mul_neg] <;> grind)
    | (simp only [act_20, act_01, act_11, act_21, act_31, actS, actT, nsmul_two_pow_pred,
         Prod.mk.injEq, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk_eq_zero, ne_eq, mul_one,
         mul_zero, mul_neg]
       and_intros <;> first | trivial | grind)

theorem inv_data_s2 (hn : 2 ≤ n) :
    ∃ u₁ u₂ r₁ r₂ : Vec n,
      act 2 0 u₁ = u₁ ∧ act 2 0 u₂ = u₂ ∧ u₂ + u₂ = 0 ∧ u₂ ≠ 0 ∧
      (2 ^ (n - 1) : ℕ) • u₁ ≠ 0 ∧ (2 ^ (n - 1) : ℕ) • u₁ ≠ u₂ ∧
      act 2 0 r₁ - r₁ = (2 ^ (n - 1) : ℕ) • u₁ ∧ act 2 0 r₂ - r₂ = u₂ ∧
      ∀ q, act 2 0 q = q → q + q = 0 →
        q = 0 ∨ q = (2 ^ (n - 1) : ℕ) • u₁ ∨ q = u₂ ∨ q = (2 ^ (n - 1) : ℕ) • u₁ + u₂ := by
  have hn1 : 1 ≤ n := by omega
  set ε : ZMod (2 ^ n) := 2 ^ (n - 1) with hεdef
  set δ : ZMod (2 ^ n) := 2 ^ (n - 2) with hδdef
  have hε0 : ε ≠ 0 := two_pow_pred_ne_zero hn1
  have hεε : ε + ε = 0 := two_pow_pred_add_self hn1
  have hδδ : δ + δ = ε := by
    rw [hδdef, hεdef, ← two_mul, ← pow_succ']
    congr 1
    omega
  have key := two_mul_eq_zero_vec (n := n) hn1
  refine ⟨(1, 0, 1), (0, ε, ε), (ε, 0, 0), (δ, δ, 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rintro ⟨a, b, c⟩ hq hq2
       obtain ⟨ha, hb, hc⟩ := key _ hq2
       simp only [act_20, act_01, act_11, act_21, act_31, actS, actT, Prod.mk.injEq] at hq
       rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
         simp only [nsmul_two_pow_pred, Prod.mk_add_mk, Prod.mk.injEq, Prod.mk_eq_zero,
           mul_one, mul_zero, mul_neg] <;> grind)
    | (simp only [act_20, act_01, act_11, act_21, act_31, actS, actT, nsmul_two_pow_pred,
         Prod.mk.injEq, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk_eq_zero, ne_eq, mul_one,
         mul_zero, mul_neg]
       and_intros <;> first | trivial | grind)

theorem inv_data_s2t (hn : 2 ≤ n) :
    ∃ u₁ u₂ r₁ r₂ : Vec n,
      act 2 1 u₁ = u₁ ∧ act 2 1 u₂ = u₂ ∧ u₂ + u₂ = 0 ∧ u₂ ≠ 0 ∧
      (2 ^ (n - 1) : ℕ) • u₁ ≠ 0 ∧ (2 ^ (n - 1) : ℕ) • u₁ ≠ u₂ ∧
      act 2 1 r₁ - r₁ = (2 ^ (n - 1) : ℕ) • u₁ ∧ act 2 1 r₂ - r₂ = u₂ ∧
      ∀ q, act 2 1 q = q → q + q = 0 →
        q = 0 ∨ q = (2 ^ (n - 1) : ℕ) • u₁ ∨ q = u₂ ∨ q = (2 ^ (n - 1) : ℕ) • u₁ + u₂ := by
  have hn1 : 1 ≤ n := by omega
  set ε : ZMod (2 ^ n) := 2 ^ (n - 1) with hεdef
  set δ : ZMod (2 ^ n) := 2 ^ (n - 2) with hδdef
  have hε0 : ε ≠ 0 := two_pow_pred_ne_zero hn1
  have hεε : ε + ε = 0 := two_pow_pred_add_self hn1
  have hδδ : δ + δ = ε := by
    rw [hδdef, hεdef, ← two_mul, ← pow_succ']
    congr 1
    omega
  have key := two_mul_eq_zero_vec (n := n) hn1
  refine ⟨(1, -2, 1), (0, 0, ε), (0, ε, 0), (0, 0, δ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rintro ⟨a, b, c⟩ hq hq2
       obtain ⟨ha, hb, hc⟩ := key _ hq2
       simp only [act_20, act_01, act_11, act_21, act_31, actS, actT, Prod.mk.injEq] at hq
       rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
         simp only [nsmul_two_pow_pred, Prod.mk_add_mk, Prod.mk.injEq, Prod.mk_eq_zero,
           mul_one, mul_zero, mul_neg] <;> grind)
    | (simp only [act_20, act_01, act_11, act_21, act_31, actS, actT, nsmul_two_pow_pred,
         Prod.mk.injEq, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk_eq_zero, ne_eq, mul_one,
         mul_zero, mul_neg]
       and_intros <;> first | trivial | grind)

theorem inv_data_s3t (hn : 2 ≤ n) :
    ∃ u₁ u₂ r₁ r₂ : Vec n,
      act 3 1 u₁ = u₁ ∧ act 3 1 u₂ = u₂ ∧ u₂ + u₂ = 0 ∧ u₂ ≠ 0 ∧
      (2 ^ (n - 1) : ℕ) • u₁ ≠ 0 ∧ (2 ^ (n - 1) : ℕ) • u₁ ≠ u₂ ∧
      act 3 1 r₁ - r₁ = (2 ^ (n - 1) : ℕ) • u₁ ∧ act 3 1 r₂ - r₂ = u₂ ∧
      ∀ q, act 3 1 q = q → q + q = 0 →
        q = 0 ∨ q = (2 ^ (n - 1) : ℕ) • u₁ ∨ q = u₂ ∨ q = (2 ^ (n - 1) : ℕ) • u₁ + u₂ := by
  have hn1 : 1 ≤ n := by omega
  set ε : ZMod (2 ^ n) := 2 ^ (n - 1) with hεdef
  set δ : ZMod (2 ^ n) := 2 ^ (n - 2) with hδdef
  have hε0 : ε ≠ 0 := two_pow_pred_ne_zero hn1
  have hεε : ε + ε = 0 := two_pow_pred_add_self hn1
  have hδδ : δ + δ = ε := by
    rw [hδdef, hεdef, ← two_mul, ← pow_succ']
    congr 1
    omega
  have key := two_mul_eq_zero_vec (n := n) hn1
  refine ⟨(0, -1, 1), (ε, ε, 0), (0, ε, 0), (δ, -δ, 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rintro ⟨a, b, c⟩ hq hq2
       obtain ⟨ha, hb, hc⟩ := key _ hq2
       simp only [act_20, act_01, act_11, act_21, act_31, actS, actT, Prod.mk.injEq] at hq
       rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
         simp only [nsmul_two_pow_pred, Prod.mk_add_mk, Prod.mk.injEq, Prod.mk_eq_zero,
           mul_one, mul_zero, mul_neg] <;> grind)
    | (simp only [act_20, act_01, act_11, act_21, act_31, actS, actT, nsmul_two_pow_pred,
         Prod.mk.injEq, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk_eq_zero, ne_eq, mul_one,
         mul_zero, mul_neg]
       and_intros <;> first | trivial | grind)

theorem inv_type_data (hn : 2 ≤ n) {i e : ℕ} (hi : i < 4) (he : e < 2) (hτ : e = 1 ∨ i = 2) :
    ∃ u₁ u₂ r₁ r₂ : Vec n,
      act i e u₁ = u₁ ∧ act i e u₂ = u₂ ∧ u₂ + u₂ = 0 ∧ u₂ ≠ 0 ∧
      (2 ^ (n - 1) : ℕ) • u₁ ≠ 0 ∧ (2 ^ (n - 1) : ℕ) • u₁ ≠ u₂ ∧
      act i e r₁ - r₁ = (2 ^ (n - 1) : ℕ) • u₁ ∧ act i e r₂ - r₂ = u₂ ∧
      ∀ q, act i e q = q → q + q = 0 →
        q = 0 ∨ q = (2 ^ (n - 1) : ℕ) • u₁ ∨ q = u₂ ∨ q = (2 ^ (n - 1) : ℕ) • u₁ + u₂ := by
  interval_cases i <;> interval_cases e <;> try omega
  · exact inv_data_t hn
  · exact inv_data_st hn
  · exact inv_data_s2 hn
  · exact inv_data_s2t hn
  · exact inv_data_s3t hn

theorem fix_inj {i e : ℕ} (hi : i < 4) (he : e < 2) (hne : ¬ (i = 0 ∧ e = 0)) :
    ∃ ψ φ : Vec n → ZMod (2 ^ n), (∀ p, act i e p = p → φ p + φ p = 0) ∧
      ∀ p q, act i e p = p → act i e q = q → ψ p = ψ q → φ p = φ q → p = q := by
  interval_cases i <;> interval_cases e <;> try omega
  · refine ⟨fun p => p.1, fun p => p.2.1, ?_, ?_⟩
    · rintro ⟨a, b, c⟩ h
      simp only [act_01, actT, Prod.mk.injEq] at h ⊢
      grind
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h h' h1 h2
      simp only [act_01, actT, Prod.mk.injEq] at h h' h1 h2 ⊢
      and_intros <;> grind
  · refine ⟨fun p => p.1, fun p => p.2.1, ?_, ?_⟩
    · rintro ⟨a, b, c⟩ h
      simp only [act_10, actS, Prod.mk.injEq] at h ⊢
      grind
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h h' h1 h2
      simp only [act_10, actS, Prod.mk.injEq] at h h' h1 h2 ⊢
      and_intros <;> grind
  · refine ⟨fun p => p.1, fun p => p.2.2, ?_, ?_⟩
    · rintro ⟨a, b, c⟩ h
      simp only [act_11, actS, actT, Prod.mk.injEq] at h ⊢
      grind
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h h' h1 h2
      simp only [act_11, actS, actT, Prod.mk.injEq] at h h' h1 h2 ⊢
      and_intros <;> grind
  · refine ⟨fun p => p.1, fun p => p.2.1, ?_, ?_⟩
    · rintro ⟨a, b, c⟩ h
      simp only [act_20, actS, Prod.mk.injEq] at h ⊢
      grind
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h h' h1 h2
      simp only [act_20, actS, Prod.mk.injEq] at h h' h1 h2 ⊢
      and_intros <;> grind
  · refine ⟨fun p => p.1, fun p => p.2.2 - p.1, ?_, ?_⟩
    · rintro ⟨a, b, c⟩ h
      simp only [act_21, actS, actT, Prod.mk.injEq] at h ⊢
      grind
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h h' h1 h2
      simp only [act_21, actS, actT, Prod.mk.injEq] at h h' h1 h2 ⊢
      and_intros <;> grind
  · refine ⟨fun p => p.1, fun p => p.2.1, ?_, ?_⟩
    · rintro ⟨a, b, c⟩ h
      simp only [act_30, actS, Prod.mk.injEq] at h ⊢
      grind
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h h' h1 h2
      simp only [act_30, actS, Prod.mk.injEq] at h h' h1 h2 ⊢
      and_intros <;> grind
  · refine ⟨fun p => p.2.2, fun p => p.1, ?_, ?_⟩
    · rintro ⟨a, b, c⟩ h
      simp only [act_31, actS, actT, Prod.mk.injEq] at h ⊢
      grind
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h h' h1 h2
      simp only [act_31, actS, actT, Prod.mk.injEq] at h h' h1 h2 ⊢
      and_intros <;> grind

theorem card_two_torsion (hn : 1 ≤ n) : Nat.card {x : ZMod (2 ^ n) // x + x = 0} = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨0, add_zero 0⟩, ⟨2 ^ (n - 1), two_pow_pred_add_self hn⟩, fun h => ?_, ?_⟩
  · exact two_pow_pred_ne_zero hn (congrArg Subtype.val h).symm
  · ext ⟨x, hx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true, Subtype.ext_iff]
    exact (two_mul_eq_zero_iff hn x).1 (by rw [two_mul]; exact hx)

end Coord

end CFSG.OddStandard.ONan76
