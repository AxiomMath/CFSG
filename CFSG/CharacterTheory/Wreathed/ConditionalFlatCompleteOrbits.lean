module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseOrbits
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

open scoped BigOperators

namespace CFSG.Wreathed.FlatComplete

open CFSG.Wreathed.ConditionalGeneralBase

theorem c_orbit_eq {m : ℕ} {β : Type*} (c : ZMod m → ZMod m → β)
    (hsymm : ∀ i j, c i j = c j i ∧ c i j = c j (-i - j)) {I J : ZMod m × ZMod m}
    (hJ : J ∈ MulAction.orbit (dualGroup m) I) : c J.1 J.2 = c I.1 I.2 := by
  obtain ⟨i, j⟩ := I
  rw [mem_orbit_dualGroup_iff, mem_dualSix_iff] at hJ
  have hrot2 : c (-i - j) i = c i j := by
    have h := (hsymm j (-i - j)).2
    rw [show -j - (-i - j) = i by ring] at h
    rw [← h, ← (hsymm i j).2]
  rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact (hsymm i j).1.symm
  · exact (hsymm i j).2.symm
  · exact hrot2
  · exact ((hsymm i (-i - j)).1.trans hrot2)
  · exact ((hsymm (-i - j) j).1.trans (hsymm i j).2.symm)

variable {m M : ℕ}

theorem M_add_M (hm : m = 2 * M) : (M : ZMod m) + M = 0 := by
  have h : ((2 * M : ℕ) : ZMod m) = 0 := by rw [← hm, ZMod.natCast_self]
  push_cast at h
  rw [← h]
  ring

theorem neg_M (hm : m = 2 * M) : -(M : ZMod m) = M := by
  have h := M_add_M hm
  linear_combination -h

theorem natCast_ne_zero_of_lt {j : ℕ} (h0 : 0 < j) (hj : j < m) : (j : ZMod m) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

theorem natCast_inj_of_lt {j j' : ℕ} (hj : j < m) (hj' : j' < m)
    (h : (j : ZMod m) = (j' : ZMod m)) : j = j' := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at h

theorem neg_two_mul_eq (hm : m = 2 * M) {r : ℕ} (hr : r ≤ M) :
    -(2 * (r : ZMod m)) = ((m - 2 * r : ℕ) : ZMod m) := by
  have h : ((m - 2 * r : ℕ) : ZMod m) + 2 * r = 0 := by
    have : ((m - 2 * r + 2 * r : ℕ) : ZMod m) = 0 := by
      rw [show m - 2 * r + 2 * r = m by omega, ZMod.natCast_self]
    push_cast at this
    exact this
  linear_combination -h

theorem neg_two_mul_ne_zero (hm : m = 2 * M) {r : ℕ} (hr : r ∈ Finset.Ico 1 M) :
    -(2 * (r : ZMod m)) ≠ 0 := by
  rw [Finset.mem_Ico] at hr
  rw [neg_two_mul_eq hm hr.2.le]
  exact natCast_ne_zero_of_lt (by omega) (by omega)

theorem odd_ne_neg_two_mul (hm : m = 2 * M) {h r : ℕ} (hh : h < m) (hodd : Odd h)
    (hr : r ∈ Finset.Ico 1 M) : (h : ZMod m) ≠ -(2 * (r : ZMod m)) := by
  rw [Finset.mem_Ico] at hr
  rw [neg_two_mul_eq hm hr.2.le]
  intro he
  have := natCast_inj_of_lt hh (by omega) he
  obtain ⟨t, rfl⟩ := hodd
  omega

theorem neg_two_mul_inj (hm : m = 2 * M) {r r' : ℕ} (hr : r ∈ Finset.Ico 1 M)
    (hr' : r' ∈ Finset.Ico 1 M) (h : -(2 * (r : ZMod m)) = -(2 * (r' : ZMod m))) : r = r' := by
  rw [Finset.mem_Ico] at hr hr'
  rw [neg_two_mul_eq hm hr.2.le, neg_two_mul_eq hm hr'.2.le] at h
  have := natCast_inj_of_lt (by omega) (by omega) h
  omega

theorem orbit_reduction (hm : m = 2 * M) {β : Type*} (c : ZMod m → ZMod m → β)
    (hsymm : ∀ i j, c i j = c j i ∧ c i j = c j (-i - j)) (V : Finset (ZMod m × ZMod m))
    (hVrep : ∀ I, (MulAction.orbit (dualGroup m) I).ncard = 6 →
      ∃! J, J ∈ V ∧ J ∈ MulAction.orbit (dualGroup m) I) (a b : ZMod m) :
    (a = 0 ∧ b = 0) ∨
      (∃ ρ : ZMod m, ρ ≠ 0 ∧ c a b = c ρ ρ ∧
        ((a = 0 ∨ a = M) ∧ (b = 0 ∨ b = M) ↔ ρ = M)) ∨
      (∃ J ∈ V, c a b = c J.1 J.2 ∧ ¬ ((a = 0 ∨ a = M) ∧ (b = 0 ∨ b = M))) := by
  have hMM := M_add_M hm
  have hnM := neg_M hm
  rcases orbit_trichotomy (a, b) with h | ⟨ρ, hρ, h⟩ | h
  · left
    have hmem : (a, b) ∈ MulAction.orbit (dualGroup m) (a, b) := MulAction.mem_orbit_self _
    rw [h, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    exact hmem
  · right
    left
    have hmem : (a, b) ∈ MulAction.orbit (dualGroup m) (ρ, ρ) := by
      rw [← h]
      exact MulAction.mem_orbit_self _
    refine ⟨ρ, hρ, c_orbit_eq c hsymm hmem, ?_⟩
    have hmem' := hmem
    rw [mem_orbit_dualGroup_iff, mem_dualSix_iff] at hmem'
    simp only [Prod.mk.injEq] at hmem'
    constructor
    · rintro ⟨ha, hb⟩
      rcases hmem' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact ha.resolve_left hρ
      · exact ha.resolve_left hρ
      · exact ha.resolve_left hρ
      · exact hb.resolve_left hρ
      · exact ha.resolve_left hρ
      · exact hb.resolve_left hρ
    · rintro rfl
      have h2 : -(M : ZMod m) - M = 0 := by linear_combination -hMM
      rcases hmem' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | exact ⟨Or.inr rfl, Or.inr rfl⟩
        | exact ⟨Or.inr rfl, Or.inl h2⟩
        | exact ⟨Or.inl h2, Or.inr rfl⟩
  · right
    right
    obtain ⟨J, ⟨hJV, hJ⟩, -⟩ := hVrep (a, b) h
    have hJ' : (a, b) ∈ MulAction.orbit (dualGroup m) J := by
      rw [MulAction.orbit_eq_iff.mpr hJ]
      exact MulAction.mem_orbit_self _
    refine ⟨J, hJV, c_orbit_eq c hsymm hJ', ?_⟩
    rintro ⟨ha, hb⟩
    rw [ncard_orbit_eq_six_iff, nodup_dualSix_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only at h1 h2 h3
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact h1 rfl
    · apply h2
      rw [neg_zero, zero_sub, hnM]
    · apply h3
      rw [sub_zero, hnM]
    · exact h1 rfl

theorem diag_index [NeZero m] (hm : m = 2 * M) {ρ : ZMod m} (hρ : ρ ≠ 0) (hρM : ρ ≠ M) :
    ∃ r ∈ Finset.Ico 1 M, ρ = r ∨ ρ = r + M := by
  have hlt := ZMod.val_lt ρ
  have hv0 : ρ.val ≠ 0 := fun h => hρ ((ZMod.val_eq_zero ρ).mp h)
  have hvM : ρ.val ≠ M := fun h => hρM (by rw [← ZMod.natCast_zmod_val ρ, h])
  rcases lt_or_gt_of_ne hvM with h | h
  · exact ⟨ρ.val, Finset.mem_Ico.mpr ⟨by omega, h⟩, Or.inl (ZMod.natCast_zmod_val ρ).symm⟩
  · refine ⟨ρ.val - M, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, Or.inr ?_⟩
    have : ((ρ.val - M + M : ℕ) : ZMod m) = ρ := by
      rw [show ρ.val - M + M = ρ.val by omega, ZMod.natCast_zmod_val]
    push_cast at this
    exact this.symm

theorem index_cases [NeZero m] (hm : m = 2 * M) {j : ZMod m} (hj : j ≠ 0) :
    (∃ h ∈ (Finset.Ico 1 m).filter Odd, j = h) ∨ ∃ r ∈ Finset.Ico 1 M, j = -(2 * (r : ZMod m)) := by
  have hlt := ZMod.val_lt j
  have hv0 : j.val ≠ 0 := fun h => hj ((ZMod.val_eq_zero j).mp h)
  rcases Nat.even_or_odd j.val with he | ho
  · right
    obtain ⟨t, ht⟩ := he
    refine ⟨M - t, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [neg_two_mul_eq hm (by omega), show m - 2 * (M - t) = j.val by omega,
      ZMod.natCast_zmod_val]
  · left
    exact ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hlt⟩, ho⟩,
      (ZMod.natCast_zmod_val j).symm⟩

theorem card_reps {n : ℕ} (V : Finset (ZMod (2 ^ n) × ZMod (2 ^ n)))
    (hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6)
    (hVrep : ∀ I, (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6 →
      ∃! J, J ∈ V ∧ J ∈ MulAction.orbit (dualGroup (2 ^ n)) I) :
    V.card = (2 ^ n - 1) * (2 ^ n - 2) / 6 := by
  rw [← ncard_orbits_six (n := n), ← Set.ncard_coe_finset]
  have himage : (fun I : ZMod (2 ^ n) × ZMod (2 ^ n) => MulAction.orbit (dualGroup (2 ^ n)) I) ''
      (V : Set (ZMod (2 ^ n) × ZMod (2 ^ n))) =
      (fun I : ZMod (2 ^ n) × ZMod (2 ^ n) => MulAction.orbit (dualGroup (2 ^ n)) I) ''
        {I | (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6} := by
    ext O
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨I, hV6 I hI, rfl⟩
    · rintro ⟨I, hI, rfl⟩
      obtain ⟨J, ⟨hJV, hJ⟩, -⟩ := hVrep I hI
      exact ⟨J, hJV, MulAction.orbit_eq_iff.mpr hJ⟩
  rw [← himage]
  symm
  apply Set.InjOn.ncard_image
  intro I hI J hJ hIJ
  have hJI : J ∈ MulAction.orbit (dualGroup (2 ^ n)) I := by
    have h : MulAction.orbit (dualGroup (2 ^ n)) I = MulAction.orbit (dualGroup (2 ^ n)) J := hIJ
    rw [h]
    exact MulAction.mem_orbit_self _
  obtain ⟨K₀, -, hK₀⟩ := hVrep I (hV6 I hI)
  exact (hK₀ I ⟨hI, MulAction.mem_orbit_self _⟩).trans (hK₀ J ⟨hJ, hJI⟩).symm

theorem count_eq {n : ℕ} (hn : 1 ≤ n) :
    5 + 2 ^ n / 2 + 4 * (2 ^ n / 2 - 1) + (2 ^ n - 1) * (2 ^ n - 2) / 6 =
      ((2 ^ n) ^ 2 + 12 * 2 ^ n + 8) / 6 := by
  set m := 2 ^ n with hmdef
  have hm2 : 2 ≤ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have heven : m % 2 = 0 := by
    rw [hmdef, ← Nat.dvd_iff_mod_eq_zero]
    exact dvd_pow_self 2 (by omega)
  have h3 : m % 3 ≠ 0 := by
    intro h
    have h3 : 3 ∣ 2 ^ n := by rw [← hmdef]; exact Nat.dvd_of_mod_eq_zero h
    have := (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  obtain ⟨t, ht⟩ : 6 ∣ (m - 1) * (m - 2) := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.mul_mod]
    have h6 : m % 6 = 2 ∨ m % 6 = 4 := by omega
    rcases h6 with h6 | h6
    · have e1 : (m - 1) % 6 = 1 := by omega
      have e2 : (m - 2) % 6 = 0 := by omega
      rw [e1, e2]
    · have e1 : (m - 1) % 6 = 3 := by omega
      have e2 : (m - 2) % 6 = 2 := by omega
      rw [e1, e2]
  rw [ht, Nat.mul_div_cancel_left _ (by norm_num)]
  symm
  apply Nat.div_eq_of_eq_mul_left (by norm_num)
  obtain ⟨u, hu⟩ : ∃ u, m = u + 2 := ⟨m - 2, by omega⟩
  have hu2 : u % 2 = 0 := by omega
  obtain ⟨M, hM⟩ : ∃ M, u = 2 * M := ⟨u / 2, by omega⟩
  subst hM
  rw [hu] at ht ⊢
  rw [show 2 * M + 2 - 1 = 2 * M + 1 by omega, show 2 * M + 2 - 2 = 2 * M by omega] at ht
  rw [show (2 * M + 2) / 2 = M + 1 by omega, show M + 1 - 1 = M by omega]
  nlinarith [ht]

end CFSG.Wreathed.FlatComplete
