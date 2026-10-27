module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
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

namespace CFSG.QuasithinUnique.B42A57

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def fixSub (g : MulAut W) : Subgroup W where
  carrier := {w | g w = w}
  one_mem' := map_one g
  mul_mem' := fun {x y} hx hy => by
    have hx' : g x = x := hx
    have hy' : g y = y := hy
    show g (x * y) = x * y
    rw [map_mul, hx', hy']
  inv_mem' := fun {x} hx => by
    have hx' : g x = x := hx
    show g x⁻¹ = x⁻¹
    rw [map_inv, hx']

omit [Finite W] in
theorem mem_fixSub {g : MulAut W} {w : W} : w ∈ fixSub g ↔ g w = w := Iff.rfl

theorem card_modEq_fixed (g : MulAut W) (hg : g ^ 5 = 1) :
    Nat.card W ≡ Nat.card (fixSub g) [MOD 5] := by
  by_cases h1 : g = 1
  · subst h1
    have : fixSub (1 : MulAut W) = ⊤ := by
      ext w
      simp [mem_fixSub]
    rw [this, Subgroup.card_top]
  · have h5 : Nat.Prime 5 := by norm_num
    have : Fact (Nat.Prime 5) := ⟨h5⟩
    have hord : orderOf g = 5 := orderOf_eq_prime hg h1
    have hcard : Nat.card (Subgroup.zpowers g) = 5 ^ 1 := by
      rw [Nat.card_zpowers, hord, pow_one]
    have key := (IsPGroup.of_card hcard).card_modEq_card_fixedPoints W
    have hset : (MulAction.fixedPoints (Subgroup.zpowers g) W) = (fixSub g : Set W) := by
      ext w
      rw [MulAction.mem_fixedPoints]
      constructor
      · intro h
        have := h ⟨g, Subgroup.mem_zpowers g⟩
        exact this
      · intro h m
        obtain ⟨m, hm⟩ := m
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
        have hw : g w = w := h
        show (g ^ k) w = w
        induction k using Int.induction_on with
        | zero => simp
        | succ n ih =>
          rw [zpow_add, zpow_one, MulAut.mul_apply, hw]
          exact ih (Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _)
        | pred n ih =>
          have hw' : g⁻¹ w = w := by
            have := congrArg (fun v => g⁻¹ v) hw
            simpa using this.symm
          rw [zpow_sub, zpow_one, MulAut.mul_apply, hw']
          exact ih (Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _)
    have e : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) W) = Nat.card (fixSub g) := by
      rw [hset]
      rfl
    rw [e] at key
    exact key

omit [Finite W] in
theorem isPGroup_two (hW : ∀ w : W, w * w = 1) : IsPGroup 2 W := fun w =>
  ⟨1, by simpa [pow_two] using hW w⟩

theorem card_fix_pow (hW : ∀ w : W, w * w = 1) (g : MulAut W) :
    ∃ k j : ℕ, Nat.card W = 2 ^ k ∧ Nat.card (fixSub g) = 2 ^ j ∧ j ≤ k := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := W)).1 (isPGroup_two hW)
  have hd : Nat.card (fixSub g) ∣ 2 ^ k := hk ▸ Subgroup.card_subgroup_dvd_card (fixSub g)
  obtain ⟨j, hj, hjk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact ⟨k, j, hk, hjk, hj⟩

theorem eq_one_of_card_le_eight (hW : ∀ w : W, w * w = 1) (hcard : Nat.card W ≤ 8) (g : MulAut W)
    (hg : g ^ 5 = 1) : g = 1 := by
  obtain ⟨k, j, hk, hj, hjk⟩ := card_fix_pow hW g
  have hmod := card_modEq_fixed g hg
  rw [hk, hj] at hmod
  have hk3 : k ≤ 3 := by
    by_contra h
    push Not at h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hjk' : j = k := by
    interval_cases k <;> interval_cases j <;> first | rfl | (exfalso; revert hmod; decide)
  have hfix : fixSub g = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top (fixSub g)).1
    rw [hj, hk, hjk']
  apply MulEquiv.ext
  intro w
  have : w ∈ fixSub g := by rw [hfix]; trivial
  exact this

theorem fixed_eq_bot_of_card_sixteen (hW : ∀ w : W, w * w = 1) (hcard : Nat.card W = 16)
    (g : MulAut W) (hg : g ^ 5 = 1) (hne : g ≠ 1) : fixSub g = ⊥ := by
  obtain ⟨k, j, hk, hj, hjk⟩ := card_fix_pow hW g
  have hmod := card_modEq_fixed g hg
  rw [hk, hj] at hmod
  have hk4 : k = 4 := by
    have : 2 ^ k = 2 ^ 4 := by rw [← hk, hcard]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  subst hk4
  have hj0 : j = 0 := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with h | h | h | h | h
    · exact h
    · subst h; exfalso; revert hmod; decide
    · subst h; exfalso; revert hmod; decide
    · subst h; exfalso; revert hmod; decide
    · subst h
      exfalso
      apply hne
      have hfix : fixSub g = ⊤ := by
        apply (Subgroup.card_eq_iff_eq_top (fixSub g)).1
        rw [hj, hk]
      apply MulEquiv.ext
      intro w
      have : w ∈ fixSub g := by rw [hfix]; trivial
      exact this
  subst hj0
  exact (Subgroup.eq_bot_iff_card (fixSub g)).2 (by rw [hj]; rfl)

theorem card_ge_sixteen_of_order_five (hW : ∀ w : W, w * w = 1) (g : MulAut W) (hg : g ^ 5 = 1)
    (hne : g ≠ 1) : 16 ≤ Nat.card W := by
  by_contra h
  push Not at h
  have h8 : Nat.card W ≤ 8 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := W)).1 (isPGroup_two hW)
    have hk4 : k ≤ 3 := by
      by_contra hk'
      push Not at hk'
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk'
      omega
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk4
      _ = 8 := by norm_num
  exact hne (eq_one_of_card_le_eight hW h8 g hg)

end CFSG.QuasithinUnique.B42A57
