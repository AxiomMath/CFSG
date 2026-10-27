module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup

section Util

variable {Y : Type} [Group Y]

theorem eq_one_of_mul_self_of_odd {x : Y} (h : x * x = 1) (ho : Odd (orderOf x)) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have h2 : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.2 ho
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem odd_orderOf_mul_of_commute {x y : Y} (h : Commute x y) (hx : Odd (orderOf x))
    (hy : Odd (orderOf y)) : Odd (orderOf (x * y)) :=
  (hx.mul hy).of_dvd_nat ((h.orderOf_mul_dvd_lcm).trans (Nat.lcm_dvd_mul _ _))

theorem exists_abelian_normalized [Finite Y] {Bb : Subgroup Y} (hodd : Odd (Nat.card ↥Bb))
    (hne : Bb ≠ ⊥) (M : Subgroup Y) (hn : ∀ m ∈ M, ∀ b ∈ Bb, m * b * m⁻¹ ∈ Bb) :
    ∃ W : Subgroup Y, W ≤ Bb ∧ W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧
      ∀ m ∈ M, ∀ w ∈ W, m * w * m⁻¹ ∈ W := by
  have hsolv : Group.IsSolvable ↥Bb := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hex : ∃ n : ℕ, derivedSeries ↥Bb n = ⊥ := hsolv.solvable
  classical
  set n₀ := Nat.find hex with hn₀
  have hn₀spec : derivedSeries ↥Bb n₀ = ⊥ := Nat.find_spec hex
  have hnt : Nontrivial ↥Bb := (Subgroup.nontrivial_iff_ne_bot Bb).2 hne
  have hn₀pos : n₀ ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hn₀spec
    simp at hn₀spec
  obtain ⟨j, hj⟩ : ∃ j, n₀ = j + 1 := Nat.exists_eq_succ_of_ne_zero hn₀pos
  have hjne : derivedSeries ↥Bb j ≠ ⊥ := Nat.find_min hex (by omega)
  have hcomm : ⁅derivedSeries ↥Bb j, derivedSeries ↥Bb j⁆ = ⊥ := by
    rw [← derivedSeries_succ, ← hj]; exact hn₀spec
  have hle : derivedSeries ↥Bb j ≤ centralizer (derivedSeries ↥Bb j : Set ↥Bb) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  refine ⟨(derivedSeries ↥Bb j).map Bb.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro h
    apply hjne
    rw [Subgroup.map_eq_bot_iff_of_injective _ Bb.subtype_injective] at h
    exact h
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 (hle hy) x hx
    exact congrArg Subtype.val this
  · intro m hm w hw
    obtain ⟨w', hw', rfl⟩ := hw
    let f : ↥Bb →* ↥Bb :=
      { toFun := fun x => ⟨m * x * m⁻¹, hn m hm x x.2⟩
        map_one' := by ext; simp
        map_mul' := by intro x y; ext; simp [mul_assoc] }
    have h1 : f w' ∈ derivedSeries ↥Bb j :=
      map_derivedSeries_le_derivedSeries f j ⟨w', hw', rfl⟩
    exact ⟨f w', h1, rfl⟩

end Util

section Util2

variable {Y : Type} [Group Y]

theorem fixes_of_odd_of_card_eight {P : Subgroup Y} (hP : Nat.card ↥P = 8) {a : Y} (haP : a ∈ P)
    (ha4 : orderOf a = 4) {w : Y} (hwo : Odd (orderOf w)) (hwP : ∀ x ∈ P, w * x * w⁻¹ ∈ P)
    (hwa : w * a * w⁻¹ = a) : ∀ x ∈ P, w * x * w⁻¹ = x := by
  classical
  set H : Subgroup Y := zpowers a with hH
  have hHP : H ≤ P := (Subgroup.zpowers_le).2 haP
  have hHcard : Nat.card ↥H = 4 := by rw [hH, Nat.card_zpowers, ha4]
  have hfixH : ∀ h ∈ H, w * h * w⁻¹ = h := by
    intro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [← conj_zpow, hwa]
  have hfixH' : ∀ h ∈ H, w⁻¹ * h * w = h := by
    intro h hh
    have := hfixH h hh
    calc w⁻¹ * h * w = w⁻¹ * (w * h * w⁻¹) * w := by rw [this]
      _ = h := by group
  set Hs : Subgroup ↥P := H.subgroupOf P with hHs
  have hHscard : Nat.card ↥Hs = 4 := by
    rw [hHs, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHP).toEquiv]; exact hHcard
  have hidx : Hs.index = 2 := by
    have h1 := Subgroup.card_mul_index Hs
    rw [hHscard, hP] at h1
    omega
  intro x hx
  by_cases hxH : x ∈ H
  · exact hfixH x hxH
  · have hy : w * x * w⁻¹ ∈ P := hwP x hx
    have hxs : (⟨x, hx⟩ : ↥P) ∉ Hs := fun h => hxH (Subgroup.mem_subgroupOf.1 h)
    have hys : (⟨w * x * w⁻¹, hy⟩ : ↥P) ∉ Hs := by
      intro h
      apply hxH
      have h' : w * x * w⁻¹ ∈ H := Subgroup.mem_subgroupOf.1 h
      have h2 := hfixH' _ h'
      have e : w⁻¹ * (w * x * w⁻¹) * w = x := by group
      rw [e] at h2
      rwa [← h2] at h'
    have hxs' : (⟨x, hx⟩ : ↥P)⁻¹ ∉ Hs := by rwa [inv_mem_iff]
    have hprod : (⟨x, hx⟩ : ↥P)⁻¹ * ⟨w * x * w⁻¹, hy⟩ ∈ Hs := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact ⟨fun h => absurd h hxs', fun h => absurd h hys⟩
    have hh₀ : x⁻¹ * (w * x * w⁻¹) ∈ H := Subgroup.mem_subgroupOf.1 hprod
    set h₀ := x⁻¹ * (w * x * w⁻¹) with hh₀def
    have hwx : w * x * w⁻¹ = x * h₀ := by rw [hh₀def]; group
    have hpow : ∀ m : ℕ, w ^ m * x * (w ^ m)⁻¹ = x * h₀ ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        calc w ^ (m + 1) * x * (w ^ (m + 1))⁻¹ = w * (w ^ m * x * (w ^ m)⁻¹) * w⁻¹ := by
              rw [pow_succ', mul_inv_rev]; group
          _ = w * (x * h₀ ^ m) * w⁻¹ := by rw [ih]
          _ = (w * x * w⁻¹) * (w * h₀ ^ m * w⁻¹) := by group
          _ = (x * h₀) * h₀ ^ m := by rw [hwx, hfixH _ (Subgroup.pow_mem H hh₀ m)]
          _ = x * h₀ ^ (m + 1) := by rw [pow_succ', mul_assoc]
    have h1 := hpow (orderOf w)
    rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at h1
    have h2 : h₀ ^ (orderOf w) = 1 := by
      have : x * h₀ ^ (orderOf w) = x * 1 := by rw [← h1, mul_one]
      exact mul_left_cancel this
    have h3 : h₀ ^ 4 = 1 := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hh₀
      have ha4' : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [ha4']
    have h4 : orderOf h₀ ∣ Nat.gcd (orderOf w) 4 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    have hcop : Nat.gcd (orderOf w) 4 = 1 := by
      have : Nat.Coprime (orderOf w) (2 ^ 2) := (Nat.coprime_two_right.2 hwo).pow_right 2
      exact this
    rw [hcop] at h4
    have h5 : h₀ = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
    rw [hwx, h5, mul_one]

end Util2

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
