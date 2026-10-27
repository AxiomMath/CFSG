module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalInvolution.Q3.TF1

theorem q8_mul_mul_of_ne : ∀ p q : QuaternionGroup 2, p * p = QuaternionGroup.a 2 →
    q * q = QuaternionGroup.a 2 → q ≠ p → q ≠ p⁻¹ →
      (p * q) * (p * q) = QuaternionGroup.a 2 ∧ q * p = (p * q)⁻¹ := by
  decide

theorem q8_eq_of_mul_self_eq_one : ∀ p : QuaternionGroup 2, p * p = 1 →
    p = 1 ∨ p = QuaternionGroup.a 2 := by
  decide

theorem q8_mul_self_eq : ∀ p : QuaternionGroup 2, p * p = 1 ∨ p * p = QuaternionGroup.a 2 := by
  decide

theorem q8_a_one_mul_self : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
    QuaternionGroup.a 2 := by
  decide

theorem q8_a_two_ne_one : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by
  decide

theorem q8_a_two_mul_self : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by
  decide

theorem q8_eq_of_comm : ∀ p c : QuaternionGroup 2, p * p = QuaternionGroup.a 2 →
    c * c = QuaternionGroup.a 2 → c * p = p * c → c = p ∨ c = p⁻¹ := by
  decide

theorem q8_eq_of_ne : ∀ v b c : QuaternionGroup 2, v * v = QuaternionGroup.a 2 →
    b * b = QuaternionGroup.a 2 → b ≠ v → b ≠ v⁻¹ → c * c = QuaternionGroup.a 2 → c ≠ v →
      c ≠ v⁻¹ → c = b ∨ c = b⁻¹ ∨ c = v * b ∨ c = (v * b)⁻¹ := by
  decide

theorem q8_eq_elems : ∀ v b x : QuaternionGroup 2, v * v = QuaternionGroup.a 2 →
    b * b = QuaternionGroup.a 2 → b ≠ v → b ≠ v⁻¹ → x = 1 ∨ x = v * v ∨ x = v ∨ x = v⁻¹ ∨ x = b ∨
      x = b⁻¹ ∨ x = v * b ∨ x = (v * b)⁻¹ := by
  decide

theorem q8_sq_mul : ∀ v b : QuaternionGroup 2, v * v = QuaternionGroup.a 2 →
    b * b = QuaternionGroup.a 2 → v * v * b = b⁻¹ := by
  decide

theorem q8_conj_inv : ∀ v b : QuaternionGroup 2, v * v = QuaternionGroup.a 2 →
    b * b = QuaternionGroup.a 2 → b ≠ v → b ≠ v⁻¹ → v * b * v⁻¹ = b⁻¹ := by
  decide

theorem q8_mul_mul_eq : ∀ v b : QuaternionGroup 2, v * v = QuaternionGroup.a 2 →
    b * b = QuaternionGroup.a 2 → b ≠ v → b ≠ v⁻¹ → v * b * v = b := by
  decide

theorem q8_exists_ne : ∀ v : QuaternionGroup 2, v * v = QuaternionGroup.a 2 →
    ∃ b : QuaternionGroup 2, b * b = QuaternionGroup.a 2 ∧ b ≠ v ∧ b ≠ v⁻¹ := by
  decide

namespace Q8Sub

variable {G : Type*} [Group G] {Q : Subgroup G} (e : ↥Q ≃* QuaternionGroup 2)
include e

theorem mul_self_eq {y : G} (hy : y ∈ Q) :
    y * y = 1 ∨ y * y = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) := by
  rcases q8_mul_self_eq (e ⟨y, hy⟩) with h | h
  · left
    have h1 : (⟨y, hy⟩ : ↥Q) * ⟨y, hy⟩ = 1 := e.injective (by rw [map_mul, h, map_one])
    exact congrArg Subtype.val h1
  · right
    have h1 : (⟨y, hy⟩ : ↥Q) * ⟨y, hy⟩ = e.symm (QuaternionGroup.a 2) :=
      e.injective (by rw [map_mul, h, MulEquiv.apply_symm_apply])
    exact congrArg Subtype.val h1

theorem eq_of_mul_self_eq_one {y : G} (hy : y ∈ Q) (h : y * y = 1) :
    y = 1 ∨ y = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) := by
  have h1 : e ⟨y, hy⟩ * e ⟨y, hy⟩ = 1 := by
    rw [← map_mul]
    have : (⟨y, hy⟩ : ↥Q) * ⟨y, hy⟩ = 1 := Subtype.ext h
    rw [this, map_one]
  rcases q8_eq_of_mul_self_eq_one _ h1 with h2 | h2
  · left
    have : (⟨y, hy⟩ : ↥Q) = 1 := e.injective (by rw [h2, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨y, hy⟩ : ↥Q) = e.symm (QuaternionGroup.a 2) :=
      e.injective (by rw [h2, MulEquiv.apply_symm_apply])
    exact congrArg Subtype.val this

theorem mem_inv : ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) ∈ Q := (e.symm _).2

theorem inv_mul_self : ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) *
    ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) = 1 := by
  rw [← Subgroup.coe_mul, ← map_mul, q8_a_two_mul_self, map_one, Subgroup.coe_one]

theorem inv_ne_one : ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) ≠ 1 := by
  intro h
  apply q8_a_two_ne_one
  have : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
  rw [← e.apply_symm_apply (QuaternionGroup.a 2), this, map_one]

theorem exists_mul_self_eq : ∃ p ∈ Q, p * p = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) := by
  refine ⟨((e.symm (QuaternionGroup.a 1) : ↥Q) : G), (e.symm _).2, ?_⟩
  rw [← Subgroup.coe_mul, ← map_mul, q8_a_one_mul_self]

theorem anticomm {p q : G} (hp : p ∈ Q) (hq : q ∈ Q)
    (hp2 : p * p = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G))
    (hq2 : q * q = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G)) (hne : q ≠ p) (hne' : q ≠ p⁻¹) :
    (p * q) * (p * q) = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) ∧ q * p = (p * q)⁻¹ := by
  set p' : QuaternionGroup 2 := e ⟨p, hp⟩ with hp'
  set q' : QuaternionGroup 2 := e ⟨q, hq⟩ with hq'
  have hsq : ∀ {y : G} (hy : y ∈ Q), y * y = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) →
      e ⟨y, hy⟩ * e ⟨y, hy⟩ = QuaternionGroup.a 2 := by
    intro y hy h
    rw [← map_mul]
    have : (⟨y, hy⟩ : ↥Q) * ⟨y, hy⟩ = e.symm (QuaternionGroup.a 2) := Subtype.ext h
    rw [this, MulEquiv.apply_symm_apply]
  have h1 : q' ≠ p' := fun h => hne (congrArg Subtype.val (e.injective h))
  have h2 : q' ≠ p'⁻¹ := by
    intro h
    apply hne'
    have : (⟨q, hq⟩ : ↥Q) = (⟨p, hp⟩ : ↥Q)⁻¹ := e.injective (by rw [map_inv]; exact h)
    exact congrArg Subtype.val this
  obtain ⟨h3, h4⟩ := q8_mul_mul_of_ne p' q' (hsq hp hp2) (hsq hq hq2) h1 h2
  refine ⟨?_, ?_⟩
  · have : (⟨p, hp⟩ : ↥Q) * ⟨q, hq⟩ * (⟨p, hp⟩ * ⟨q, hq⟩) = e.symm (QuaternionGroup.a 2) :=
      e.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact h3)
    exact congrArg Subtype.val this
  · have : (⟨q, hq⟩ : ↥Q) * ⟨p, hp⟩ = (⟨p, hp⟩ * ⟨q, hq⟩)⁻¹ :=
      e.injective (by rw [map_mul, map_inv, map_mul]; exact h4)
    exact congrArg Subtype.val this

theorem orderOf_eq_four_iff {y : G} (hy : y ∈ Q) :
    orderOf y = 4 ↔ y * y = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) := by
  constructor
  · intro h4
    rcases mul_self_eq e hy with h | h
    · exfalso
      have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
      rw [h4] at this
      omega
    · exact h
  · intro h
    have hs := inv_mul_self e
    have hs1 := inv_ne_one e
    have h1 : ¬ y ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq, h]
      exact hs1
    have h2 : y ^ 2 ^ (1 + 1) = 1 := by
      have e4 : y ^ 2 ^ (1 + 1) = (y * y) * (y * y) := by
        rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [e4, h, hs]
    rw [orderOf_eq_prime_pow h1 h2]
    norm_num

theorem exists_comm_of_four {c₁ c₂ : G} (hc₁Q : ∀ q ∈ Q, c₁ * q * c₁⁻¹ ∈ Q)
    (hc₂Q : ∀ q ∈ Q, c₂ * q * c₂⁻¹ ∈ Q) (hc₁2 : c₁ * c₁ = 1) (hc₁₂ : c₁ * c₂ = c₂ * c₁)
    (hna : ¬ ∃ w ∈ Q, orderOf w = 4 ∧ w * c₁ = c₁ * w) :
    (∃ w ∈ Q, orderOf w = 4 ∧ w * c₂ = c₂ * w) ∨
      ∃ w ∈ Q, orderOf w = 4 ∧ w * (c₁ * c₂) = (c₁ * c₂) * w := by
  set s : G := ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) with hs
  have hsQ : s ∈ Q := mem_inv e
  have hss : s * s = 1 := inv_mul_self e
  have hs1 : s ≠ 1 := inv_ne_one e
  have hcs : ∀ c : G, (∀ q ∈ Q, c * q * c⁻¹ ∈ Q) → c * s * c⁻¹ = s := by
    intro c hc
    have h1 : c * s * c⁻¹ ∈ Q := hc s hsQ
    have h2 : (c * s * c⁻¹) * (c * s * c⁻¹) = 1 := by
      rw [show c * s * c⁻¹ * (c * s * c⁻¹) = c * (s * s) * c⁻¹ by group, hss]
      group
    rcases eq_of_mul_self_eq_one e h1 h2 with h | h
    · exfalso
      apply hs1
      calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hsqc : ∀ c : G, (∀ q ∈ Q, c * q * c⁻¹ ∈ Q) → ∀ y : G, y * y = s →
      (c * y * c⁻¹) * (c * y * c⁻¹) = s := by
    intro c hc y hy
    rw [show c * y * c⁻¹ * (c * y * c⁻¹) = c * (y * y) * c⁻¹ by group, hy, hcs c hc]
  have hcomm : ∀ c y : G, c * y * c⁻¹ = y → y * c = c * y := by
    intro c y h
    calc y * c = c * y * c⁻¹ * c := by rw [h]
      _ = c * y := by group
  obtain ⟨p₀, hp₀Q, hp₀2⟩ := exists_mul_self_eq e
  obtain ⟨y₀, hy₀Q, hy₀2, hy₀inv⟩ : ∃ y₀ ∈ Q, y₀ * y₀ = s ∧ c₁ * y₀ * c₁⁻¹ = y₀⁻¹ := by
    set q₁ : G := c₁ * p₀ * c₁⁻¹ with hq₁
    have hq₁Q : q₁ ∈ Q := hc₁Q p₀ hp₀Q
    have hq₁2 : q₁ * q₁ = s := hsqc c₁ hc₁Q p₀ hp₀2
    by_cases h1 : q₁ = p₀
    · exact absurd ⟨p₀, hp₀Q, (orderOf_eq_four_iff e hp₀Q).mpr hp₀2, hcomm c₁ p₀ h1⟩ hna
    by_cases h2 : q₁ = p₀⁻¹
    · exact ⟨p₀, hp₀Q, hp₀2, h2⟩
    obtain ⟨h3, h4⟩ := anticomm e hp₀Q hq₁Q hp₀2 hq₁2 h1 h2
    refine ⟨p₀ * q₁, Q.mul_mem hp₀Q hq₁Q, h3, ?_⟩
    have hcc : c₁ * q₁ * c₁⁻¹ = p₀ := by
      rw [hq₁, show c₁ * (c₁ * p₀ * c₁⁻¹) * c₁⁻¹ = (c₁ * c₁) * p₀ * (c₁ * c₁)⁻¹ by group, hc₁2]
      group
    calc c₁ * (p₀ * q₁) * c₁⁻¹ = (c₁ * p₀ * c₁⁻¹) * (c₁ * q₁ * c₁⁻¹) := by group
      _ = q₁ * p₀ := by rw [hcc]
      _ = (p₀ * q₁)⁻¹ := h4
  set y₁ : G := c₂ * y₀ * c₂⁻¹ with hy₁
  have hy₁Q : y₁ ∈ Q := hc₂Q y₀ hy₀Q
  have hy₁2 : y₁ * y₁ = s := hsqc c₂ hc₂Q y₀ hy₀2
  have hc₂₁ : c₂ * c₁ = c₁ * c₂ := hc₁₂.symm
  have hy₁inv : c₁ * y₁ * c₁⁻¹ = y₁⁻¹ := by
    have e1 : c₁ * y₁ * c₁⁻¹ = c₂ * (c₁ * y₀ * c₁⁻¹) * c₂⁻¹ := by
      rw [hy₁]
      calc c₁ * (c₂ * y₀ * c₂⁻¹) * c₁⁻¹ = (c₁ * c₂) * y₀ * (c₁ * c₂)⁻¹ := by group
        _ = (c₂ * c₁) * y₀ * (c₂ * c₁)⁻¹ := by rw [hc₁₂]
        _ = c₂ * (c₁ * y₀ * c₁⁻¹) * c₂⁻¹ := by group
    rw [e1, hy₀inv, hy₁]
    group
  by_cases h1 : y₁ = y₀
  · exact Or.inl ⟨y₀, hy₀Q, (orderOf_eq_four_iff e hy₀Q).mpr hy₀2, hcomm c₂ y₀ h1⟩
  by_cases h2 : y₁ = y₀⁻¹
  · refine Or.inr ⟨y₀, hy₀Q, (orderOf_eq_four_iff e hy₀Q).mpr hy₀2, hcomm _ y₀ ?_⟩
    calc c₁ * c₂ * y₀ * (c₁ * c₂)⁻¹ = c₁ * y₁ * c₁⁻¹ := by rw [hy₁]; group
      _ = c₁ * y₀⁻¹ * c₁⁻¹ := by rw [h2]
      _ = (c₁ * y₀ * c₁⁻¹)⁻¹ := by group
      _ = y₀ := by rw [hy₀inv, inv_inv]
  · exfalso
    obtain ⟨h3, h4⟩ := anticomm e hy₀Q hy₁Q hy₀2 hy₁2 h1 h2
    refine hna ⟨y₀ * y₁, Q.mul_mem hy₀Q hy₁Q, (orderOf_eq_four_iff e (Q.mul_mem hy₀Q hy₁Q)).mpr h3,
      hcomm c₁ _ ?_⟩
    calc c₁ * (y₀ * y₁) * c₁⁻¹ = (c₁ * y₀ * c₁⁻¹) * (c₁ * y₁ * c₁⁻¹) := by group
      _ = y₀⁻¹ * y₁⁻¹ := by rw [hy₀inv, hy₁inv]
      _ = (y₁ * y₀)⁻¹ := by group
      _ = y₀ * y₁ := by rw [h4, inv_inv]

theorem coe_symm_mul (x y : QuaternionGroup 2) :
    ((e.symm x : ↥Q) : G) * ((e.symm y : ↥Q) : G) = ((e.symm (x * y) : ↥Q) : G) := by
  rw [map_mul, Subgroup.coe_mul]

theorem coe_symm_inv (x : QuaternionGroup 2) :
    ((e.symm x : ↥Q) : G)⁻¹ = ((e.symm x⁻¹ : ↥Q) : G) := by
  rw [map_inv, Subgroup.coe_inv]

theorem coe_symm_one : ((e.symm 1 : ↥Q) : G) = 1 := by
  rw [map_one, Subgroup.coe_one]

theorem coe_symm_inj {x y : QuaternionGroup 2} :
    ((e.symm x : ↥Q) : G) = ((e.symm y : ↥Q) : G) ↔ x = y :=
  ⟨fun h => e.symm.injective (Subtype.ext h), fun h => h ▸ rfl⟩

theorem exists_coe_symm {p : G} (hp : p ∈ Q) : ∃ x : QuaternionGroup 2, p = ((e.symm x : ↥Q) : G) :=
  ⟨e ⟨p, hp⟩, by rw [MulEquiv.symm_apply_apply]⟩

theorem eq_of_comm {p c : G} (hp : p ∈ Q) (hc : c ∈ Q)
    (hp2 : p * p = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G))
    (hc2 : c * c = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G)) (hpc : c * p = p * c) :
    c = p ∨ c = p⁻¹ := by
  obtain ⟨x, rfl⟩ := exists_coe_symm e hp
  obtain ⟨y, rfl⟩ := exists_coe_symm e hc
  rw [coe_symm_mul, coe_symm_inj] at hp2 hc2
  rw [coe_symm_mul, coe_symm_mul, coe_symm_inj] at hpc
  rw [coe_symm_inv, coe_symm_inj, coe_symm_inj]
  exact q8_eq_of_comm x y hp2 hc2 hpc

theorem eq_of_ne {v b c : G} (hv : v ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q)
    (hv2 : v * v = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G))
    (hb2 : b * b = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G)) (hbv : b ≠ v) (hbv' : b ≠ v⁻¹)
    (hc2 : c * c = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G)) (hcv : c ≠ v) (hcv' : c ≠ v⁻¹) :
    c = b ∨ c = b⁻¹ ∨ c = v * b ∨ c = (v * b)⁻¹ := by
  obtain ⟨x, rfl⟩ := exists_coe_symm e hv
  obtain ⟨y, rfl⟩ := exists_coe_symm e hb
  obtain ⟨w, rfl⟩ := exists_coe_symm e hc
  rw [coe_symm_mul, coe_symm_inj] at hv2 hb2 hc2
  rw [coe_symm_inv, Ne, coe_symm_inj] at hbv' hcv'
  rw [Ne, coe_symm_inj] at hbv hcv
  rw [coe_symm_inv, coe_symm_mul, coe_symm_inv, coe_symm_inj, coe_symm_inj, coe_symm_inj,
    coe_symm_inj]
  exact q8_eq_of_ne x y w hv2 hb2 hbv hbv' hc2 hcv hcv'

theorem eq_elems {v b x : G} (hv : v ∈ Q) (hb : b ∈ Q) (hx : x ∈ Q)
    (hv2 : v * v = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G))
    (hb2 : b * b = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G)) (hbv : b ≠ v) (hbv' : b ≠ v⁻¹) :
    x = 1 ∨ x = v * v ∨ x = v ∨ x = v⁻¹ ∨ x = b ∨ x = b⁻¹ ∨ x = v * b ∨ x = (v * b)⁻¹ := by
  obtain ⟨p, rfl⟩ := exists_coe_symm e hv
  obtain ⟨q, rfl⟩ := exists_coe_symm e hb
  obtain ⟨w, rfl⟩ := exists_coe_symm e hx
  rw [coe_symm_mul, coe_symm_inj] at hv2 hb2
  rw [coe_symm_inv, Ne, coe_symm_inj] at hbv'
  rw [Ne, coe_symm_inj] at hbv
  rw [← coe_symm_one e, coe_symm_mul, coe_symm_inv, coe_symm_inv, coe_symm_mul, coe_symm_inv,
    coe_symm_inj, coe_symm_inj, coe_symm_inj, coe_symm_inj, coe_symm_inj, coe_symm_inj,
    coe_symm_inj, coe_symm_inj]
  exact q8_eq_elems p q w hv2 hb2 hbv hbv'

theorem rels {v b : G} (hv : v ∈ Q) (hb : b ∈ Q)
    (hv2 : v * v = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G))
    (hb2 : b * b = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G)) (hbv : b ≠ v) (hbv' : b ≠ v⁻¹) :
    v * v * b = b⁻¹ ∧ v * b * v⁻¹ = b⁻¹ ∧ v * b * v = b := by
  obtain ⟨p, rfl⟩ := exists_coe_symm e hv
  obtain ⟨q, rfl⟩ := exists_coe_symm e hb
  rw [coe_symm_mul, coe_symm_inj] at hv2 hb2
  rw [coe_symm_inv, Ne, coe_symm_inj] at hbv'
  rw [Ne, coe_symm_inj] at hbv
  refine ⟨?_, ?_, ?_⟩
  · rw [coe_symm_mul, coe_symm_mul, coe_symm_inv, coe_symm_inj]
    exact q8_sq_mul p q hv2 hb2
  · rw [coe_symm_mul, coe_symm_inv, coe_symm_mul, coe_symm_inv, coe_symm_inj]
    exact q8_conj_inv p q hv2 hb2 hbv hbv'
  · rw [coe_symm_mul, coe_symm_mul, coe_symm_inj]
    exact q8_mul_mul_eq p q hv2 hb2 hbv hbv'

theorem exists_ne {v : G} (hv : v ∈ Q) (hv2 : v * v = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G)) :
    ∃ b ∈ Q, b * b = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) ∧ b ≠ v ∧ b ≠ v⁻¹ := by
  obtain ⟨p, rfl⟩ := exists_coe_symm e hv
  rw [coe_symm_mul, coe_symm_inj] at hv2
  obtain ⟨q, hq2, hqp, hqp'⟩ := q8_exists_ne p hv2
  refine ⟨((e.symm q : ↥Q) : G), (e.symm q).2, ?_, ?_, ?_⟩
  · rw [coe_symm_mul, coe_symm_inj]
    exact hq2
  · rw [Ne, coe_symm_inj]
    exact hqp
  · rw [coe_symm_inv, Ne, coe_symm_inj]
    exact hqp'

theorem pow_four_comm {g v : G} (hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hv : v ∈ Q)
    (hv2 : v * v = ((e.symm (QuaternionGroup.a 2) : ↥Q) : G))
    (hgv : g * v * g⁻¹ = v ∨ g * v * g⁻¹ = v⁻¹) :
    ∀ x ∈ Q, g * g * g * g * x = x * (g * g * g * g) := by
  set s : G := ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) with hs
  obtain ⟨b, hbQ, hb2, hbv, hbv'⟩ := exists_ne e hv hv2
  obtain ⟨-, hrel2, hrel3⟩ := rels e hv hbQ hv2 hb2 hbv hbv'
  have hrel1 := (rels e hv hbQ hv2 hb2 hbv hbv').1
  have hcs : g * s * g⁻¹ = s := by
    have h1 : g * s * g⁻¹ ∈ Q := hgQ s (mem_inv e)
    have h2 : (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := by
      rw [show g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ by group, inv_mul_self e]
      group
    rcases eq_of_mul_self_eq_one e h1 h2 with h | h
    · exfalso
      apply inv_ne_one e
      calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hsq : ∀ y : G, y * y = s → (g * y * g⁻¹) * (g * y * g⁻¹) = s := by
    intro y hy
    rw [show g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group, hy, hcs]
  have hgb2 := hsq b hb2
  have hgbQ := hgQ b hbQ
  have hgbv : g * b * g⁻¹ ≠ v ∧ g * b * g⁻¹ ≠ v⁻¹ := by
    constructor
    · intro h
      rcases hgv with h' | h'
      · apply hbv
        have := congrArg (fun y => g⁻¹ * y * g) (h.trans h'.symm)
        simpa [mul_assoc] using this
      · apply hbv'
        have : g * b * g⁻¹ = g * v⁻¹ * g⁻¹ := by
          rw [h, show g * v⁻¹ * g⁻¹ = (g * v * g⁻¹)⁻¹ by group, h', inv_inv]
        have := congrArg (fun y => g⁻¹ * y * g) this
        simpa [mul_assoc] using this
    · intro h
      rcases hgv with h' | h'
      · apply hbv'
        have : g * b * g⁻¹ = g * v⁻¹ * g⁻¹ := by
          rw [h, show g * v⁻¹ * g⁻¹ = (g * v * g⁻¹)⁻¹ by group, h']
        have := congrArg (fun y => g⁻¹ * y * g) this
        simpa [mul_assoc] using this
      · apply hbv
        have : g * b * g⁻¹ = g * v * g⁻¹ := by rw [h, h']
        have := congrArg (fun y => g⁻¹ * y * g) this
        simpa [mul_assoc] using this
  have hg2v : g * (g * v * g⁻¹) * g⁻¹ = v := by
    rcases hgv with h | h
    · rw [h, h]
    · rw [h, show g * v⁻¹ * g⁻¹ = (g * v * g⁻¹)⁻¹ by group, h, inv_inv]
  have hg2b : g * (g * b * g⁻¹) * g⁻¹ = b ∨ g * (g * b * g⁻¹) * g⁻¹ = b⁻¹ := by
    rcases eq_of_ne e hv hbQ hgbQ hv2 hb2 hbv hbv' hgb2 hgbv.1 hgbv.2 with h | h | h | h
    · left
      rw [h, h]
    · left
      rw [h, show g * b⁻¹ * g⁻¹ = (g * b * g⁻¹)⁻¹ by group, h, inv_inv]
    · rw [h, show g * (v * b) * g⁻¹ = (g * v * g⁻¹) * (g * b * g⁻¹) by group, h]
      rcases hgv with h' | h'
      · right
        rw [h', ← mul_assoc, hrel1]
      · left
        rw [h']
        group
    · rw [h, show g * (v * b)⁻¹ * g⁻¹ = ((g * v * g⁻¹) * (g * b * g⁻¹))⁻¹ by group, h]
      rcases hgv with h' | h'
      · right
        rw [h', show (v * (v * b)⁻¹)⁻¹ = v * b * v⁻¹ by group, hrel2]
      · left
        rw [h', show (v⁻¹ * (v * b)⁻¹)⁻¹ = v * b * v by group, hrel3]
  set g4 : G := g * g * g * g with hg4
  have h4 : ∀ y : G, g4 * y * g4⁻¹ = g * (g * (g * (g * y * g⁻¹) * g⁻¹) * g⁻¹) * g⁻¹ := by
    intro y
    rw [hg4]
    group
  have h4v : g4 * v * g4⁻¹ = v := by
    rw [h4, hg2v, hg2v]
  have h4b : g4 * b * g4⁻¹ = b := by
    rw [h4]
    rcases hg2b with h | h
    · rw [h, h]
    · rw [h, show g * (g * b⁻¹ * g⁻¹) * g⁻¹ = (g * (g * b * g⁻¹) * g⁻¹)⁻¹ by
        simp only [mul_inv_rev, inv_inv, mul_assoc], h, inv_inv]
  have hcomm : ∀ y : G, g4 * y * g4⁻¹ = y → g4 * y = y * g4 := by
    intro y hy
    calc g4 * y = g4 * y * g4⁻¹ * g4 := by group
      _ = y * g4 := by rw [hy]
  have hcv := hcomm v h4v
  have hcb := hcomm b h4b
  have hmul : ∀ y₁ y₂ : G, g4 * y₁ = y₁ * g4 → g4 * y₂ = y₂ * g4 →
      g4 * (y₁ * y₂) = y₁ * y₂ * g4 := by
    intro y₁ y₂ h₁ h₂
    calc g4 * (y₁ * y₂) = (g4 * y₁) * y₂ := by group
      _ = y₁ * (g4 * y₂) := by rw [h₁, mul_assoc]
      _ = y₁ * (y₂ * g4) := by rw [h₂]
      _ = y₁ * y₂ * g4 := by group
  have hinv : ∀ y : G, g4 * y = y * g4 → g4 * y⁻¹ = y⁻¹ * g4 := by
    intro y h
    calc g4 * y⁻¹ = y⁻¹ * (y * g4) * y⁻¹ := by group
      _ = y⁻¹ * (g4 * y) * y⁻¹ := by rw [h]
      _ = y⁻¹ * g4 := by group
  intro x hx
  have key : g4 * x = x * g4 := by
    rcases eq_elems e hv hbQ hx hv2 hb2 hbv hbv' with h | h | h | h | h | h | h | h <;> rw [h]
    · group
    · exact hmul v v hcv hcv
    · exact hcv
    · exact hinv v hcv
    · exact hcb
    · exact hinv b hcb
    · exact hmul v b hcv hcb
    · exact hinv _ (hmul v b hcv hcb)
  exact key

end Q8Sub

end CFSG.ClassicalInvolution.Q3.TF1
