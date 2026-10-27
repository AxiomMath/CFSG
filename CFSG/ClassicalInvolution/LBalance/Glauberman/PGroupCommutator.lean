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
public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.ClassicalInvolution.GlaubermanAut

section PGroupCommutator

theorem commutator_mul_central {G : Type*} [Group G] (a b x y : G) (hxa : x * a = a * x)
    (hxb : x * b = b * x) (hxy : x * y = y * x) (hya : y * a = a * y) (hyb : y * b = b * y) :
    (a * x)⁻¹ * (b * y)⁻¹ * (a * x) * (b * y) = a⁻¹ * b⁻¹ * a * b := by
  have h1 : Commute x a := hxa
  have h2 : Commute x b := hxb
  have h3 : Commute x y := hxy
  have h4 : Commute y a := hya
  have h5 : Commute y b := hyb
  have hv : Commute x (b * y) := h2.mul_right h3
  have hw : Commute x (a⁻¹ * (b * y)⁻¹ * a * (b * y)) :=
    ((h1.inv_right.mul_right hv.inv_right).mul_right h1).mul_right hv
  have hyw : Commute y (b⁻¹ * a * b) := (h5.inv_right.mul_right h4).mul_right h5
  calc (a * x)⁻¹ * (b * y)⁻¹ * (a * x) * (b * y)
      = x⁻¹ * (a⁻¹ * (b * y)⁻¹ * a * (x * (b * y))) := by group
    _ = x⁻¹ * (a⁻¹ * (b * y)⁻¹ * a * ((b * y) * x)) := by rw [hv.eq]
    _ = x⁻¹ * ((a⁻¹ * (b * y)⁻¹ * a * (b * y)) * x) := by group
    _ = x⁻¹ * (x * (a⁻¹ * (b * y)⁻¹ * a * (b * y))) := by rw [← hw.eq]
    _ = a⁻¹ * (y⁻¹ * (b⁻¹ * a * b) * y) := by group
    _ = a⁻¹ * (b⁻¹ * a * b) := by rw [mul_assoc (y⁻¹), ← hyw.eq, inv_mul_cancel_left]
    _ = a⁻¹ * b⁻¹ * a * b := by group

variable {X : Type*} [Group X] [Finite X]

theorem exists_central_involution_commutator (hX : IsPGroup 2 X)
    (hnc : ∃ a b : X, a * b ≠ b * a) :
    ∃ α β : X, α⁻¹ * β⁻¹ * α * β ≠ 1 ∧
      (α⁻¹ * β⁻¹ * α * β) * (α⁻¹ * β⁻¹ * α * β) = 1 ∧
      ∀ γ : X, (α⁻¹ * β⁻¹ * α * β) * γ = γ * (α⁻¹ * β⁻¹ * α * β) := by
  set Z := Subgroup.center X with hZ
  have hZtop : Z ≠ ⊤ := by
    intro h
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have hb : b ∈ Z := h ▸ Subgroup.mem_top b
    exact Subgroup.mem_center_iff.1 hb a
  have hnt : Nontrivial (X ⧸ Z) := QuotientGroup.nontrivial_iff.2 hZtop
  have hQp : IsPGroup 2 (X ⧸ Z) := hX.to_quotient Z
  have hcen : Nontrivial (Subgroup.center (X ⧸ Z)) := hQp.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center (X ⧸ Z)) :=
    hQp.of_injective (Subgroup.center (X ⧸ Z)).subtype (Subgroup.center (X ⧸ Z)).subtype_injective
  have h2d : 2 ∣ Nat.card (Subgroup.center (X ⧸ Z)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hcp
    have hne : Nat.card (Subgroup.center (X ⧸ Z)) ≠ 1 := by
      have := Finite.one_lt_card_iff_nontrivial.2 hcen
      omega
    rw [hn] at hne ⊢
    rcases n with _ | n
    · simp at hne
    · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2d
  obtain ⟨α, hα⟩ := QuotientGroup.mk_surjective (z : X ⧸ Z)
  have hz2 : (z : X ⧸ Z) * (z : X ⧸ Z) = 1 := by
    have : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have h2 : ((z ^ 2 : Subgroup.center (X ⧸ Z)) : X ⧸ Z) = 1 := by rw [this]; rfl
    simpa [pow_two] using h2
  have hz1 : (z : X ⧸ Z) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    omega
  have hαc : ∀ g : X ⧸ Z, g * (QuotientGroup.mk α : X ⧸ Z) = (QuotientGroup.mk α : X ⧸ Z) * g := by
    intro g
    rw [hα]
    exact Subgroup.mem_center_iff.1 z.2 g
  have hαZ : α ∉ Z := by
    intro h
    exact hz1 (hα ▸ (QuotientGroup.eq_one_iff α).2 h)
  have hβ : ∃ β : X, α * β ≠ β * α := by
    by_contra hcon
    push Not at hcon
    exact hαZ (Subgroup.mem_center_iff.2 fun g => (hcon g).symm)
  obtain ⟨β, hαβ⟩ := hβ
  have hτ1 : α⁻¹ * β⁻¹ * α * β ≠ 1 := by
    intro h
    apply hαβ
    calc α * β = (β * α) * (α⁻¹ * β⁻¹ * α * β) := by group
      _ = β * α := by rw [h, mul_one]
  have hτZ : α⁻¹ * β⁻¹ * α * β ∈ Z := by
    have h1 : ((β * α : X) : X ⧸ Z) = ((α * β : X) : X ⧸ Z) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hαc _
    have h2 := QuotientGroup.eq.1 h1
    have e : (β * α)⁻¹ * (α * β) = α⁻¹ * β⁻¹ * α * β := by group
    rwa [e] at h2
  have hτc : ∀ γ : X, (α⁻¹ * β⁻¹ * α * β) * γ = γ * (α⁻¹ * β⁻¹ * α * β) := fun γ =>
    (Subgroup.mem_center_iff.1 hτZ γ).symm
  have hα2 : α * α ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hα]
    exact hz2
  have hβα2 : β * (α * α) = (α * α) * β := Subgroup.mem_center_iff.1 hα2 β
  have hτ2 : (α⁻¹ * β⁻¹ * α * β) * (α⁻¹ * β⁻¹ * α * β) = 1 := by
    have e1 : α⁻¹ * (α⁻¹ * β⁻¹ * α * β) * α = α⁻¹ * β⁻¹ * α * β := by
      have := hτc α
      calc α⁻¹ * (α⁻¹ * β⁻¹ * α * β) * α = α⁻¹ * ((α⁻¹ * β⁻¹ * α * β) * α) := by group
        _ = α⁻¹ * (α * (α⁻¹ * β⁻¹ * α * β)) := by rw [this]
        _ = α⁻¹ * β⁻¹ * α * β := by group
    have e2 : β⁻¹ * (α * α) * β = α * α := by
      rw [mul_assoc, ← hβα2, inv_mul_cancel_left]
    calc (α⁻¹ * β⁻¹ * α * β) * (α⁻¹ * β⁻¹ * α * β)
        = (α⁻¹ * (α⁻¹ * β⁻¹ * α * β) * α) * (α⁻¹ * β⁻¹ * α * β) := by rw [e1]
      _ = (α * α)⁻¹ * (β⁻¹ * (α * α) * β) := by group
      _ = 1 := by rw [e2]; group
  exact ⟨α, β, hτ1, hτ2, hτc⟩

end PGroupCommutator

end CFSG.ClassicalInvolution.GlaubermanAut
