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

namespace CFSG.LargeExtraspecial.S10

open Subgroup

theorem le_sup_of_comm_hom {X : Type*} [Group X] [Finite X] {K K' A Z : Subgroup X} {x : X}
    (hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hcard : Nat.card K = Nat.card K')
    (hZK : Z ≤ K)
    (hcomm : ∀ k ∈ K, ∀ k' ∈ K', k * k' * k⁻¹ * k'⁻¹ ∈ Z)
    (hf : ∀ z ∈ K', z * x * z⁻¹ * x⁻¹ ∈ K ⊓ A)
    (hJ : ∀ z ∈ K', z * x * z⁻¹ * x⁻¹ ∈ Z → z ∈ Z) : K ≤ A ⊔ Z := by
  classical
  set Zs : Subgroup K := Z.subgroupOf K with hZs
  have hZn : Zs.Normal := ⟨fun n hn k => by
    have e : k * n * k⁻¹ = n := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hKab k k.2 n n.2]
      group)
    rw [e]
    exact hn⟩
  let f : K' → K := fun z => ⟨(z : X) * x * (z : X)⁻¹ * x⁻¹, (hf z z.2).1⟩
  have hfmul : ∀ z₁ z₂ : K', ((f z₁ * f z₂)⁻¹ * f (z₁ * z₂) : K) ∈ Zs := by
    intro z₁ z₂
    rw [hZs, mem_subgroupOf]
    set a : X := (z₂ : X) * x * (z₂ : X)⁻¹ * x⁻¹ with hadef
    set b : X := (z₁ : X) * x * (z₁ : X)⁻¹ * x⁻¹ with hbdef
    set c : X := (z₁ : X) * a * (z₁ : X)⁻¹ * a⁻¹ with hcdef
    have ha : a ∈ K := (hf z₂ z₂.2).1
    have hb : b ∈ K := (hf z₁ z₁.2).1
    have hc : c ∈ Z := by
      have := inv_mem (hcomm a ha z₁ z₁.2)
      rwa [show (a * (z₁ : X) * a⁻¹ * (z₁ : X)⁻¹)⁻¹ = c by rw [hcdef]; group] at this
    have hcK : c ∈ K := hZK hc
    have hab := hKab a ha b hb
    have hca := hKab c hcK a ha
    have hcb := hKab c hcK b hb
    have e1 : (z₁ : X) * (z₂ : X) * x * ((z₁ : X) * (z₂ : X))⁻¹ * x⁻¹ = c * a * b := by
      rw [hcdef, hadef, hbdef]
      group
    have e : (((f z₁ * f z₂)⁻¹ * f (z₁ * z₂) : K) : X) = c := by
      simp only [f, Subgroup.coe_mul, Subgroup.coe_inv]
      change (b * a)⁻¹ * ((z₁ : X) * (z₂ : X) * x * ((z₁ : X) * (z₂ : X))⁻¹ * x⁻¹) = c
      rw [e1]
      calc (b * a)⁻¹ * (c * a * b) = a⁻¹ * b⁻¹ * (c * a) * b := by group
        _ = a⁻¹ * b⁻¹ * (a * c) * b := by rw [hca]
        _ = a⁻¹ * b⁻¹ * a * (c * b) := by group
        _ = a⁻¹ * b⁻¹ * a * (b * c) := by rw [hcb]
        _ = a⁻¹ * b⁻¹ * (a * b) * c := by group
        _ = a⁻¹ * b⁻¹ * (b * a) * c := by rw [hab]
        _ = c := by group
    rw [e]
    exact hc
  let F : K' →* K ⧸ Zs := MonoidHom.mk' (fun z => QuotientGroup.mk (f z)) (fun z₁ z₂ => by
    change QuotientGroup.mk (f (z₁ * z₂)) = QuotientGroup.mk (f z₁) * QuotientGroup.mk (f z₂)
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq.mpr (hfmul z₁ z₂)).symm)
  have hFker : ∀ z : K', F z = 1 → (z : X) ∈ Z := by
    intro z hz
    change QuotientGroup.mk (f z) = 1 at hz
    rw [QuotientGroup.eq_one_iff, hZs, mem_subgroupOf] at hz
    exact hJ z z.2 hz
  have h1 : Nat.card K' = Nat.card F.range * Nat.card F.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup F.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange F).toEquiv]
  have h2 : Nat.card F.ker ≤ Nat.card Z := by
    have hle : F.ker.map K'.subtype ≤ Z := by
      rintro _ ⟨z, hz, rfl⟩
      exact hFker z hz
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective K'.subtype_injective] at this
  have h3 : Nat.card K = Nat.card (K ⧸ Zs) * Nat.card Z := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Zs, hZs,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv]
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have h4 : Nat.card (K ⧸ Zs) ≤ Nat.card F.range := by
    have := Nat.mul_le_mul_left (Nat.card F.range) h2
    have h5 : Nat.card (K ⧸ Zs) * Nat.card Z ≤ Nat.card F.range * Nat.card Z := by
      rw [← h3, hcard, h1]
      exact this
    exact Nat.le_of_mul_le_mul_right h5 hZpos
  have htop : F.range = ⊤ := by
    refine Subgroup.eq_top_of_le_card _ ?_
    exact h4
  intro k hk
  obtain ⟨z, hz⟩ : (QuotientGroup.mk (⟨k, hk⟩ : K) : K ⧸ Zs) ∈ F.range := by
    rw [htop]
    exact mem_top _
  change QuotientGroup.mk (f z) = QuotientGroup.mk ⟨k, hk⟩ at hz
  rw [QuotientGroup.eq, hZs, mem_subgroupOf] at hz
  have hfz : (z : X) * x * (z : X)⁻¹ * x⁻¹ ∈ A := (hf z z.2).2
  have e : k = ((z : X) * x * (z : X)⁻¹ * x⁻¹) * (((f z)⁻¹ * ⟨k, hk⟩ : K) : X) := by
    simp only [f, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact mul_mem_sup hfz hz

end CFSG.LargeExtraspecial.S10
