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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial.S9

open Subgroup

variable {M : Type*} [Group M]

@[expose] def nOrbit (N : Subgroup M) (τ : M) : Set M := {x | ∃ n ∈ N, n * τ * n⁻¹ = x}

theorem self_mem_nOrbit (N : Subgroup M) (τ : M) : τ ∈ nOrbit N τ :=
  ⟨1, N.one_mem, by simp⟩

theorem conj_mem_nOrbit {N : Subgroup M} {τ x c : M} (hc : c ∈ N) (hx : x ∈ nOrbit N τ) :
    c * x * c⁻¹ ∈ nOrbit N τ := by
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨c * n, N.mul_mem hc hn, by group⟩

theorem eq_one_or_eq_of_mem_zpowers {t x : M} (ht : t * t = 1) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  obtain ⟨r, rfl | rfl⟩ := Int.even_or_odd' k
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem commute_conj_conj {a b : M} (c : M) (h : Commute a b) :
    Commute (c * a * c⁻¹) (c * b * c⁻¹) := by
  change c * a * c⁻¹ * (c * b * c⁻¹) = c * b * c⁻¹ * (c * a * c⁻¹)
  calc c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
    _ = c * (b * a) * c⁻¹ := by rw [h.eq]
    _ = c * b * c⁻¹ * (c * a * c⁻¹) := by group

theorem conj_ne_conj {a b : M} (c : M) (h : a ≠ b) : c * a * c⁻¹ ≠ c * b * c⁻¹ :=
  fun e => h (by simpa using e)

section Lambda

variable {t τ : M} {N : Subgroup M}

theorem mem_of_mul_mem_nOrbit (hτ : τ * τ = 1) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N) {y : M}
    (hy : τ * y ∈ nOrbit N τ) : y ∈ N := by
  obtain ⟨n, hn, h⟩ := hy
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hy' : y = τ * n * τ⁻¹ * n⁻¹ := by
    have h' : y = τ⁻¹ * (n * τ * n⁻¹) := by rw [h]; group
    rw [h', hτi]; group
  rw [hy']
  exact N.mul_mem (hτN n hn) (N.inv_mem hn)

theorem mul_self_eq_one_of_mul_mem_nOrbit (ht : t * t = 1) (hτ : τ * τ = 1)
    (htτ : Commute t τ) (hsq : ∀ n ∈ N, n * n ∈ zpowers t)
    (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N) (hnc : ∀ n ∈ N, n * τ * n⁻¹ ≠ τ * t) {y : M}
    (hy : τ * y ∈ nOrbit N τ) : y * y = 1 := by
  have hyN := mem_of_mul_mem_nOrbit hτ hτN hy
  rcases eq_one_or_eq_of_mem_zpowers ht (hsq y hyN) with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn, hx⟩ := hy
    have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
    set x := n * τ * n⁻¹ with hxdef
    have hx2 : x * x = 1 :=
      calc x * x = n * (τ * τ) * n⁻¹ := by rw [hxdef]; group
        _ = 1 := by rw [hτ, mul_one, mul_inv_cancel]
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have hyx : y = τ * x := by rw [hx, ← mul_assoc, hτ, one_mul]
    apply hnc y hyN
    rw [hyx] at h ⊢
    calc τ * x * τ * (τ * x)⁻¹ = τ * x * (τ * x) * τ := by rw [mul_inv_rev, hxi, hτi]; group
      _ = t * τ := by rw [h]
      _ = τ * t := htτ.eq

theorem commute_of_mul_mem_nOrbit (hτ : τ * τ = 1) {y : M} (hy : τ * y ∈ nOrbit N τ)
    (hy2 : y * y = 1) : Commute τ y := by
  obtain ⟨n, -, hx⟩ := hy
  set x := n * τ * n⁻¹ with hxdef
  have hyx : y = τ * x := by rw [hx, ← mul_assoc, hτ, one_mul]
  have hτx : τ * x * τ = x := by
    have h1 : τ * x * τ * x = 1 := by rw [hyx] at hy2; rw [← hy2]; group
    have hx2 : x * x = 1 :=
      calc x * x = n * (τ * τ) * n⁻¹ := by rw [hxdef]; group
        _ = 1 := by rw [hτ, mul_one, mul_inv_cancel]
    calc τ * x * τ = τ * x * τ * (x * x) := by rw [hx2, mul_one]
      _ = (τ * x * τ * x) * x := by group
      _ = x := by rw [h1, one_mul]
  change τ * y = y * τ
  rw [hyx, ← mul_assoc, hτ, one_mul, hτx]

theorem mul_t_not_mem_nOrbit (ht : t * t = 1) (htc : ∀ n ∈ N, Commute n t)
    (hnc : ∀ n ∈ N, n * τ * n⁻¹ ≠ τ * t) {y : M} (hy : τ * y ∈ nOrbit N τ) :
    τ * (y * t) ∉ nOrbit N τ := by
  rintro ⟨m, hm, h2⟩
  obtain ⟨n, hn, h1⟩ := hy
  apply hnc (m⁻¹ * n) (N.mul_mem (N.inv_mem hm) hn)
  have h3 : τ * y = m * τ * m⁻¹ * t⁻¹ := by rw [h2]; group
  calc m⁻¹ * n * τ * (m⁻¹ * n)⁻¹ = m⁻¹ * (n * τ * n⁻¹) * m := by group
    _ = m⁻¹ * (m * τ * m⁻¹ * t⁻¹) * m := by rw [h1, h3]
    _ = τ * (m⁻¹ * (t⁻¹ * m)) := by group
    _ = τ * t⁻¹ := by rw [← (htc m hm).inv_right.eq]; group
    _ = τ * t := by rw [inv_eq_of_mul_eq_one_right ht]

theorem mul_mem_nOrbit_or (ht : t * t = 1) (hτ : τ * τ = 1)
    (hcomm : ∀ n ∈ N, ∀ m ∈ N, n * m * n⁻¹ * m⁻¹ ∈ zpowers t) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N)
    {y₁ y₂ : M} (hy₁ : τ * y₁ ∈ nOrbit N τ) (hy₂ : τ * y₂ ∈ nOrbit N τ) :
    τ * (y₁ * y₂) ∈ nOrbit N τ ∨ τ * (t * (y₁ * y₂)) ∈ nOrbit N τ := by
  have hy₁N := mem_of_mul_mem_nOrbit hτ hτN hy₁
  obtain ⟨n₁, hn₁, h1⟩ := hy₁
  obtain ⟨n₂, hn₂, h2⟩ := hy₂
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have ha : τ⁻¹ * n₂ * τ ∈ N := by
    have := hτN n₂ hn₂
    rw [hτi] at this ⊢
    exact this
  have e1 : y₁ = τ⁻¹ * (n₁ * τ * n₁⁻¹) := by rw [h1]; group
  have e2 : y₂ = τ⁻¹ * (n₂ * τ * n₂⁻¹) := by rw [h2]; group
  have key : τ⁻¹ * n₂ * τ * y₁ * (τ⁻¹ * n₂ * τ)⁻¹ * y₁⁻¹ * (y₁ * y₂) =
      τ⁻¹ * ((n₂ * n₁) * τ * (n₂ * n₁)⁻¹) := by
    rw [e1, e2]; group
  have hk : τ * (τ⁻¹ * ((n₂ * n₁) * τ * (n₂ * n₁)⁻¹)) ∈ nOrbit N τ :=
    ⟨n₂ * n₁, N.mul_mem hn₂ hn₁, by group⟩
  rcases eq_one_or_eq_of_mem_zpowers ht (hcomm _ ha _ hy₁N) with hc | hc
  · left; rw [hc, one_mul] at key; rwa [key]
  · right; rw [hc] at key; rwa [key]

theorem commute_of_mul_mem_nOrbit₂ (ht : t * t = 1) (hτ : τ * τ = 1) (htτ : Commute t τ)
    (htc : ∀ n ∈ N, Commute n t) (hcomm : ∀ n ∈ N, ∀ m ∈ N, n * m * n⁻¹ * m⁻¹ ∈ zpowers t)
    (hsq : ∀ n ∈ N, n * n ∈ zpowers t) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N)
    (hnc : ∀ n ∈ N, n * τ * n⁻¹ ≠ τ * t) {y₁ y₂ : M} (hy₁ : τ * y₁ ∈ nOrbit N τ)
    (hy₂ : τ * y₂ ∈ nOrbit N τ) : Commute y₁ y₂ := by
  have sq := fun {y : M} (hy : τ * y ∈ nOrbit N τ) =>
    mul_self_eq_one_of_mul_mem_nOrbit ht hτ htτ hsq hτN hnc hy
  have h12 : y₁ * y₂ * (y₁ * y₂) = 1 := by
    rcases mul_mem_nOrbit_or ht hτ hcomm hτN hy₁ hy₂ with h | h
    · exact sq h
    · have hc : Commute (y₁ * y₂) t := htc _ (N.mul_mem (mem_of_mul_mem_nOrbit hτ hτN hy₁)
        (mem_of_mul_mem_nOrbit hτ hτN hy₂))
      calc y₁ * y₂ * (y₁ * y₂) = (t * t) * (y₁ * y₂ * (y₁ * y₂)) := by rw [ht, one_mul]
        _ = t * (t * (y₁ * y₂)) * (y₁ * y₂) := by group
        _ = t * ((y₁ * y₂) * t) * (y₁ * y₂) := by rw [hc.eq]
        _ = t * (y₁ * y₂) * (t * (y₁ * y₂)) := by group
        _ = 1 := sq h
  have := inv_eq_of_mul_eq_one_right h12
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (sq hy₁),
    inv_eq_of_mul_eq_one_right (sq hy₂)] at this
  exact this.symm

theorem not_mul_mem_nOrbit_of_conj
    (htri : ∀ ρ₁ ∈ nOrbit N τ, ∀ ρ₂ ∈ nOrbit N τ, Commute τ ρ₁ → Commute τ ρ₂ →
      Commute ρ₁ ρ₂ → ρ₁ ≠ τ → ρ₂ ≠ τ → ρ₁ ≠ ρ₂ → τ * ρ₁ * ρ₂ ∉ nOrbit N τ)
    {c σ ρ₁ ρ₂ : M} (hc : c ∈ N) (hσ : c * σ * c⁻¹ = τ) (hρ₁ : ρ₁ ∈ nOrbit N τ)
    (hρ₂ : ρ₂ ∈ nOrbit N τ) (h₁ : Commute σ ρ₁) (h₂ : Commute σ ρ₂) (h₁₂ : Commute ρ₁ ρ₂)
    (n₁ : ρ₁ ≠ σ) (n₂ : ρ₂ ≠ σ) (n₁₂ : ρ₁ ≠ ρ₂) : σ * ρ₁ * ρ₂ ∉ nOrbit N τ := by
  intro h
  have e : τ * (c * ρ₁ * c⁻¹) * (c * ρ₂ * c⁻¹) = c * (σ * ρ₁ * ρ₂) * c⁻¹ := by
    rw [← hσ]; group
  refine htri _ (conj_mem_nOrbit hc hρ₁) _ (conj_mem_nOrbit hc hρ₂)
    (hσ ▸ commute_conj_conj c h₁) (hσ ▸ commute_conj_conj c h₂) (commute_conj_conj c h₁₂)
    (hσ ▸ conj_ne_conj c n₁) (hσ ▸ conj_ne_conj c n₂) (conj_ne_conj c n₁₂) ?_
  rw [e]
  exact conj_mem_nOrbit hc h

end Lambda

theorem ncard_le_four {α : Type*} (p q r s : α) : ({p, q, r, s} : Set α).ncard ≤ 4 :=
  calc ({p, q, r, s} : Set α).ncard ≤ ({q, r, s} : Set α).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ (({r, s} : Set α).ncard + 1) + 1 := by gcongr; exact Set.ncard_insert_le _ _
    _ ≤ ((({s} : Set α).ncard + 1) + 1) + 1 := by gcongr; exact Set.ncard_insert_le _ _
    _ = 4 := by rw [Set.ncard_singleton]

theorem nat_card_nOrbit (N : Subgroup M) (τ : M) :
    Nat.card (nOrbit N τ) = (centralizer {τ}).relIndex N := by
  classical
  rw [Subgroup.relIndex, Subgroup.index]
  have key : ∀ a b : N, (a : M) * τ * (a : M)⁻¹ = (b : M) * τ * (b : M)⁻¹ ↔
      a⁻¹ * b ∈ (centralizer {τ}).subgroupOf N := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro h
      calc (a : M)⁻¹ * b * τ = (a : M)⁻¹ * ((b : M) * τ * (b : M)⁻¹) * b := by group
        _ = (a : M)⁻¹ * ((a : M) * τ * (a : M)⁻¹) * b := by rw [h]
        _ = τ * ((a : M)⁻¹ * b) := by group
    · intro h
      calc (a : M) * τ * (a : M)⁻¹ = a * (τ * ((a : M)⁻¹ * b)) * (b : M)⁻¹ := by group
        _ = a * ((a : M)⁻¹ * b * τ) * (b : M)⁻¹ := by rw [h]
        _ = (b : M) * τ * (b : M)⁻¹ := by group
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun q => Quotient.liftOn' q
    (fun n : N => (⟨(n : M) * τ * (n : M)⁻¹, n, n.2, rfl⟩ : nOrbit N τ))
    fun a b hab => Subtype.ext ((key a b).mpr (QuotientGroup.leftRel_apply.mp hab))) ⟨?_, ?_⟩)
  · intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with | H a => ?_
    induction q₂ using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.mpr ((key a b).mp (congrArg Subtype.val h))
  · rintro ⟨x, n, hn, rfl⟩
    exact ⟨QuotientGroup.mk ⟨n, hn⟩, rfl⟩

theorem false_of_lambda {t τ : M} {N : Subgroup M} (ht : t * t = 1) (hτ : τ * τ = 1)
    (htτ : Commute t τ) (htc : ∀ n ∈ N, Commute n t)
    (hcomm : ∀ n ∈ N, ∀ m ∈ N, n * m * n⁻¹ * m⁻¹ ∈ zpowers t)
    (hsq : ∀ n ∈ N, n * n ∈ zpowers t) (hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N)
    (hnc : ∀ n ∈ N, n * τ * n⁻¹ ≠ τ * t)
    (htri : ∀ ρ₁ ∈ nOrbit N τ, ∀ ρ₂ ∈ nOrbit N τ, Commute τ ρ₁ → Commute τ ρ₂ →
      Commute ρ₁ ρ₂ → ρ₁ ≠ τ → ρ₂ ≠ τ → ρ₁ ≠ ρ₂ → τ * ρ₁ * ρ₂ ∉ nOrbit N τ)
    (hcard : 4 < Nat.card (nOrbit N τ)) : False := by
  have sq := fun {y : M} (hy : τ * y ∈ nOrbit N τ) =>
    mul_self_eq_one_of_mul_mem_nOrbit ht hτ htτ hsq hτN hnc hy
  have cτ := fun {y : M} (hy : τ * y ∈ nOrbit N τ) => commute_of_mul_mem_nOrbit hτ hy (sq hy)
  have c₂ := fun {y₁ y₂ : M} (hy₁ : τ * y₁ ∈ nOrbit N τ) (hy₂ : τ * y₂ ∈ nOrbit N τ) =>
    commute_of_mul_mem_nOrbit₂ ht hτ htτ htc hcomm hsq hτN hnc hy₁ hy₂
  have cl := fun {y₁ y₂ : M} (hy₁ : τ * y₁ ∈ nOrbit N τ) (hy₂ : τ * y₂ ∈ nOrbit N τ) =>
    mul_mem_nOrbit_or ht hτ hcomm hτN hy₁ hy₂
  have mN := fun {y : M} (hy : τ * y ∈ nOrbit N τ) => mem_of_mul_mem_nOrbit hτ hτN hy
  have tri : ∀ {y₀ y₁ y₂ : M}, τ * y₀ ∈ nOrbit N τ → τ * y₁ ∈ nOrbit N τ →
      τ * y₂ ∈ nOrbit N τ → y₁ ≠ y₀ → y₂ ≠ y₀ → y₁ ≠ y₂ → τ * (y₀ * y₁ * y₂) ∉ nOrbit N τ := by
    intro y₀ y₁ y₂ h₀ h₁ h₂ n₁ n₂ n₁₂ h
    obtain ⟨n₀, hn₀, e₀⟩ := id h₀
    have hσ : n₀⁻¹ * (τ * y₀) * n₀⁻¹⁻¹ = τ := by rw [← e₀]; group
    have key : ∀ {a b : M}, τ * a ∈ nOrbit N τ → τ * b ∈ nOrbit N τ →
        Commute (τ * a) (τ * b) := fun ha hb =>
      ((Commute.refl τ).mul_right (cτ hb)).mul_left ((cτ ha).symm.mul_right (c₂ ha hb))
    have a0 := (cτ h₀).eq
    have a1 := (cτ h₁).eq
    have e : τ * y₀ * (τ * y₁) * (τ * y₂) = τ * (y₀ * y₁ * y₂) :=
      calc τ * y₀ * (τ * y₁) * (τ * y₂) = y₀ * (τ * τ) * y₁ * τ * y₂ := by rw [a0]; group
        _ = y₀ * (y₁ * τ) * y₂ := by rw [hτ]; group
        _ = y₀ * (τ * y₁) * y₂ := by rw [← a1]
        _ = (y₀ * τ) * y₁ * y₂ := by group
        _ = τ * (y₀ * y₁ * y₂) := by rw [← a0]; group
    refine not_mul_mem_nOrbit_of_conj htri (N.inv_mem hn₀) hσ h₁ h₂ (key h₀ h₁) (key h₀ h₂)
      (key h₁ h₂) (fun e => n₁ (mul_left_cancel e)) (fun e => n₂ (mul_left_cancel e))
      (fun e => n₁₂ (mul_left_cancel e)) ?_
    rw [e]
    exact h
  have h1 : τ * 1 ∈ nOrbit N τ := by rw [mul_one]; exact self_mem_nOrbit N τ
  have hsmall : ∀ p q r s : M,
      (∀ y, τ * y ∈ nOrbit N τ → y = p ∨ y = q ∨ y = r ∨ y = s) → False := by
    intro p q r s h
    have hsub : nOrbit N τ ⊆ {τ * p, τ * q, τ * r, τ * s} := by
      intro x hx
      have hxx : x = τ * (τ * x) := by rw [← mul_assoc, hτ, one_mul]
      have hx' : τ * (τ * x) ∈ nOrbit N τ := hxx ▸ hx
      rcases h _ hx' with e | e | e | e <;> rw [hxx, e] <;> simp
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h4 := ncard_le_four (τ * p) (τ * q) (τ * r) (τ * s)
    rw [Nat.card_coe_set_eq] at hcard
    omega
  obtain ⟨a, ha, ha1⟩ : ∃ a, τ * a ∈ nOrbit N τ ∧ a ≠ 1 := by
    by_contra hne
    push Not at hne
    exact hsmall 1 1 1 1 fun y hy => Or.inl (hne y hy)
  obtain ⟨b, hb, hb1, hba⟩ : ∃ b, τ * b ∈ nOrbit N τ ∧ b ≠ 1 ∧ b ≠ a := by
    by_contra hne
    push Not at hne
    refine hsmall 1 a a a fun y hy => ?_
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (Or.inl (hne y hy hy1))
  have hab : τ * (t * (a * b)) ∈ nOrbit N τ := by
    rcases cl ha hb with h | h
    · exact (tri h1 ha hb ha1 hb1 (Ne.symm hba) (by rwa [one_mul])).elim
    · exact h
  obtain ⟨c, hc, hc1, hca, hcb, hcab⟩ :
      ∃ c, τ * c ∈ nOrbit N τ ∧ c ≠ 1 ∧ c ≠ a ∧ c ≠ b ∧ c ≠ t * (a * b) := by
    by_contra hne
    push Not at hne
    refine hsmall 1 a b (t * (a * b)) fun y hy => ?_
    by_cases h₁ : y = 1
    · exact Or.inl h₁
    by_cases h₂ : y = a
    · exact Or.inr (Or.inl h₂)
    by_cases h₃ : y = b
    · exact Or.inr (Or.inr (Or.inl h₃))
    exact Or.inr (Or.inr (Or.inr (hne y hy h₁ h₂ h₃)))
  have hbc : τ * (t * (b * c)) ∈ nOrbit N τ := by
    rcases cl hb hc with h | h
    · exact (tri h1 hb hc hb1 hc1 (Ne.symm hcb) (by rwa [one_mul])).elim
    · exact h
  have hbt : Commute b t := htc b (mN hb)
  have hb2 : b * b = 1 := sq hb
  have n₁ : t * (b * c) ≠ a := by
    intro e
    apply hcab
    calc c = (t * t) * (b * b) * c := by rw [ht, hb2, one_mul, one_mul]
      _ = t * (t * b) * b * c := by group
      _ = t * (b * t) * b * c := by rw [← hbt.eq]
      _ = t * b * (t * (b * c)) := by group
      _ = t * (a * b) := by rw [e, mul_assoc, (c₂ ha hb).eq]
  have n₁₂ : t * (b * c) ≠ 1 := by
    intro e
    have e' : b * c = t := by
      have := eq_inv_of_mul_eq_one_right e
      rwa [inv_eq_of_mul_eq_one_right ht] at this
    have hcbt : c = b * t := by rw [← e', ← mul_assoc, hb2, one_mul]
    exact mul_t_not_mem_nOrbit ht htc hnc hb (hcbt ▸ hc)
  have habc : τ * (a * b * c) ∉ nOrbit N τ := tri ha hb hc hba hca (Ne.symm hcb)
  have htabc : τ * (a * (t * (b * c)) * 1) ∉ nOrbit N τ :=
    tri ha hbc h1 n₁ (Ne.symm ha1) n₁₂
  rcases cl hab hc with h | h
  · apply htabc
    have e : a * (t * (b * c)) * 1 = t * (a * b) * c := by
      rw [mul_one, ← mul_assoc, (htc a (mN ha)).eq]; group
    rwa [e]
  · apply habc
    have e : t * (t * (a * b) * c) = a * b * c := by
      rw [show t * (t * (a * b) * c) = (t * t) * (a * b * c) by group, ht, one_mul]
    rwa [e] at h

end CFSG.LargeExtraspecial.S9
