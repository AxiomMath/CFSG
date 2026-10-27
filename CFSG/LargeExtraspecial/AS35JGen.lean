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

namespace CFSG.LargeExtraspecial.AS35J

open Subgroup

variable {G : Type*} [Group G]

theorem map_conj_eq_self_of_mem {H : Subgroup G} {k : G} (hk : k ∈ H) :
    H.map (MulAut.conj k).toMonoidHom = H := by
  refine le_antisymm ?_ fun x hx => ⟨k⁻¹ * x * k, H.mul_mem (H.mul_mem (H.inv_mem hk) hx) hk, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact H.mul_mem (H.mul_mem hk hy) (H.inv_mem hk)
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem commute_of_weaklyClosed [Finite G] {T R : Subgroup G} (hT : IsPGroup 2 T) (hRT : R ≤ T)
    {a : G} (haR : ∀ r ∈ R, r * a = a * r)
    (hwc : ∀ g ∈ T, (∀ r ∈ R, r * (g * a * g⁻¹) = g * a * g⁻¹ * r) → g * a * g⁻¹ = a) :
    ∀ g ∈ T, g * a = a * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Set G := {x | ∃ g ∈ T, g * a * g⁻¹ = x} with hC
  have hmemC : ∀ {k : G}, k ∈ T → ∀ x ∈ C, k * x * k⁻¹ ∈ C := by
    rintro k hk _ ⟨g, hg, rfl⟩
    exact ⟨k * g, T.mul_mem hk hg, by group⟩
  have haC : a ∈ C := ⟨1, T.one_mem, by group⟩
  let act : ∀ K : Subgroup G, K ≤ T → MulAction K C := fun K hK =>
    { smul := fun k x => ⟨k * x * (k : G)⁻¹, hmemC (hK k.2) x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change (1 : G) * x * 1⁻¹ = x
        group)
      mul_smul := fun k l x => Subtype.ext (by
        change (k * l : G) * x * (k * l : G)⁻¹ = k * (l * x * (l : G)⁻¹) * (k : G)⁻¹
        group) }
  have hRfix : Nat.card (@MulAction.fixedPoints R C _ (act R hRT)) = 1 := by
    let _ := act R hRT
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨a, haC⟩, fun r => Subtype.ext ?_⟩, ?_⟩
    · change (r : G) * a * (r : G)⁻¹ = a
      rw [haR r r.2]
      group
    · rintro ⟨⟨x, g, hg, rfl⟩, hx⟩
      apply Subtype.ext
      apply Subtype.ext
      change g * a * g⁻¹ = a
      refine hwc g hg fun r hr => ?_
      have h1 := congrArg Subtype.val (hx ⟨r, hr⟩)
      change r * (g * a * g⁻¹) * r⁻¹ = g * a * g⁻¹ at h1
      calc r * (g * a * g⁻¹) = r * (g * a * g⁻¹) * r⁻¹ * r := by group
        _ = g * a * g⁻¹ * r := by rw [h1]
  have hodd : Nat.card C % 2 = 1 := by
    let _ := act R hRT
    have h := (hT.to_le hRT).card_modEq_card_fixedPoints C
    rw [hRfix] at h
    exact h
  have hTfix : (@MulAction.fixedPoints T C _ (act T le_rfl)).Nonempty := by
    let _ := act T le_rfl
    have h := hT.card_modEq_card_fixedPoints C
    unfold Nat.ModEq at h
    rw [hodd] at h
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at h
    simp at h
  obtain ⟨⟨x, g, hg, rfl⟩, hx⟩ := hTfix
  have hfix : ∀ k ∈ T, k * (g * a * g⁻¹) * k⁻¹ = g * a * g⁻¹ := fun k hk =>
    congrArg Subtype.val (hx ⟨k, hk⟩)
  have hga : g * a * g⁻¹ = a := by
    have h1 := hfix g⁻¹ (T.inv_mem hg)
    rw [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at h1
    exact h1.symm
  intro k hk
  have h1 := hfix k hk
  rw [hga] at h1
  calc k * a = k * a * k⁻¹ * k := by group
    _ = a * k := by rw [h1]

theorem mul_mem_pair {e u v : G} (he : e * e = 1) (hu : u = 1 ∨ u = e) (hv : v = 1 ∨ v = e) :
    u * v = 1 ∨ u * v = e := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · left; group
  · right; group
  · right; group
  · left; exact he

theorem inv_mem_pair {e u : G} (he : e * e = 1) (hu : u = 1 ∨ u = e) : u⁻¹ = 1 ∨ u⁻¹ = e := by
  rcases hu with rfl | rfl
  · left; group
  · right; exact inv_eq_of_mul_eq_one_right he

theorem conj_eq_of_mem_pair {e u c : G} (hc : c * e = e * c) (hu : u = 1 ∨ u = e) :
    c * u * c⁻¹ = u := by
  rcases hu with rfl | rfl
  · group
  · rw [hc]; group

theorem mul_self_mem_pair_of_mem_closure {A : Set G} {e : G} (he : e * e = 1)
    (hA : ∀ a ∈ A, a * a = 1) (hAe : ∀ a ∈ A, a * e = e * a)
    (hAA : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = e) :
    ∀ x ∈ closure A, x * x = 1 ∨ x * x = e := by
  have hcent : ∀ x ∈ closure A, x * e = e * x := by
    have hle : closure A ≤ centralizer ({e} : Set G) := by
      rw [closure_le]
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (hAe a ha)
    exact fun x hx => mem_centralizer_singleton_iff.mp (hle hx)
  have h1 : ∀ x ∈ closure A, ∀ b ∈ A, x * b * x⁻¹ * b⁻¹ = 1 ∨ x * b * x⁻¹ * b⁻¹ = e := by
    intro x hx
    induction hx using closure_induction with
    | mem a ha => exact fun b hb => hAA a ha b hb
    | one => exact fun b _ => Or.inl (by group)
    | mul x y hx hy ihx ihy =>
      intro b hb
      rw [show x * y * b * (x * y)⁻¹ * b⁻¹ =
        x * (y * b * y⁻¹ * b⁻¹) * x⁻¹ * (x * b * x⁻¹ * b⁻¹) by group,
        conj_eq_of_mem_pair (hcent x hx) (ihy b hb)]
      exact mul_mem_pair he (ihy b hb) (ihx b hb)
    | inv x hx ihx =>
      intro b hb
      rw [show x⁻¹ * b * x⁻¹⁻¹ * b⁻¹ = x⁻¹ * (x * b * x⁻¹ * b⁻¹)⁻¹ * x⁻¹⁻¹ by group,
        conj_eq_of_mem_pair (hcent _ (inv_mem hx)) (inv_mem_pair he (ihx b hb))]
      exact inv_mem_pair he (ihx b hb)
  have h2 : ∀ x ∈ closure A, ∀ y ∈ closure A,
      x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = e := by
    intro x hx y hy
    induction hy using closure_induction with
    | mem b hb => exact h1 x hx b hb
    | one => exact Or.inl (by group)
    | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
      rw [show x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
        (x * y₁ * x⁻¹ * y₁⁻¹) * (y₁ * (x * y₂ * x⁻¹ * y₂⁻¹) * y₁⁻¹) by group,
        conj_eq_of_mem_pair (hcent y₁ hy₁) ih₂]
      exact mul_mem_pair he ih₁ ih₂
    | inv y hy ih =>
      rw [show x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ by group,
        conj_eq_of_mem_pair (hcent _ (inv_mem hy)) (inv_mem_pair he ih)]
      exact inv_mem_pair he ih
  intro x hx
  induction hx using closure_induction with
  | mem a ha => exact Or.inl (hA a ha)
  | one => exact Or.inl (by group)
  | mul x y hx hy ihx ihy =>
    have hc := h2 y hy x hx
    rw [show x * y * (x * y) = x * (y * x * y⁻¹ * x⁻¹) * x⁻¹ * (x * x) * (y * y) by group,
      conj_eq_of_mem_pair (hcent x hx) hc]
    exact mul_mem_pair he (mul_mem_pair he hc ihx) ihy
  | inv x hx ihx =>
    rw [show x⁻¹ * x⁻¹ = (x * x)⁻¹ by group]
    exact inv_mem_pair he ihx

theorem isPGroup_closure_of_comm {A : Set G} {e : G} (he : e * e = 1)
    (hA : ∀ a ∈ A, a * a = 1) (hAe : ∀ a ∈ A, a * e = e * a)
    (hAA : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = e) :
    IsPGroup 2 (closure A) := by
  intro x
  refine ⟨2, Subtype.ext ?_⟩
  have h := mul_self_mem_pair_of_mem_closure he hA hAe hAA x x.2
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one,
    show (x : G) ^ 2 ^ 2 = (x * x : G) * (x * x : G) by norm_num [pow_succ, mul_assoc]]
  rcases h with h | h <;> rw [h]
  · group
  · exact he

end CFSG.LargeExtraspecial.AS35J
