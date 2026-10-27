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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup
open scoped commutatorElement

theorem commutatorElement_mul_central_left {X : Type*} [Group X] {z : X} (hz : z ∈ center X)
    (p q : X) : ⁅p * z, q⁆ = ⁅p, q⁆ := by
  have h1 : ∀ g : X, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  have h2 : q * z⁻¹ = z⁻¹ * q := by
    have := h1 q
    calc q * z⁻¹ = z⁻¹ * (z * q) * z⁻¹ := by group
      _ = z⁻¹ * (q * z) * z⁻¹ := by rw [this]
      _ = z⁻¹ * q := by group
  simp only [commutatorElement_def, mul_inv_rev]
  calc p * z * q * (z⁻¹ * p⁻¹) * q⁻¹ = p * (z * q) * (z⁻¹ * p⁻¹) * q⁻¹ := by group
    _ = p * (q * z) * (z⁻¹ * p⁻¹) * q⁻¹ := by rw [h1 q]
    _ = p * q * (z * z⁻¹) * p⁻¹ * q⁻¹ := by group
    _ = p * q * p⁻¹ * q⁻¹ := by group

theorem commutatorElement_mul_central_right {X : Type*} [Group X] {z : X} (hz : z ∈ center X)
    (p q : X) : ⁅p, q * z⁆ = ⁅p, q⁆ := by
  rw [← commutatorElement_inv (q * z) p, commutatorElement_mul_central_left hz q p,
    commutatorElement_inv]

theorem commutator_le_of_central_cosets {X : Type*} [Group X] (P Q : Subgroup X)
    (hQ : ∀ q ∈ Q, ∃ p ∈ P, p⁻¹ * q ∈ center X) : ⁅Q, Q⁆ ≤ ⁅P, P⁆ := by
  rw [Subgroup.commutator_le]
  intro q₁ h₁ q₂ h₂
  obtain ⟨p₁, hp₁, hz₁⟩ := hQ q₁ h₁
  obtain ⟨p₂, hp₂, hz₂⟩ := hQ q₂ h₂
  have e1 : q₁ = p₁ * (p₁⁻¹ * q₁) := by group
  have e2 : q₂ = p₂ * (p₂⁻¹ * q₂) := by group
  rw [e1, e2, commutatorElement_mul_central_left hz₁, commutatorElement_mul_central_right hz₂]
  exact Subgroup.commutator_mem_commutator hp₁ hp₂

theorem isPerfect_iff_commutator_eq {X : Type*} [Group X] (P : Subgroup X) :
    Group.IsPerfect ↥P ↔ ⁅P, P⁆ = P := by
  constructor
  · intro h
    rw [← Subgroup.map_subtype_commutator, h.commutator_eq_top, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro h
    refine ⟨?_⟩
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subtype_commutator, h, Subgroup.map_top, Subgroup.range_subtype]

theorem commutator_le_self' {X : Type*} [Group X] (P : Subgroup X) : ⁅P, P⁆ ≤ P := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  exact P.mul_mem (P.mul_mem (P.mul_mem hg hh) (P.inv_mem hg)) (P.inv_mem hh)

theorem commutator_comap_le_centralizer {X Y : Type*} [Group X] [Group Y] (ρ : X →* Y)
    (hker : ρ.ker ≤ center X) (a : X) :
    ⁅(centralizer ({ρ a} : Set Y)).comap ρ, (centralizer ({ρ a} : Set Y)).comap ρ⁆ ≤
      centralizer ({a} : Set X) := by
  rw [Subgroup.commutator_le]
  have key : ∀ g ∈ (centralizer ({ρ a} : Set Y)).comap ρ, ∃ v ∈ center X, g⁻¹ * a * g = v * a := by
    intro g hg
    have hg' : ρ g * ρ a = ρ a * ρ g := Subgroup.mem_centralizer_singleton_iff.1 hg
    refine ⟨g⁻¹ * a * g * a⁻¹, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc (ρ g)⁻¹ * ρ a * ρ g * (ρ a)⁻¹ = (ρ g)⁻¹ * (ρ a * ρ g) * (ρ a)⁻¹ := by group
      _ = (ρ g)⁻¹ * (ρ g * ρ a) * (ρ a)⁻¹ := by rw [hg']
      _ = 1 := by group
  intro g hg h hh
  obtain ⟨vg, hvg, eg⟩ := key g hg
  obtain ⟨vh, hvh, eh⟩ := key h hh
  have hcg : ∀ x : X, x * vg = vg * x := fun x => Subgroup.mem_center_iff.1 hvg x
  have hch : ∀ x : X, x * vh = vh * x := fun x => Subgroup.mem_center_iff.1 hvh x
  have E : (g * h)⁻¹ * a * (g * h) = (h * g)⁻¹ * a * (h * g) := by
    calc (g * h)⁻¹ * a * (g * h) = h⁻¹ * (g⁻¹ * a * g) * h := by group
      _ = h⁻¹ * (vg * a) * h := by rw [eg]
      _ = (h⁻¹ * vg) * (a * h) := by group
      _ = (vg * h⁻¹) * (a * h) := by rw [hcg h⁻¹]
      _ = vg * (h⁻¹ * a * h) := by group
      _ = vg * (vh * a) := by rw [eh]
      _ = (vg * vh) * a := by group
      _ = (vh * vg) * a := by rw [hcg vh]
      _ = vh * (vg * a) := by group
      _ = vh * (g⁻¹ * a * g) := by rw [eg]
      _ = (h * g)⁻¹ * a * (h * g) := by
        calc vh * (g⁻¹ * a * g) = g⁻¹ * (vh * a) * g := by
              have := hch g⁻¹
              calc vh * (g⁻¹ * a * g) = (vh * g⁻¹) * a * g := by group
                _ = (g⁻¹ * vh) * a * g := by rw [← this]
                _ = g⁻¹ * (vh * a) * g := by group
          _ = g⁻¹ * (h⁻¹ * a * h) * g := by rw [eh]
          _ = (h * g)⁻¹ * a * (h * g) := by group
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hY : (h * g)⁻¹ * a = (g * h)⁻¹ * a * (g * h) * (h * g)⁻¹ := by
    calc (h * g)⁻¹ * a = ((h * g)⁻¹ * a * (h * g)) * (h * g)⁻¹ := by group
      _ = _ := by rw [← E]
  calc ⁅g, h⁆ * a = (g * h) * ((h * g)⁻¹ * a) := by group
    _ = (g * h) * ((g * h)⁻¹ * a * (g * h) * (h * g)⁻¹) := by rw [hY]
    _ = a * ⁅g, h⁆ := by group

theorem perfect_core_of_cover {X Y : Type*} [Group X] [Group Y] (ρ : X →* Y)
    (hker : ρ.ker ≤ center X) (a : X) (D : Subgroup Y)
    (hDC : D ≤ ((centralizer ({ρ a} : Set Y)).comap ρ).map ρ)
    (hcomm : ⁅((centralizer ({ρ a} : Set Y)).comap ρ).map ρ,
      ((centralizer ({ρ a} : Set Y)).comap ρ).map ρ⁆ ≤ D)
    (hperf : ⁅D, D⁆ = D)
    (hK : ∀ P : Subgroup X, P ≤ centralizer ({a} : Set X) → ⁅P, P⁆ = P → P ⊓ ρ.ker = ⊥) :
    ∃ P : Subgroup X, P ≤ centralizer ({a} : Set X) ∧ ⁅P, P⁆ = P ∧ P.map ρ = D ∧
      Nonempty (↥P ≃* ↥D) ∧
      ∀ P' : Subgroup X, P' ≤ centralizer ({a} : Set X) → ⁅P', P'⁆ = P' → P' ≤ P := by
  set Pre : Subgroup X := (centralizer ({ρ a} : Set Y)).comap ρ with hPre
  set Q : Subgroup X := ⁅Pre, Pre⁆ with hQ
  have hQC : Q ≤ centralizer ({a} : Set X) := commutator_comap_le_centralizer ρ hker a
  have hQmap : Q.map ρ = D := by
    refine le_antisymm ?_ ?_
    · rw [hQ, Subgroup.map_commutator]; exact hcomm
    · calc D = ⁅D, D⁆ := hperf.symm
        _ ≤ ⁅Pre.map ρ, Pre.map ρ⁆ := Subgroup.commutator_mono hDC hDC
        _ = Q.map ρ := by rw [hQ, Subgroup.map_commutator]
  set P : Subgroup X := ⁅Q, Q⁆ with hP
  have hPmap : P.map ρ = D := by
    rw [hP, Subgroup.map_commutator, hQmap, hperf]
  have hcos : ∀ {S : Subgroup X}, (∀ x ∈ S, ρ x ∈ D) → ∀ x ∈ S, ∃ p ∈ P, p⁻¹ * x ∈ center X := by
    intro S hS x hx
    have : ρ x ∈ P.map ρ := by rw [hPmap]; exact hS x hx
    obtain ⟨p, hp, hpx⟩ := this
    refine ⟨p, hp, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, inv_mul_cancel]
  have hperfP : ⁅P, P⁆ = P := by
    refine le_antisymm (commutator_le_self' P) ?_
    exact commutator_le_of_central_cosets P Q
      (fun q hq => hcos (S := Q) (fun x hx => hQmap ▸ Subgroup.mem_map_of_mem ρ hx) q hq)
  have hPC : P ≤ centralizer ({a} : Set X) := (commutator_le_self' Q).trans hQC
  have hPK := hK P hPC hperfP
  refine ⟨P, hPC, hperfP, hPmap, ?_, ?_⟩
  · have hinj : Function.Injective (ρ.subgroupMap P) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : ρ (x : X) = 1 := congrArg Subtype.val hx
      have h2 : (x : X) ∈ P ⊓ ρ.ker := ⟨x.2, h1⟩
      rw [hPK, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    have hbij : Function.Bijective (ρ.subgroupMap P) := ⟨hinj, ρ.subgroupMap_surjective P⟩
    exact ⟨(MulEquiv.ofBijective _ hbij).trans (MulEquiv.subgroupCongr hPmap)⟩
  · intro P' hP'C hP'perf
    have hP'Pre : P' ≤ Pre := by
      intro g hg
      have : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.1 (hP'C hg)
      show ρ g ∈ centralizer ({ρ a} : Set Y)
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, this]
    have hP'D : ∀ x ∈ P', ρ x ∈ D := by
      intro x hx
      have h1 : P'.map ρ ≤ D := by
        calc P'.map ρ = (⁅P', P'⁆).map ρ := by rw [hP'perf]
          _ = ⁅P'.map ρ, P'.map ρ⁆ := Subgroup.map_commutator _ _ _
          _ ≤ ⁅Pre.map ρ, Pre.map ρ⁆ :=
              Subgroup.commutator_mono (Subgroup.map_mono hP'Pre) (Subgroup.map_mono hP'Pre)
          _ ≤ D := hcomm
      exact h1 (Subgroup.mem_map_of_mem ρ hx)
    calc P' = ⁅P', P'⁆ := hP'perf.symm
      _ ≤ ⁅P, P⁆ := commutator_le_of_central_cosets P P' (hcos hP'D)
      _ ≤ P := commutator_le_self' P

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
