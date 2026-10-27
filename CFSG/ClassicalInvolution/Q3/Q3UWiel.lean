module

import CFSG.Walter.AStar.Subnormal
import CFSG.ClassicalInvolution.Q3.Q3MOdd
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
public import Mathlib.GroupTheory.IsSubnormal
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

namespace CFSG.ClassicalInvolution.Q3

open scoped Pointwise

theorem inf_le_normalizer_inf {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (W L : Subgroup G)
    [W.Normal] (P : Sylow p G) :
    (P : Subgroup G) ⊓ L ≤ Subgroup.normalizer (((P : Subgroup G) ⊓ W : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have haP : a ∈ (P : Subgroup G) := ha.1
  have haW : ∀ w : G, w ∈ W ↔ a * w * a⁻¹ ∈ W := fun w => by
    constructor
    · intro hw
      exact (inferInstance : W.Normal).conj_mem w hw a
    · intro hw
      have := (inferInstance : W.Normal).conj_mem _ hw a⁻¹
      simpa [mul_assoc] using this
  have haP' : ∀ x : G, x ∈ (P : Subgroup G) ↔ a * x * a⁻¹ ∈ (P : Subgroup G) := fun x => by
    constructor
    · intro hx
      exact (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem haP hx)
        ((P : Subgroup G).inv_mem haP)
    · intro hx
      have := (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem
        ((P : Subgroup G).inv_mem haP) hx) haP
      simpa [mul_assoc] using this
  simp only [Subgroup.mem_inf]
  rw [haP' y, haW y]

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
theorem mem_sylow_smul_iff (P : Sylow p G) (g x : G) :
    x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  have h : ((g • P : Sylow p G) : Subgroup G) =
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    ext y
    simp [Subgroup.pointwise_smul_def]
  rw [h, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem card_sylow_inf_of_isSubnormal (P : Sylow p G) {H : Subgroup G} (hH : H.IsSubnormal) :
    Nat.card ↥((P : Subgroup G) ⊓ H) = p ^ (Nat.card H).factorization p := by
  obtain ⟨R, hR⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hH
  rw [← hR, Subgroup.card_map_of_injective H.subtype_injective]
  exact R.card_eq_multiplicity

theorem sylow_eq_sup_inf {W L : Subgroup G} [W.Normal] (hL : L.IsSubnormal) (hWL : W ⊔ L = ⊤)
    (P : Sylow p G) :
    (P : Subgroup G) = ((P : Subgroup G) ⊓ L) ⊔ ((P : Subgroup G) ⊓ W) := by
  set A : Subgroup G := (P : Subgroup G) ⊓ L with hA
  set B : Subgroup G := (P : Subgroup G) ⊓ W with hB
  have hWsub : W.IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
  have hAB : A ⊔ B ≤ (P : Subgroup G) := sup_le inf_le_left inf_le_left
  have hA' : Nat.card A = p ^ (Nat.card L).factorization p := card_sylow_inf_of_isSubnormal P hL
  have hB' : Nat.card B = p ^ (Nat.card W).factorization p :=
    card_sylow_inf_of_isSubnormal P hWsub
  have hAB1 : A ⊓ B = (P : Subgroup G) ⊓ (L ⊓ W) := by
    ext x
    simp only [hA, hB, Subgroup.mem_inf]
    tauto
  have hAB' : Nat.card ↥(A ⊓ B) = p ^ (Nat.card ↥(L ⊓ W)).factorization p := by
    rw [hAB1]
    exact card_sylow_inf_of_isSubnormal P (hL.inf hWsub)
  have hG : Nat.card G * Nat.card ↥(L ⊓ W) = Nat.card L * Nat.card W := by
    have h := M.card_sup_mul_card_inf_of_le_normalizer (A := L) (B := W)
      (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
    rwa [sup_comm, hWL, Subgroup.card_top] at h
  have hP : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card G).factorization p :=
    P.card_eq_multiplicity
  have hkey : Nat.card A * Nat.card B = Nat.card ↥(P : Subgroup G) * Nat.card ↥(A ⊓ B) := by
    rw [hA', hB', hAB', hP, ← pow_add, ← pow_add]
    congr 1
    have h1 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have h2 : Nat.card ↥(L ⊓ W) ≠ 0 := Nat.card_pos.ne'
    have h3 : Nat.card W ≠ 0 := Nat.card_pos.ne'
    have h4 : Nat.card L ≠ 0 := Nat.card_pos.ne'
    have := congrArg (fun n => n.factorization p) hG
    simp only [Nat.factorization_mul h1 h2, Nat.factorization_mul h4 h3, Finsupp.add_apply]
      at this
    omega
  have hnorm : A ≤ Subgroup.normalizer (B : Set G) := inf_le_normalizer_inf W L P
  have hsup := M.card_sup_mul_card_inf_of_le_normalizer hnorm
  have hpos : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
  have hcard : Nat.card ↥(A ⊔ B) = Nat.card ↥(P : Subgroup G) :=
    Nat.eq_of_mul_eq_mul_right hpos (hsup.trans hkey)
  exact (Subgroup.eq_of_le_of_card_ge hAB hcard.ge).symm

theorem exists_mul_of_sylow {W L : Subgroup G} [W.Normal] (hL : L.IsSubnormal)
    (hWL : W ⊔ L = ⊤) (P : Sylow p G) {x : G} (hx : x ∈ (P : Subgroup G)) :
    ∃ l ∈ (P : Subgroup G) ⊓ L, ∃ w ∈ (P : Subgroup G) ⊓ W, x = l * w := by
  have h := sylow_eq_sup_inf hL hWL P
  have hx' : x ∈ (((P : Subgroup G) ⊓ L) ⊔ ((P : Subgroup G) ⊓ W) : Subgroup G) := by
    rw [← h]
    exact hx
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right ((P : Subgroup G) ⊓ L)
    ((P : Subgroup G) ⊓ W) (inf_le_normalizer_inf W L P)
  have hmem : x ∈ (((P : Subgroup G) ⊓ L : Subgroup G) : Set G) *
      (((P : Subgroup G) ⊓ W : Subgroup G) : Set G) := by
    rw [← hset]
    exact hx'
  obtain ⟨l, hl, w, hw, rfl⟩ := hmem
  exact ⟨l, hl, w, hw, rfl⟩

theorem exists_commutator_eq {W L : Subgroup G} [W.Normal] (hL : L.IsSubnormal)
    (hWL : W ⊔ L = ⊤) (P : Sylow p G) {σ : G} (hσP : σ ∈ (P : Subgroup G)) (hσL : σ ∈ L)
    {ω : G} (hω : ω ∈ W) :
    ∃ l ∈ L ⊓ W, ∃ π ∈ (P : Subgroup G) ⊓ W,
      σ⁻¹ * ω⁻¹ * σ * ω = l * (ω⁻¹ * π * ω) := by
  set P' : Sylow p G := ω⁻¹ • P with hP'
  have hxP' : ω⁻¹ * σ * ω ∈ (P' : Subgroup G) := by
    rw [hP', mem_sylow_smul_iff, inv_inv, show ω * (ω⁻¹ * σ * ω) * ω⁻¹ = σ by group]
    exact hσP
  obtain ⟨ℓ, hℓ, π', hπ', hxe⟩ := exists_mul_of_sylow hL hWL P' hxP'
  have hπ'P : ω * π' * ω⁻¹ ∈ (P : Subgroup G) := by
    have h : π' ∈ ((ω⁻¹ • P : Sylow p G) : Subgroup G) := hπ'.1
    rw [mem_sylow_smul_iff, inv_inv] at h
    exact h
  have hπ'W : π' ∈ W := hπ'.2
  have hπW : ω * π' * ω⁻¹ ∈ W := (inferInstance : W.Normal).conj_mem π' hπ'W ω
  refine ⟨σ⁻¹ * ℓ, ⟨(L.mul_mem (L.inv_mem hσL) hℓ.2), ?_⟩, ω * π' * ω⁻¹, ⟨hπ'P, hπW⟩, ?_⟩
  ·
    have h1 : σ⁻¹ * ω⁻¹ * σ ∈ W := by
      have := (inferInstance : W.Normal).conj_mem ω⁻¹ (W.inv_mem hω) σ⁻¹
      simpa [mul_assoc] using this
    have h2 : σ⁻¹ * ℓ = (σ⁻¹ * ω⁻¹ * σ * ω) * π'⁻¹ := by
      have : ℓ = ω⁻¹ * σ * ω * π'⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        exact hxe.symm
      rw [this]
      group
    rw [h2]
    exact W.mul_mem (by simpa [mul_assoc] using W.mul_mem h1 hω) (W.inv_mem hπ'W)
  · have hπ' : ω⁻¹ * (ω * π' * ω⁻¹) * ω = π' := by group
    rw [hπ']
    have : σ⁻¹ * ω⁻¹ * σ * ω = σ⁻¹ * (ω⁻¹ * σ * ω) := by group
    rw [this, hxe]
    group

end CFSG.ClassicalInvolution.Q3
