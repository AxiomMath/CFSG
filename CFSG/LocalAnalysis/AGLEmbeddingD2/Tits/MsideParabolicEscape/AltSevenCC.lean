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
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.AltSeven

open Equiv

abbrev A7 := alternatingGroup (Fin 7)

@[expose] noncomputable def cc (x : A7) : ℕ := Nat.card (Subgroup.centralizer ({x} : Set A7))

theorem cc_eq_card_filter (x : A7) :
    cc x = (Finset.univ.filter (fun g : Perm (Fin 7) => g * (x : Perm (Fin 7)) = x * g ∧
      Perm.sign g = 1)).card := by
  classical
  unfold cc
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun g => ⟨(g.1 : Perm (Fin 7)), ?_, ?_⟩
      invFun := fun g => ⟨⟨g.1, ?_⟩, ?_⟩
      left_inv := fun g => by simp
      right_inv := fun g => by simp }
  · have := Subgroup.mem_centralizer_iff.mp g.2 x (Set.mem_singleton x)
    exact congrArg Subtype.val this.symm
  · exact (Perm.mem_alternatingGroup.mp g.1.2)
  · exact Perm.mem_alternatingGroup.mpr g.2.2
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Subtype.ext g.2.1.symm

@[expose] def a0 : A7 := ⟨c[0, 1, 2], by rw [Perm.mem_alternatingGroup]; decide⟩
@[expose] def b0 : A7 := ⟨c[3, 4, 5], by rw [Perm.mem_alternatingGroup]; decide⟩

theorem cc_a0 : cc a0 = 36 := by
  rw [cc_eq_card_filter]; decide +kernel

theorem cc_a0b0 : cc (a0 * b0) = 9 := by
  rw [cc_eq_card_filter]; decide +kernel

theorem cc_mulEquiv (β : A7 ≃* A7) (x : A7) : cc (β x) = cc x := by
  unfold cc
  refine Nat.card_congr
    { toFun := fun g => ⟨β.symm g.1, ?_⟩
      invFun := fun g => ⟨β g.1, ?_⟩
      left_inv := fun g => by simp
      right_inv := fun g => by simp }
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := Subgroup.mem_centralizer_iff.mp g.2 (β h) (Set.mem_singleton _)
    apply β.injective
    simpa using this
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := Subgroup.mem_centralizer_iff.mp g.2 x (Set.mem_singleton _)
    simpa using congrArg β this

theorem a0_b0_comm : a0 * b0 = b0 * a0 := by decide +kernel

theorem a0_pow : a0 ^ 3 = 1 := by decide +kernel
theorem b0_pow : b0 ^ 3 = 1 := by decide +kernel
theorem a0_ne : a0 ≠ 1 := by decide +kernel
theorem a0b0_ne : a0 * b0 ≠ 1 := by decide +kernel

theorem isPGroup_closure_a0_b0 : IsPGroup 3 (Subgroup.closure ({a0, b0} : Set A7)) := by
  have hcomm : ∀ x ∈ ({a0, b0} : Set A7), ∀ y ∈ ({a0, b0} : Set A7), x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact a0_b0_comm
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact a0_b0_comm.symm
    · rw [Set.mem_singleton_iff] at hx hy; subst hx; subst hy; rfl
  have h1 : Subgroup.closure ({a0, b0} : Set A7) ≤ Subgroup.centralizer ({a0, b0} : Set A7) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm y hy x hx)
  have h2 : Subgroup.closure ({a0, b0} : Set A7) ≤
      Subgroup.centralizer (Subgroup.centralizer ({a0, b0} : Set A7) : Set A7) :=
    Subgroup.closure_le_centralizer_centralizer _
  have key : ∀ g ∈ Subgroup.closure ({a0, b0} : Set A7), g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact a0_pow
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact b0_pow
    | one => simp
    | mul x y hx hy hx3 hy3 =>
      have hc : Commute x y := by
        have := Subgroup.mem_centralizer_iff.mp (h2 hy) x (h1 hx)
        exact this
      rw [hc.mul_pow, hx3, hy3, one_mul]
    | inv x hx hx3 => rw [inv_pow, hx3, inv_one]
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using key g.1 g.2

theorem card_A7 : Nat.card A7 = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem exists_cc_ne (E : Subgroup A7) (hE : Nat.card E = 9) :
    ∃ x ∈ E, ∃ y ∈ E, x ≠ 1 ∧ y ≠ 1 ∧ cc x ≠ cc y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card A7).factorization 3 = 2 := by
    rw [card_A7]
    have h : (2520:ℕ) = 3 ^ 2 * 280 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 280),
      Nat.Prime.factorization_pow Nat.prime_three]
    simp
  let S : Sylow 3 A7 := Sylow.ofCard E (by rw [hE, hfac]; norm_num)
  obtain ⟨Q, hQ⟩ := isPGroup_closure_a0_b0.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A7 Q S
  have hmem : ∀ z ∈ Subgroup.closure ({a0, b0} : Set A7), g * z * g⁻¹ ∈ E := by
    intro z hz
    have h1 : z ∈ (Q : Subgroup A7) := hQ hz
    have h2 : g * z * g⁻¹ ∈ ((g • Q : Sylow 3 A7) : Subgroup A7) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨z, h1, by simp [MulAut.conj_apply]⟩
    rw [hg] at h2
    have h3 : ((S : Sylow 3 A7) : Subgroup A7) = E := Sylow.coe_ofCard E _
    rwa [h3] at h2
  have ha : a0 ∈ Subgroup.closure ({a0, b0} : Set A7) := Subgroup.subset_closure (by simp)
  have hb : b0 ∈ Subgroup.closure ({a0, b0} : Set A7) := Subgroup.subset_closure (by simp)
  refine ⟨g * a0 * g⁻¹, hmem _ ha, g * (a0 * b0) * g⁻¹, hmem _ (Subgroup.mul_mem _ ha hb), ?_, ?_, ?_⟩
  · intro h
    apply a0_ne
    have := congrArg (fun t => g⁻¹ * t * g) h
    simpa [mul_assoc] using this
  · intro h
    apply a0b0_ne
    have := congrArg (fun t => g⁻¹ * t * g) h
    simpa [mul_assoc] using this
  · have e1 := cc_mulEquiv (MulAut.conj g) a0
    have e2 := cc_mulEquiv (MulAut.conj g) (a0 * b0)
    simp only [MulAut.conj_apply] at e1 e2
    rw [e1, e2, cc_a0, cc_a0b0]
    norm_num

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.AltSeven
