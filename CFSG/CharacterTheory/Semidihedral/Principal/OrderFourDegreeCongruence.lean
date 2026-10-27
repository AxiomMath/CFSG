module

public import CFSG.CharacterTheory.Semidihedral.FocalTransfer
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.Semidihedral.Principal

namespace OrderFourDegree

@[expose] noncomputable def fourthRoot : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

theorem fourthRoot_injective : Function.Injective fourthRoot := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [fourthRoot, Complex.ext_iff] at h ⊢ <;> norm_num at h

@[simp] theorem fourthRoot_zero : fourthRoot 0 = 1 := rfl

@[simp] theorem fourthRoot_one : fourthRoot 1 = -1 := rfl

@[simp] theorem fourthRoot_two : fourthRoot 2 = Complex.I := rfl

@[simp] theorem fourthRoot_three : fourthRoot 3 = -Complex.I := rfl

theorem exists_fourthRoot_eq {μ : ℂ} (h : μ ^ 4 = 1) : ∃ j, fourthRoot j = μ := by
  have h' : (μ - 1) * (μ + 1) * (μ - Complex.I) * (μ + Complex.I) = 0 := by
    linear_combination h + (1 - μ ^ 2) * Complex.I_sq
  rcases mul_eq_zero.mp h' with h₁ | h₁
  · rcases mul_eq_zero.mp h₁ with h₂ | h₂
    · rcases mul_eq_zero.mp h₂ with h₃ | h₃
      · exact ⟨0, by simp [fourthRoot]; linear_combination -h₃⟩
      · exact ⟨1, by simp [fourthRoot]; linear_combination -h₃⟩
    · exact ⟨2, by simp [fourthRoot]; linear_combination -h₂⟩
  · exact ⟨3, by simp [fourthRoot]; linear_combination -h₁⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem isInternal_eigenspaces (f : Module.End ℂ V) (hf : f ^ 4 = 1) :
    DirectSum.IsInternal (fun j : Fin 4 => f.eigenspace (fourthRoot j)) := by
  have hsemi : f.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := (Polynomial.X : Polynomial ℂ) ^ 4 - 1)
    · exact ((Polynomial.X_pow_sub_one_separable_iff (F := ℂ) (n := 4)).2
        (by norm_num)).squarefree
    · simp [hf]
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact f.eigenspaces_iSupIndep.comp fourthRoot_injective
  · rw [eq_top_iff, ← hsemi.iSup_eigenspace_eq_top]
    refine iSup_le fun μ => ?_
    by_cases hμ : f.eigenspace μ = ⊥
    · rw [hμ]
      exact bot_le
    · obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector
        (show f.HasEigenvalue μ from Module.End.hasEigenvalue_iff.mpr hμ)
      have hv4 : (f ^ 4) v = μ ^ 4 • v := hv.pow_apply 4
      rw [hf, Module.End.one_apply] at hv4
      have hμ4 : μ ^ 4 = 1 := by
        have h0 : (μ ^ 4 - 1) • v = 0 := by rw [sub_smul, ← hv4, one_smul, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hv.2)
      obtain ⟨j, rfl⟩ := exists_fourthRoot_eq hμ4
      exact le_iSup (fun j => f.eigenspace (fourthRoot j)) j

theorem trace_det_of_isInternal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → Submodule ℂ V} (hN : DirectSum.IsInternal N) (g : Module.End ℂ V) (c : ι → ℂ)
    (hg : ∀ j, ∀ v ∈ N j, g v = c j • v) :
    LinearMap.trace ℂ V g = ∑ j, (Module.finrank ℂ (N j) : ℂ) * c j ∧
      LinearMap.det g = ∏ j, c j ^ Module.finrank ℂ (N j) := by
  let b := hN.collectedBasis (fun j => Module.finBasis ℂ (N j))
  have hb : ∀ x, g (b x) = c x.1 • b x := fun x => hg x.1 _ (hN.collectedBasis_mem _ x)
  have hmat : LinearMap.toMatrix b b g = Matrix.diagonal (fun x => c x.1) := by
    ext x y
    rw [LinearMap.toMatrix_apply, hb, map_smul, b.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy
      simp
    · simp [hxy, Ne.symm hxy]
  constructor
  · rw [LinearMap.trace_eq_matrix_trace ℂ b, hmat, Matrix.trace_diagonal, Fintype.sum_sigma]
    simp [Finset.sum_const, Finset.card_univ]
  · rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal, Fintype.prod_sigma]
    simp [Finset.prod_const, Finset.card_univ]

theorem degree_congruence_of_det_eq_one {G : Type*} [Group G] (ρ : Representation ℂ G V)
    {u : G} (hu : u ^ 4 = 1) (hconj : IsConj u u⁻¹) (hdet : LinearMap.det (ρ u) = 1) :
    (∃ y : ℤ, ρ.character u = y) ∧ (∃ z : ℤ, ρ.character (u ^ 2) = z) ∧
      ∃ k : ℤ, ρ.character 1 + ρ.character (u ^ 2) - 2 * ρ.character u = 8 * k := by
  set f := ρ u with hfdef
  have hf4 : f ^ 4 = 1 := by rw [hfdef, ← map_pow, hu, map_one]
  have hN := isInternal_eigenspaces f hf4
  have hpow : ∀ k : ℕ, ∀ j, ∀ v ∈ Module.End.eigenspace f (fourthRoot j),
      (f ^ k) v = fourthRoot j ^ k • v := by
    intro k j v hv
    have hfv : f v = fourthRoot j • v := Module.End.mem_eigenspace_iff.mp hv
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hfv, smul_smul, pow_succ]
  set m : Fin 4 → ℕ := fun j => Module.finrank ℂ (Module.End.eigenspace f (fourthRoot j))
    with hm
  have hchar : ∀ k : ℕ, ρ.character (u ^ k) = ∑ j, (m j : ℂ) * fourthRoot j ^ k := by
    intro k
    have h := (trace_det_of_isInternal hN (f ^ k) (fun j => fourthRoot j ^ k) (hpow k)).1
    rw [← h, hfdef, ← map_pow]
    rfl
  have hdetf : LinearMap.det f = ∏ j, fourthRoot j ^ m j :=
    (trace_det_of_isInternal hN f fourthRoot (fun j v hv => by simpa using hpow 1 j v hv)).2
  have hu3 : u ^ 3 = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hu]
  have hinv : ρ.character (u ^ 3) = ρ.character u := by
    rw [hu3]
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [← hc, Representation.char_conj]
  have h0 := hchar 0
  have h1 := hchar 1
  have h2 := hchar 2
  have h3 := hchar 3
  simp only [Fin.sum_univ_four, Fin.prod_univ_four, fourthRoot_zero, fourthRoot_one,
    fourthRoot_two, fourthRoot_three] at h0 h1 h2 h3 hdetf
  rw [pow_zero] at h0
  rw [pow_one] at h1
  have h0' : ρ.character 1 = (m 0 : ℂ) + m 1 + m 2 + m 3 := by
    rw [h0]
    ring
  have h1' : ρ.character u = (m 0 : ℂ) - m 1 + Complex.I * ((m 2 : ℂ) - m 3) := by
    rw [h1]
    ring
  have h2' : ρ.character (u ^ 2) = (m 0 : ℂ) + m 1 - m 2 - m 3 := by
    rw [h2]
    linear_combination ((m 2 : ℂ) + m 3) * Complex.I_sq
  have h3' : ρ.character (u ^ 3) = (m 0 : ℂ) - m 1 - Complex.I * ((m 2 : ℂ) - m 3) := by
    rw [h3]
    linear_combination ((m 2 : ℂ) - m 3) * Complex.I * Complex.I_sq
  have hcd : (m 2 : ℂ) = m 3 := by
    have h := h3'.symm.trans (hinv.trans h1')
    have h' : (2 * Complex.I) * ((m 2 : ℂ) - m 3) = 0 := by linear_combination -h
    have hI : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hI)
  have hcd' : m 2 = m 3 := by exact_mod_cast hcd
  have hb : (-1 : ℂ) ^ m 1 = 1 := by
    have hII : Complex.I ^ m 2 * (-Complex.I) ^ m 2 = 1 := by
      rw [← mul_pow, show Complex.I * -Complex.I = 1 by
        rw [mul_neg, ← sq, Complex.I_sq, neg_neg], one_pow]
    have h := hdetf.symm.trans hdet
    rwa [← hcd', one_pow, one_mul, mul_assoc, hII, mul_one] at h
  obtain ⟨t, ht⟩ := (neg_one_pow_eq_one_iff_even (by norm_num)).mp hb
  have htc : (m 1 : ℂ) = t + t := by exact_mod_cast ht
  refine ⟨⟨(m 0 : ℤ) - m 1, ?_⟩, ⟨(m 0 : ℤ) + m 1 - 2 * m 2, ?_⟩, ⟨t, ?_⟩⟩
  · rw [h1', hcd']
    push_cast
    ring
  · rw [h2', hcd']
    push_cast
    ring
  · rw [h0', h1', h2', hcd', htc]
    push_cast
    ring

end OrderFourDegree

open OrderFourDegree

theorem det_representation_eq_one_of_mem_commutator {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) {g : G} (hg : g ∈ commutator G) :
    LinearMap.det (ρ g) = 1 := by
  let D : G →* ℂˣ := ((LinearMap.det : Module.End ℂ V →* ℂ).comp ρ).toHomUnits
  have h : D g = 1 := Abelianization.commutator_subset_ker D hg
  simpa [D] using congrArg Units.val h

theorem perfect_real_order_four_degree_congruence {G V : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {u : G} (hu : orderOf u = 4) (hconj : IsConj u u⁻¹) :
    (∃ y : ℤ, ρ.character u = y) ∧ (∃ z : ℤ, ρ.character (u ^ 2) = z) ∧
      ∃ k : ℤ, ρ.character 1 + ρ.character (u ^ 2) - 2 * ρ.character u = 8 * k :=
  degree_congruence_of_det_eq_one ρ (hu ▸ pow_orderOf_eq_one u) hconj
    (det_representation_eq_one_of_mem_commutator ρ Group.IsPerfect.mem_commutator)

theorem no_index_two_real_order_four_degree_congruence {G V : Type*} [Group G] [Finite G]
    (hG : ∀ H : Subgroup G, H.index ≠ 2) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {u : G} (hu : orderOf u = 4) (hconj : IsConj u u⁻¹) :
    (∃ y : ℤ, ρ.character u = y) ∧ (∃ z : ℤ, ρ.character (u ^ 2) = z) ∧
      ∃ k : ℤ, ρ.character 1 + ρ.character (u ^ 2) - 2 * ρ.character u = 8 * k := by
  have hp : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu]; norm_num)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hSc : (S : Subgroup G) ≤ commutator G := Subgroup.subgroupOf_eq_top.mp
    ((CFSG.Semidihedral.FocalTransfer.no_index_two_iff_derived_subgroupOf_eq_top S).mp hG)
  exact degree_congruence_of_det_eq_one ρ (hu ▸ pow_orderOf_eq_one u) hconj
    (det_representation_eq_one_of_mem_commutator ρ (hSc (hS (Subgroup.mem_zpowers u))))

end CFSG.Semidihedral.Principal
