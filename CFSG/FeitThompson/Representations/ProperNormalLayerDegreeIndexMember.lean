module

public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
import CFSG.FeitThompson.Representations.TensorAndDualCharacters
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace SolvableNormalLayer

open Module

theorem coe_monoidHom_units_mem_Irr {G : Type*} [Group G] (χ : G →* ℂˣ) :
    (fun g => (χ g : ℂ)) ∈ Irr G := by
  have hirr : (Representation.twist (Representation.trivial ℂ G ℂ) χ).IsIrreducible :=
    Representation.isIrreducible_of_finrank_eq_one _ (finrank_self ℂ)
  have h := character_mem_Irr_of_isIrreducible _ hirr
  have hc : (Representation.twist (Representation.trivial ℂ G ℂ) χ).character
      = fun g => (χ g : ℂ) := by
    funext g
    rw [Representation.character_twist]
    simp [Representation.character, Representation.trivial]
  rwa [hc] at h

theorem exists_monoidHom_units_apply_ne_one (Q : Type*) [Group Q] [Finite Q]
    [Group.IsSolvable Q] [Nontrivial Q] : ∃ (ψ : Q →* ℂˣ) (x : Q), ψ x ≠ 1 := by
  have hcomm : _root_.commutator Q ≠ ⊤ :=
    (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Q)).ne
  have : Nontrivial (Abelianization Q) := QuotientGroup.nontrivial_iff.2 hcomm
  have : Finite (Abelianization Q) := Quotient.finite _
  have : NeZero (Monoid.exponent (Abelianization Q)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨a, ha⟩ := exists_ne (1 : Abelianization Q)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Abelianization Q) ℂ ha
  obtain ⟨x, hx⟩ : ∃ x : Q, Abelianization.of x = a := Quot.exists_rep a
  exact ⟨φ.comp Abelianization.of, x, by rw [MonoidHom.comp_apply, hx]; exact hφ⟩

theorem indClassFun_one_eq_index {L : Type*} [Group L] [Fintype L] (K : Subgroup L)
    {θ : K → ℂ} (hθ : θ 1 = 1) : indClassFun K θ 1 = (K.index : ℂ) := by
  have hK : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [indClassFun_one, hθ, mul_one, div_eq_iff hK, ← Nat.cast_mul, mul_comm,
    Subgroup.card_mul_index]

theorem exists_mem_Irr_ne_one_apply_one_eq_one_of_lt {L : Type*} [Group L] [Finite L]
    {K A : Subgroup L} [Group.IsSolvable K] [A.Normal] (hAK : A < K) :
    ∃ θ ∈ Irr K, θ ≠ 1 ∧ (A.subgroupOf K : Set K) ⊆ charValueKernel θ ∧ θ 1 = 1 := by
  have _ : (A.subgroupOf K).Normal := ‹A.Normal›.subgroupOf K
  have hne : A.subgroupOf K ≠ ⊤ := fun h => hAK.not_ge (Subgroup.subgroupOf_eq_top.1 h)
  have : Nontrivial (K ⧸ A.subgroupOf K) := QuotientGroup.nontrivial_iff.2 hne
  obtain ⟨ψ, q, hq⟩ := exists_monoidHom_units_apply_ne_one (K ⧸ A.subgroupOf K)
  set χ : K →* ℂˣ := ψ.comp (QuotientGroup.mk' (A.subgroupOf K)) with hχ
  refine ⟨fun x => (χ x : ℂ), coe_monoidHom_units_mem_Irr χ, ?_, ?_, by simp⟩
  · obtain ⟨x, hx⟩ : ∃ x : K, (QuotientGroup.mk x : K ⧸ A.subgroupOf K) = q := Quot.exists_rep q
    intro h
    have hx1 : (χ x : ℂ) = 1 := congrFun h x
    exact hq (by rw [← hx]; exact Units.ext (by simpa [hχ] using hx1))
  · intro x hx
    refine mem_charValueKernel.2 ?_
    have h1 : (QuotientGroup.mk x : K ⧸ A.subgroupOf K) = 1 := (QuotientGroup.eq_one_iff x).2 hx
    change (χ x : ℂ) = (χ 1 : ℂ)
    simp [hχ, h1]

theorem exists_mem_Irr_indClassFun_one_eq_index_of_lt {L : Type*} [Group L] [Fintype L]
    {K A : Subgroup L} [Group.IsSolvable K] [A.Normal] (hAK : A < K) :
    ∃ θ ∈ Irr K, θ ≠ 1 ∧ (A.subgroupOf K : Set K) ⊆ charValueKernel θ ∧ θ 1 = 1 ∧
      indClassFun K θ 1 = (K.index : ℂ) := by
  obtain ⟨θ, hθ, hne, hker, h1⟩ := exists_mem_Irr_ne_one_apply_one_eq_one_of_lt (A := A) hAK
  exact ⟨θ, hθ, hne, hker, h1, indClassFun_one_eq_index K h1⟩

theorem exists_mem_indFam_apply_one_eq_index_of_lt {L : Type*} [Group L] [Fintype L]
    {K A : Subgroup L} [Group.IsSolvable K] [A.Normal] (hAK : A < K) :
    ∃ f ∈ indFam K (Irr K), f 1 = (K.index : ℂ) := by
  obtain ⟨θ, hθ, -, -, -, hdeg⟩ := exists_mem_Irr_indClassFun_one_eq_index_of_lt (A := A) hAK
  exact ⟨indClassFun K θ, indClassFun_mem_indFam K hθ, hdeg⟩

end SolvableNormalLayer

end CFSG.FeitThompson
