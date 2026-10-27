module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniVector

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u v

theorem odd_negative_two_isUnit (p : ℕ) (hpodd : Odd p) : IsUnit (-2 : ZMod p) := by
  have hu : IsUnit (2 : ZMod p) := (ZMod.isUnit_iff_coprime 2 p).mpr hpodd.coprime_two_left
  exact hu.neg

section ElementaryAction

variable {A : Type u} [Group A] {V : Type v} [Group V]
variable {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V] [MulDistribMulAction A V]

@[expose] def negativeTwoFixedSpaceEquiv (hpodd : Odd p) (a : A) :
    elementaryActorFixedSubspace (V := V) (p := p) a ≃ₗ[ZMod p]
      elementaryActorFixedSubspace (V := V) (p := p) a :=
  LinearEquiv.smulOfNeZero (ZMod p) _ (-2 : ZMod p) (odd_negative_two_isUnit p hpodd).ne_zero

theorem negativeTwoFixedSpaceEquiv_apply (hpodd : Odd p) (a : A)
    (x : elementaryActorFixedSubspace (V := V) (p := p) a) :
    (negativeTwoFixedSpaceEquiv (V := V) hpodd a x : Additive V) =
      (-2 : ZMod p) • (x : Additive V) := rfl

theorem negative_two_covers_fixed_space (hpodd : Odd p) (a : A)
    (x : elementaryActorFixedSubspace (V := V) (p := p) a) :
    ∃ y : elementaryActorFixedSubspace (V := V) (p := p) a,
      (-2 : ZMod p) • (y : Additive V) = (x : Additive V) := by
  refine ⟨(negativeTwoFixedSpaceEquiv (V := V) hpodd a).symm x, ?_⟩
  exact congrArg Subtype.val ((negativeTwoFixedSpaceEquiv (V := V) hpodd a).apply_symm_apply x)

end ElementaryAction

section FrattiniAction

variable {A : Type u} [Group A] [Finite A]
variable {P : Type v} [Group P] [Finite P] [MulDistribMulAction A P]
variable {p : ℕ} [Fact p.Prime]

omit [Finite A] in
theorem frattini_commutator_vector_image (hP : IsPGroup p P) (t : A)
    (hinv : let := frattiniQuotientAction (A := A) (P := P)
      ∀ x : P ⧸ frattini P, t • x = x⁻¹) (a : P) :
    let : IsElementaryAbelian p (P ⧸ frattini P) :=
      (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
    Additive.ofMul (QuotientGroup.mk' (frattini P) (a⁻¹ * (t • a))) =
      (-2 : ZMod p) • Additive.ofMul (QuotientGroup.mk' (frattini P) a) := by
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  rw [frattini_commutator_image t hinv a, ofMul_mul, ofMul_inv]
  have hscalar := neg_smul (2 : ZMod p) (Additive.ofMul (QuotientGroup.mk' (frattini P) a))
  rw [two_smul (ZMod p), neg_add] at hscalar
  exact hscalar.symm

theorem frattini_fixed_vector_commutator_representative
    (hP : IsPGroup p P) (hpodd : Odd p) (w t : A) (hw : w ^ 2 = 1)
    (hinv : let := frattiniQuotientAction (A := A) (P := P)
      ∀ x : P ⧸ frattini P, t • x = x⁻¹) :
    let := frattiniQuotientAction (A := A) (P := P)
    let : IsElementaryAbelian p (P ⧸ frattini P) :=
      (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
    ∀ x : elementaryActorFixedSubspace (V := P ⧸ frattini P) (p := p) w,
      ∃ a ∈ actorFixedSubgroup (I := P) w,
        Additive.ofMul (QuotientGroup.mk' (frattini P) (a⁻¹ * (t • a))) =
          (x : Additive (P ⧸ frattini P)) := by
  let := frattiniQuotientAction (A := A) (P := P)
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  change ∀ x : elementaryActorFixedSubspace (V := P ⧸ frattini P) (p := p) w,
    ∃ a ∈ actorFixedSubgroup (I := P) w,
      Additive.ofMul (QuotientGroup.mk' (frattini P) (a⁻¹ * (t • a))) =
        (x : Additive (P ⧸ frattini P))
  intro x
  obtain ⟨y, hy⟩ := negative_two_covers_fixed_space hpodd w x
  have hyfixed : y.val.toMul ∈ actorFixedSubgroup (I := P ⧸ frattini P) w :=
    (mem_actorFixedSubgroup w _).mpr
      ((elementaryActorFixedSubspace_mem (V := P ⧸ frattini P) (p := p) w _).mp y.property)
  rw [frattini_fixed_quotient_eq_image hP hpodd w hw] at hyfixed
  obtain ⟨a, ha, hqa⟩ := Subgroup.mem_map.mp hyfixed
  refine ⟨a, ha, ?_⟩
  rw [frattini_commutator_vector_image hP t hinv a, hqa]
  exact hy

end FrattiniAction

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
