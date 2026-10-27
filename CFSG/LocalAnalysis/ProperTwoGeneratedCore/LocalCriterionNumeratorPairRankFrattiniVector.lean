module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniOriginalSetup

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u v

section ElementaryAction

variable {A : Type u} [Group A] {V : Type v} [Group V]
variable {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V] [MulDistribMulAction A V]

@[expose] def elementaryActorLinear (a : A) : Additive V →ₗ[ZMod p] Additive V :=
  ((MulDistribMulAction.toMulAut A V a).toMonoidHom.toAdditive).toZModLinearMap p

@[expose] def elementaryActorFixedSubspace (a : A) : Submodule (ZMod p) (Additive V) :=
  (elementaryActorLinear (p := p) a).eqLocus LinearMap.id

theorem elementaryActorFixedSubspace_mem (a : A) (x : Additive V) :
    x ∈ elementaryActorFixedSubspace (p := p) a ↔ a • x.toMul = x.toMul := Iff.rfl

@[expose] def elementaryActorFixedSubspaceEquiv (a : A) :
    let : IsElementaryAbelian p (actorFixedSubgroup (I := V) a) :=
      elementary_subgroup (actorFixedSubgroup (I := V) a)
    Additive (actorFixedSubgroup (I := V) a) ≃ₗ[ZMod p]
      elementaryActorFixedSubspace (V := V) (p := p) a := by
  let : IsElementaryAbelian p (actorFixedSubgroup (I := V) a) :=
    elementary_subgroup (actorFixedSubgroup (I := V) a)
  let e : Additive (actorFixedSubgroup (I := V) a) ≃+
      elementaryActorFixedSubspace (V := V) (p := p) a :=
    { toFun := fun x => ⟨Additive.ofMul (x.toMul : V),
        (elementaryActorFixedSubspace_mem (V := V) (p := p) a _).mpr
          ((mem_actorFixedSubgroup a _).mp x.toMul.property)⟩
      invFun := fun x => Additive.ofMul ⟨x.val.toMul,
        (mem_actorFixedSubgroup a _).mpr
          ((elementaryActorFixedSubspace_mem (V := V) (p := p) a _).mp x.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective

theorem elementaryActorFixedSubspace_finrank (a : A) :
    let : IsElementaryAbelian p (actorFixedSubgroup (I := V) a) :=
      elementary_subgroup (actorFixedSubgroup (I := V) a)
    Module.finrank (ZMod p) (Additive (actorFixedSubgroup (I := V) a)) =
      Module.finrank (ZMod p) (elementaryActorFixedSubspace (V := V) (p := p) a) := by
  let : IsElementaryAbelian p (actorFixedSubgroup (I := V) a) :=
    elementary_subgroup (actorFixedSubgroup (I := V) a)
  exact (elementaryActorFixedSubspaceEquiv (V := V) (p := p) a).finrank_eq

theorem elementary_four_fixed_space_bounds [Finite A] [IsElementaryAbelian 2 A]
    [Finite V] (hAcard : Nat.card A = 4) (hpodd : Odd p)
    (hfixed : ∀ a : A, a ≠ 1 → Nat.card (actorFixedSubgroup (I := V) a) ≤ p) :
    (∀ a : A, a ≠ 1 →
      Module.finrank (ZMod p) (elementaryActorFixedSubspace (V := V) (p := p) a) ≤ 1) ∧
    Nat.card V ≤ p ^ 3 ∧ Module.finrank (ZMod p) (Additive V) ≤ 3 := by
  let : IsKleinFour A := isKleinFour_of_elementary_card_four hAcard
  refine ⟨?_, klein_four_elementary_finrank_bound hpodd hfixed⟩
  intro a ha
  let : IsElementaryAbelian p (actorFixedSubgroup (I := V) a) :=
    elementary_subgroup (actorFixedSubgroup (I := V) a)
  rw [← elementaryActorFixedSubspace_finrank (V := V) (p := p) a]
  exact elementary_finrank_le_of_card_le (n := 1) (by simpa only [pow_one] using hfixed a ha)

end ElementaryAction

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

@[expose] def ambientVectorFrattiniInversion (P : Subgroup G) (hP : IsPGroup p P)
    (t : G) (htP : t ∈ Subgroup.normalizer (P : Set G)) : Prop :=
  let := normalizerFrattiniBaseAction P
  let := frattiniQuotientAction (A := Subgroup.normalizer (P : Set G)) (P := P)
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  ∀ x : Additive (P ⧸ frattini P),
    elementaryActorLinear (p := p) (⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) x =
      (-1 : ZMod p) • x

theorem ambient_vector_inversion_iff (P : Subgroup G) (hP : IsPGroup p P)
    (t : G) (htP : t ∈ Subgroup.normalizer (P : Set G)) :
    ambientVectorFrattiniInversion P hP t htP ↔ ambientFrattiniInversion P t htP := by
  let := normalizerFrattiniBaseAction P
  let := frattiniQuotientAction (A := Subgroup.normalizer (P : Set G)) (P := P)
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  change (∀ x : Additive (P ⧸ frattini P),
    Additive.ofMul ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • x.toMul) =
      (-1 : ZMod p) • x) ↔
        (∀ x : P ⧸ frattini P,
          (⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • x = x⁻¹)
  constructor
  · intro h x
    exact congrArg Additive.toMul
      ((h (Additive.ofMul x)).trans (neg_one_smul (ZMod p) (Additive.ofMul x)))
  · intro h x
    exact (congrArg Additive.ofMul (h x.toMul)).trans (neg_one_smul (ZMod p) x).symm

theorem ambient_frattini_commutator_vector_image (P : Subgroup G) (hP : IsPGroup p P)
    (t : G) (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hinv : ambientVectorFrattiniInversion P hP t htP) (a : P) :
    let := normalizerFrattiniBaseAction P
    let : IsElementaryAbelian p (P ⧸ frattini P) :=
      (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
    Additive.ofMul (QuotientGroup.mk' (frattini P)
      (a⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • a))) =
      (-2 : ZMod p) • Additive.ofMul (QuotientGroup.mk' (frattini P) a) := by
  let := normalizerFrattiniBaseAction P
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  have h := (ambient_vector_inversion_iff P hP t htP).mp hinv
  change Additive.ofMul (QuotientGroup.mk' (frattini P)
    (a⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • a))) =
      (-2 : ZMod p) • Additive.ofMul (QuotientGroup.mk' (frattini P) a)
  rw [ambient_frattini_commutator_image P t htP h a,
    ofMul_mul, ofMul_inv]
  have hscalar := neg_smul (2 : ZMod p)
    (Additive.ofMul (QuotientGroup.mk' (frattini P) a))
  rw [two_smul (ZMod p), neg_add] at hscalar
  exact hscalar.symm

@[expose] def ambientVectorFrattiniBounds (P : Subgroup G) (hP : IsPGroup p P)
    (W : Subgroup G) (hWP : W ≤ Subgroup.normalizer (P : Set G)) : Prop :=
  let := normalizerFrattiniBaseAction P
  let : MulDistribMulAction W P := MulDistribMulAction.compHom P (Subgroup.inclusion hWP)
  let := frattiniQuotientAction (A := W) (P := P)
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  (∀ w : W, w ≠ 1 →
    Module.finrank (ZMod p)
      (elementaryActorFixedSubspace (V := P ⧸ frattini P) (p := p) w) ≤ 1) ∧
    Nat.card (P ⧸ frattini P) ≤ p ^ 3 ∧
      Module.finrank (ZMod p) (Additive (P ⧸ frattini P)) ≤ 3

theorem ambient_vector_bounds_of_group_bounds (P : Subgroup G) (hP : IsPGroup p P)
    (W : Subgroup G) (hWP : W ≤ Subgroup.normalizer (P : Set G))
    (hbounds : ambientFrattiniBounds P hP W hWP) :
    ambientVectorFrattiniBounds P hP W hWP := by
  let := normalizerFrattiniBaseAction P
  let : MulDistribMulAction W P := MulDistribMulAction.compHom P (Subgroup.inclusion hWP)
  let := frattiniQuotientAction (A := W) (P := P)
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  change _ ∧ _ ∧ _
  refine ⟨?_, hbounds.2⟩
  intro w hw
  let : IsElementaryAbelian p (actorFixedSubgroup (I := P ⧸ frattini P) w) :=
    elementary_subgroup (actorFixedSubgroup (I := P ⧸ frattini P) w)
  rw [← elementaryActorFixedSubspace_finrank (V := P ⧸ frattini P) (p := p) w]
  exact (hbounds.1 w hw).2.2

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
