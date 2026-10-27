module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniVector
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniIntersection

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG CFSG.ShultStronglyClosedTI LocalCriterionGeometry LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]

theorem elementary_four_ambient_order
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWcard : Nat.card W = 4)
    (w : W) (hw : w ≠ 1) : orderOf (w : G) = 2 := by
  let : IsKleinFour W := isKleinFour_of_elementary_card_four hWcard
  have hwsq : (w : G) ^ 2 = 1 := by
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
      congrArg Subtype.val (IsKleinFour.mul_self w)
  exact orderOf_eq_prime_iff.mpr ⟨hwsq, fun h => hw (Subtype.ext h)⟩

theorem ambient_four_frattini_fixed_commutator_images
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (I P : Subgroup G) (hPI : P ≤ I) (hP : IsPGroup p P)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWcard : Nat.card W = 4)
    (hWP : W ≤ Subgroup.normalizer (P : Set G))
    (t : G) (ht : orderOf t = 2)
    (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G))
    (hinv : ambientFrattiniInversion P t htP) :
    let := normalizerFrattiniBaseAction P
    let : MulDistribMulAction W P := MulDistribMulAction.compHom P (Subgroup.inclusion hWP)
    let := frattiniQuotientAction (A := W) (P := P)
    ∀ w : W,
      actorFixedSubgroup (I := P ⧸ frattini P) w =
          (actorFixedSubgroup (I := P) w).map (QuotientGroup.mk' (frattini P)) ∧
        actorFixedSubgroup (I := P ⧸ frattini P) w =
          ((rightInvolutionCommutatorSubgroup t
            (I ⊓ Subgroup.centralizer ({(w : G)} : Set G))).subgroupOf P).map
              (QuotientGroup.mk' (frattini P)) := by
  let : IsKleinFour W := isKleinFour_of_elementary_card_four hWcard
  let := normalizerFrattiniBaseAction P
  let := frattiniQuotientAction (A := Subgroup.normalizer (P : Set G)) (P := P)
  let : MulDistribMulAction W P := MulDistribMulAction.compHom P (Subgroup.inclusion hWP)
  let : MulDistribMulAction W (P ⧸ frattini P) :=
    MulDistribMulAction.compHom (P ⧸ frattini P) (Subgroup.inclusion hWP)
  change ∀ w : W, _ ∧ _
  intro w
  have hwsq : (w : G) ^ 2 = 1 := by
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
      congrArg Subtype.val (IsKleinFour.mul_self w)
  exact ⟨elementary_four_frattini_fixed_lifting P hP hpodd W hWcard hWP w,
    ambient_frattini_fixed_eq_commutator_intersection hpodd I P hPI hP (w : G) t
      (hWP w.property) htP hwsq ht (centralizer_four_group_commutes W t hWt w) hinv⟩

@[expose] def ambientFrattiniActionData
    {p : ℕ} [Fact p.Prime] (I P : Subgroup G) (hP : IsPGroup p P)
    (W : Subgroup G) (hWP : W ≤ Subgroup.normalizer (P : Set G))
    (t : G) (htP : t ∈ Subgroup.normalizer (P : Set G)) : Prop :=
  let := normalizerFrattiniBaseAction P
  let : MulDistribMulAction W P := MulDistribMulAction.compHom P (Subgroup.inclusion hWP)
  let := frattiniQuotientAction (A := W) (P := P)
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  ((frattini P).Characteristic ∧ Group.IsSolvable (frattini P) ∧
    Odd (Nat.card (frattini P)) ∧ IsElementaryAbelian p (P ⧸ frattini P) ∧
      Odd (Nat.card (P ⧸ frattini P))) ∧
    (∀ w : W,
      actorFixedSubgroup (I := P ⧸ frattini P) w =
          (actorFixedSubgroup (I := P) w).map (QuotientGroup.mk' (frattini P)) ∧
        actorFixedSubgroup (I := P ⧸ frattini P) w =
          ((rightInvolutionCommutatorSubgroup t
            (I ⊓ Subgroup.centralizer ({(w : G)} : Set G))).subgroupOf P).map
              (QuotientGroup.mk' (frattini P))) ∧
    (∀ a : P,
      Additive.ofMul (QuotientGroup.mk' (frattini P)
        (a⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • a))) =
          (-2 : ZMod p) • Additive.ofMul (QuotientGroup.mk' (frattini P) a)) ∧
    ambientFrattiniBounds P hP W hWP ∧ ambientVectorFrattiniBounds P hP W hWP

theorem ambient_vector_frattini_action_data_of_local_cyclic
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (I P : Subgroup G) (hPI : P ≤ I) (hP : IsPGroup p P)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWcard : Nat.card W = 4)
    (hWP : W ≤ Subgroup.normalizer (P : Set G))
    (t : G) (ht : orderOf t = 2)
    (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G))
    (hinv : ambientVectorFrattiniInversion P hP t htP)
    (hcyclic : ∀ w : W, w ≠ 1 →
      IsCyclic (rightInvolutionCommutatorSubgroup t
        (I ⊓ Subgroup.centralizer ({(w : G)} : Set G)))) :
    ambientFrattiniActionData I P hP W hWP t htP := by
  let : IsKleinFour W := isKleinFour_of_elementary_card_four hWcard
  have hinvg := (ambient_vector_inversion_iff P hP t htP).mp hinv
  have hbounds := ambient_frattini_four_group_bounds hpodd I P hPI hP W hWP t ht htP
    (centralizer_four_group_commutes W t hWt) hinvg hcyclic
  exact ⟨frattini_kernel_structure hP hpodd,
    ambient_four_frattini_fixed_commutator_images hpodd I P hPI hP W hWcard hWP
      t ht htP hWt hinvg,
    ambient_frattini_commutator_vector_image P hP t htP hinv,
    hbounds, ambient_vector_bounds_of_group_bounds P hP W hWP hbounds⟩

theorem original_pair_frattini_action_data_of_local_cyclic
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (P : Subgroup G) (hPI : P ≤ pairOddCore H beta) (hP : IsPGroup p P)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWcard : Nat.card W = 4)
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G))
    (hinvariant : W ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G))
    (hinv : ambientVectorFrattiniInversion P hP t
      (invariant_flip_mem_normalizer P W t hinvariant))
    (hcyclic : ∀ w : W, w ≠ 1 →
      IsCyclic (rightInvolutionCommutatorSubgroup t
        (pairOddCore H beta ⊓ Subgroup.centralizer ({(w : G)} : Set G)))) :
    ambientFrattiniActionData (pairOddCore H beta) P hP W
      (invariant_four_group_le_normalizer P W t hinvariant) t
        (invariant_flip_mem_normalizer P W t hinvariant) :=
  ambient_vector_frattini_action_data_of_local_cyclic hpodd (pairOddCore H beta) P hPI hP
    W hWcard (invariant_four_group_le_normalizer P W t hinvariant) t
    (original_pair_flip_order h ht) (invariant_flip_mem_normalizer P W t hinvariant)
    hWt hinv hcyclic

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
