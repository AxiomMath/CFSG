module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniAmbient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG CFSG.ShultStronglyClosedTI LocalCriterionGeometry LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

theorem invariant_four_group_le_normalizer (P W : Subgroup G) (t : G)
    (hinvariant : W ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G)) :
    W ≤ Subgroup.normalizer (P : Set G) :=
  le_sup_left.trans hinvariant

theorem invariant_flip_mem_normalizer (P W : Subgroup G) (t : G)
    (hinvariant : W ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G)) :
    t ∈ Subgroup.normalizer (P : Set G) :=
  Subgroup.zpowers_le.mp (le_sup_right.trans hinvariant)

theorem centralizer_four_group_commutes (W : Subgroup G) (t : G)
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G)) (w : W) : Commute (w : G) t :=
  Subgroup.mem_centralizer_singleton_iff.mp (hWt w.property)

theorem original_pair_flip_order [Finite G] {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    orderOf t = 2 :=
  order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1

theorem elementary_four_frattini_fixed_lifting [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P) (hpodd : Odd p)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWcard : Nat.card W = 4)
    (hWP : W ≤ Subgroup.normalizer (P : Set G)) :
    let := normalizerFrattiniBaseAction P
    let : MulDistribMulAction W P := MulDistribMulAction.compHom P (Subgroup.inclusion hWP)
    let := frattiniQuotientAction (A := W) (P := P)
    ∀ w : W, actorFixedSubgroup (I := P ⧸ frattini P) w =
      (actorFixedSubgroup (I := P) w).map (QuotientGroup.mk' (frattini P)) := by
  let : IsKleinFour W := isKleinFour_of_elementary_card_four hWcard
  let := normalizerFrattiniBaseAction P
  let := frattiniQuotientAction (A := Subgroup.normalizer (P : Set G)) (P := P)
  let : MulDistribMulAction W P := MulDistribMulAction.compHom P (Subgroup.inclusion hWP)
  let : MulDistribMulAction W (P ⧸ frattini P) :=
    MulDistribMulAction.compHom (P ⧸ frattini P) (Subgroup.inclusion hWP)
  change ∀ w : W, actorFixedSubgroup (I := P ⧸ frattini P) w =
    (actorFixedSubgroup (I := P) w).map (QuotientGroup.mk' (frattini P))
  intro w
  let wN : Subgroup.normalizer (P : Set G) := ⟨w, hWP w.property⟩
  have hwsq : wN ^ 2 = 1 := by
    apply Subtype.ext
    change (w : G) ^ 2 = 1
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
      congrArg Subtype.val (IsKleinFour.mul_self w)
  exact frattini_fixed_quotient_eq_image hP hpodd wN hwsq

theorem ambient_frattini_commutator_image (P : Subgroup G) (t : G)
    (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hinv : ambientFrattiniInversion P t htP) (a : P) :
    let := normalizerFrattiniBaseAction P
    QuotientGroup.mk' (frattini P)
        (a⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • a)) =
      (QuotientGroup.mk' (frattini P) a)⁻¹ * (QuotientGroup.mk' (frattini P) a)⁻¹ := by
  let := normalizerFrattiniBaseAction P
  exact frattini_commutator_image (⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) hinv a

theorem original_pair_frattini_bounds_of_local_cyclic [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (P : Subgroup G) (hPI : P ≤ pairOddCore H beta) (hP : IsPGroup p P)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWcard : Nat.card W = 4)
    (hWt : W ≤ Subgroup.centralizer ({t} : Set G))
    (hinvariant : W ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G))
    (hinv : ambientFrattiniInversion P t (invariant_flip_mem_normalizer P W t hinvariant))
    (hcyclic : ∀ w : W, w ≠ 1 →
      IsCyclic (rightInvolutionCommutatorSubgroup t
        (pairOddCore H beta ⊓ Subgroup.centralizer ({(w : G)} : Set G)))) :
    ambientFrattiniBounds P hP W (invariant_four_group_le_normalizer P W t hinvariant) := by
  let : IsKleinFour W := isKleinFour_of_elementary_card_four hWcard
  exact ambient_frattini_four_group_bounds hpodd (pairOddCore H beta) P hPI hP W
    (invariant_four_group_le_normalizer P W t hinvariant) t (original_pair_flip_order h ht)
    (invariant_flip_mem_normalizer P W t hinvariant)
    (centralizer_four_group_commutes W t hWt) hinv hcyclic

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
