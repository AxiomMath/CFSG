module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniScalar
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG CFSG.ShultStronglyClosedTI LocalCriterionGeometry LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

theorem ambient_fixed_representative_commutator_mem
    (I P : Subgroup G) (hPI : P ≤ I) (w t : G)
    (hwP : w ∈ Subgroup.normalizer (P : Set G))
    (htP : t ∈ Subgroup.normalizer (P : Set G)) (ht : orderOf t = 2)
    (a : P)
    (ha : let := normalizerFrattiniBaseAction P
      a ∈ actorFixedSubgroup (I := P) (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G))) :
    let := normalizerFrattiniBaseAction P
    ((a⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • a) : P) : G) ∈
      rightInvolutionCommutatorSubgroup t
        (I ⊓ Subgroup.centralizer ({w} : Set G)) ⊓ P := by
  let := normalizerFrattiniBaseAction P
  have hgen := actorCommutatorSubgroup_generator_mem
    (⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) ha
  have himage : ((a⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • a) : P) : G) ∈
      (actorCommutatorSubgroup (⟨t, htP⟩ : Subgroup.normalizer (P : Set G))
        (actorFixedSubgroup (I := P)
          (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G)))).map P.subtype :=
    Subgroup.mem_map.mpr ⟨_, hgen, rfl⟩
  rw [ambient_fixed_commutator_map P w t hwP htP ht] at himage
  exact ⟨right_involution_commutator_mono t (inf_le_inf hPI le_rfl) himage,
    (a⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • a)).property⟩

@[expose] def ambientVectorFrattiniRepresentatives [Finite G] {p : ℕ} [Fact p.Prime]
    (I P : Subgroup G) (hP : IsPGroup p P)
    (W : Subgroup G) (hWP : W ≤ Subgroup.normalizer (P : Set G))
    (t : G) (htP : t ∈ Subgroup.normalizer (P : Set G)) : Prop :=
  let := normalizerFrattiniBaseAction P
  let : MulDistribMulAction W P := MulDistribMulAction.compHom P (Subgroup.inclusion hWP)
  let := frattiniQuotientAction (A := W) (P := P)
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  ∀ w : W, ∀ x : elementaryActorFixedSubspace (V := P ⧸ frattini P) (p := p) w,
    ∃ a ∈ actorFixedSubgroup (I := P) w,
      (a : G) ∈ I ⊓ Subgroup.centralizer ({(w : G)} : Set G) ∧
        ((a⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • a) : P) : G) ∈
          rightInvolutionCommutatorSubgroup t
            (I ⊓ Subgroup.centralizer ({(w : G)} : Set G)) ⊓ P ∧
        Additive.ofMul (QuotientGroup.mk' (frattini P)
          (a⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • a))) =
            (x : Additive (P ⧸ frattini P)) ∧
        (-2 : ZMod p) • Additive.ofMul (QuotientGroup.mk' (frattini P) a) =
          (x : Additive (P ⧸ frattini P))

theorem ambient_four_frattini_vector_representatives [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (I P : Subgroup G) (hPI : P ≤ I) (hP : IsPGroup p P)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWcard : Nat.card W = 4)
    (hWP : W ≤ Subgroup.normalizer (P : Set G))
    (t : G) (ht : orderOf t = 2)
    (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hinv : ambientVectorFrattiniInversion P hP t htP) :
    ambientVectorFrattiniRepresentatives I P hP W hWP t htP := by
  let : IsKleinFour W := isKleinFour_of_elementary_card_four hWcard
  let := normalizerFrattiniBaseAction P
  let := frattiniQuotientAction (A := Subgroup.normalizer (P : Set G)) (P := P)
  let : MulDistribMulAction W P := MulDistribMulAction.compHom P (Subgroup.inclusion hWP)
  let : MulDistribMulAction W (P ⧸ frattini P) :=
    MulDistribMulAction.compHom (P ⧸ frattini P) (Subgroup.inclusion hWP)
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  change ∀ w : W, ∀ x : elementaryActorFixedSubspace (V := P ⧸ frattini P) (p := p) w,
    ∃ a ∈ actorFixedSubgroup (I := P) w,
      (a : G) ∈ I ⊓ Subgroup.centralizer ({(w : G)} : Set G) ∧
        ((a⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • a) : P) : G) ∈
          rightInvolutionCommutatorSubgroup t
            (I ⊓ Subgroup.centralizer ({(w : G)} : Set G)) ⊓ P ∧
        Additive.ofMul (QuotientGroup.mk' (frattini P)
          (a⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • a))) =
            (x : Additive (P ⧸ frattini P)) ∧
        (-2 : ZMod p) • Additive.ofMul (QuotientGroup.mk' (frattini P) a) =
          (x : Additive (P ⧸ frattini P))
  intro w x
  let wN : Subgroup.normalizer (P : Set G) := ⟨w, hWP w.property⟩
  let tN : Subgroup.normalizer (P : Set G) := ⟨t, htP⟩
  have hwsq : wN ^ 2 = 1 := by
    apply Subtype.ext
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
      congrArg Subtype.val (IsKleinFour.mul_self w)
  have hinvg := (ambient_vector_inversion_iff P hP t htP).mp hinv
  obtain ⟨a, ha, hqa⟩ := frattini_fixed_vector_commutator_representative
    hP hpodd wN tN hwsq hinvg x
  have haw : (a : G) ∈ P ⊓ Subgroup.centralizer ({(w : G)} : Set G) := by
    rw [← ambient_fixed_subgroup_map P (w : G) (hWP w.property)]
    exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  refine ⟨a, ha, ⟨hPI a.property, haw.2⟩,
    ambient_fixed_representative_commutator_mem I P hPI (w : G) t
      (hWP w.property) htP ht a ha, hqa, ?_⟩
  exact (ambient_frattini_commutator_vector_image P hP t htP hinv a).symm.trans hqa

theorem original_pair_frattini_vector_representatives [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (P : Subgroup G) (hPI : P ≤ pairOddCore H beta) (hP : IsPGroup p P)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWcard : Nat.card W = 4)
    (hinvariant : W ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G))
    (hinv : ambientVectorFrattiniInversion P hP t
      (invariant_flip_mem_normalizer P W t hinvariant)) :
    ambientVectorFrattiniRepresentatives (pairOddCore H beta) P hP W
      (invariant_four_group_le_normalizer P W t hinvariant) t
        (invariant_flip_mem_normalizer P W t hinvariant) :=
  ambient_four_frattini_vector_representatives hpodd (pairOddCore H beta) P hPI hP
    W hWcard (invariant_four_group_le_normalizer P W t hinvariant) t
    (original_pair_flip_order h ht) (invariant_flip_mem_normalizer P W t hinvariant) hinv

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
