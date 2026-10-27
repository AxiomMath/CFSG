module

public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalQuotient

public noncomputable section

namespace CFSG.Wreathed.ComponentCoveringLocal

universe u

@[expose] def ambientInternalIntersectionEquiv {X : Type u} [Group X]
    (K N : Subgroup X) : ↥(K ⊓ N) ≃* K.subgroupOf N where
  toFun b := ⟨⟨b.val, b.property.2⟩, b.property.1⟩
  invFun b := ⟨b.val.val, ⟨b.property, b.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem ambientInternalIntersectionEquiv_coe {X : Type u} [Group X]
    (K N : Subgroup X) (b : ↥(K ⊓ N)) :
    (ambientInternalIntersectionEquiv K N b).val.val = b.val := rfl

theorem ambientInternalIntersectionEquiv_symm_coe {X : Type u} [Group X]
    (K N : Subgroup X) (b : K.subgroupOf N) :
    ((ambientInternalIntersectionEquiv K N).symm b).val = b.val.val := rfl

variable {G : Type} [Group G] [Finite G]

abbrev originalAmbientCentralizerSubgroup (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) := K ⊓ involutionCentralizer n S e

@[expose] def ambientOriginalImageMap (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    originalAmbientCentralizerSubgroup n S e K →* originalImage n S e K :=
  (originalImageMap n S e K).comp
    (ambientInternalIntersectionEquiv K (involutionCentralizer n S e)).toMonoidHom

omit [Finite G] in
theorem ambientOriginalImageMap_coe (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (b : originalAmbientCentralizerSubgroup n S e K) :
    (ambientOriginalImageMap n S e K b : centralizerOddCoreQuotient n S e) =
      centralizerOddCoreMap n S e (Subgroup.inclusion inf_le_right b) := rfl

omit [Finite G] in
theorem ambientOriginalImageMap_surjective (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    Function.Surjective (ambientOriginalImageMap n S e K) :=
  (originalImageMap_surjective n S e K).comp
    (ambientInternalIntersectionEquiv K (involutionCentralizer n S e)).surjective

omit [Finite G] in
theorem ambientOriginalImageMap_ker (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    (ambientOriginalImageMap n S e K).ker =
      ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype).subgroupOf
        (originalAmbientCentralizerSubgroup n S e K) := by
  ext b
  change ambientInternalIntersectionEquiv K (involutionCentralizer n S e) b ∈
    (originalImageMap n S e K).ker ↔ _
  rw [originalImageMap_ker]
  constructor
  · intro hb
    exact ⟨Subgroup.inclusion inf_le_right b, hb, rfl⟩
  · rintro ⟨r, hr, heq⟩
    change Subgroup.inclusion inf_le_right b ∈ centralizerOddCore n S e
    exact (Subtype.ext heq : r = Subgroup.inclusion inf_le_right b) ▸ hr

theorem ambient_original_centralizer_odd_core_eq_kernel
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (hnormal : (originalImage n S e K).Normal) :
    CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K) =
      ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype).subgroupOf
        (originalAmbientCentralizerSubgroup n S e K) := by
  let : (originalImage n S e K).Normal := hnormal
  have hcore := normal_subgroup_odd_core_eq_bot (originalImage n S e K)
    (centralizerOddCoreQuotient_oddCore_eq_bot n S e)
  have hR : Odd (Nat.card ((centralizerOddCore n S e).map
      (involutionCentralizer n S e).subtype)) :=
    (CFSG.ComponentClassification.OddCore.odd_card (involutionCentralizer n S e)).of_dvd_nat
      (Subgroup.card_map_dvd _ _)
  have hker : Odd (Nat.card (ambientOriginalImageMap n S e K).ker) := by
    rw [ambientOriginalImageMap_ker]
    exact hR.of_dvd_nat (Subgroup.card_comap_dvd_of_injective _
      (originalAmbientCentralizerSubgroup n S e K).subtype
      (originalAmbientCentralizerSubgroup n S e K).subtype_injective)
  exact (odd_kernel_eq_odd_core_of_corefree_target (ambientOriginalImageMap n S e K)
    (ambientOriginalImageMap_surjective n S e K) hker hcore).trans
      (ambientOriginalImageMap_ker n S e K)

theorem ambient_original_centralizer_odd_core_map
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (hnormal : (originalImage n S e K).Normal) :
    (CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K)).map
        (originalAmbientCentralizerSubgroup n S e K).subtype =
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
        originalAmbientCentralizerSubgroup n S e K := by
  rw [ambient_original_centralizer_odd_core_eq_kernel n S e K hnormal]
  exact Subgroup.subgroupOf_map_subtype _ _

@[expose] def ambientOriginalCoreQuotientEquiv
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (hnormal : (originalImage n S e K).Normal) :
    originalAmbientCentralizerSubgroup n S e K ⧸
        CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K) ≃* originalImage n S e K :=
  (QuotientGroup.quotientMulEquivOfEq
    ((ambient_original_centralizer_odd_core_eq_kernel n S e K hnormal).trans
      (ambientOriginalImageMap_ker n S e K).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (ambientOriginalImageMap n S e K)
      (ambientOriginalImageMap_surjective n S e K))

theorem ambientOriginalCoreQuotientEquiv_mk
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (hnormal : (originalImage n S e K).Normal)
    (b : originalAmbientCentralizerSubgroup n S e K) :
    ambientOriginalCoreQuotientEquiv n S e K hnormal
        (QuotientGroup.mk' (CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K)) b) =
      ambientOriginalImageMap n S e K b := rfl

theorem ambientOriginalCoreQuotientEquiv_symm_map
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (hnormal : (originalImage n S e K).Normal)
    (b : originalAmbientCentralizerSubgroup n S e K) :
    (ambientOriginalCoreQuotientEquiv n S e K hnormal).symm
        (ambientOriginalImageMap n S e K b) =
      QuotientGroup.mk' (CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K)) b := by
  rw [← ambientOriginalCoreQuotientEquiv_mk n S e K hnormal b, MulEquiv.symm_apply_apply]

theorem ambientOriginalCoreQuotientEquiv_every_inverse
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (hnormal : (originalImage n S e K).Normal) (d : originalImage n S e K) :
    ∃ b : originalAmbientCentralizerSubgroup n S e K,
      ambientOriginalImageMap n S e K b = d ∧
      (ambientOriginalCoreQuotientEquiv n S e K hnormal).symm d =
        QuotientGroup.mk' (CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K)) b := by
  obtain ⟨b, rfl⟩ := ambientOriginalImageMap_surjective n S e K d
  exact ⟨b, rfl, ambientOriginalCoreQuotientEquiv_symm_map n S e K hnormal b⟩

end CFSG.Wreathed.ComponentCoveringLocal
