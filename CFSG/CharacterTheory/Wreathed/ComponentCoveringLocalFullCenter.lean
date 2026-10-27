module

public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalQuotient

public noncomputable section

namespace CFSG.Wreathed.ComponentCoveringLocal

open NormalOddIndexFullCenterLayer SmallerRecognitionOriginalField

variable {G : Type} [Group G] [Finite G]

abbrev originalImageFullQuotient (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :=
  originalImage n S e K ⧸ Subgroup.center (originalImage n S e K)

abbrev originalImageFullLayer (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :=
  CFSG.generalizedFitting (originalImageFullQuotient n S e K)

variable [IsSimpleGroup G]

theorem component_image_full_center
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (hnormal : (originalImage n S e K).Normal) (hodd : Odd (originalImage n S e K).index) :
    Subgroup.center (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K ∧
      (Subgroup.center (originalImage n S e K)).map (originalImage n S e K).subtype =
        Subgroup.center (centralizerOddCoreQuotient n S e) ∧
      (Subgroup.center (centralizerOddCoreQuotient n S e)).subgroupOf
        (originalImage n S e K) = Subgroup.center (originalImage n S e K) := by
  obtain ⟨_, _, _, htwo, hc⟩ := original_centralizer_layer_inputs hnonab n hn S e hfour
  let : (originalImage n S e K).Normal := hnormal
  have hAD := center_le_normal_of_odd_index (originalImage n S e K) htwo hodd
  exact ⟨hAD, center_map_eq _ _ hcover hAD hc, center_subgroupOf_eq _ _ hcover hc⟩

@[expose] def componentImageFullCenterInclusion
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    originalImageFullQuotient n S e K →*
      centralizerOddCoreQuotient n S e ⧸ Subgroup.center (centralizerOddCoreQuotient n S e) :=
  fullCenterInclusion _ _ hcover
    (original_centralizer_layer_inputs hnonab n hn S e hfour).2.2.2.2

theorem componentImageFullCenterInclusion_mk
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (d : originalImage n S e K) :
    componentImageFullCenterInclusion hnonab n hn S e hfour K hcover
        (QuotientGroup.mk' (Subgroup.center (originalImage n S e K)) d) =
      QuotientGroup.mk' (Subgroup.center (centralizerOddCoreQuotient n S e)) (d : _) := rfl

theorem component_image_full_center_layer_map
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    let i := componentImageFullCenterInclusion hnonab n hn S e hfour K hcover
    Function.Injective i ∧ (originalImageFullLayer n S e K).map i =
      CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
        Subgroup.center (centralizerOddCoreQuotient n S e)) := by
  obtain ⟨hMN, hM, _, _, hc⟩ := original_centralizer_layer_inputs hnonab n hn S e hfour
  let : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := hMN
  exact ⟨fullCenterInclusion_injective _ _ hcover hc,
    generalizedFitting_map _ _ hM hcover hc⟩

@[expose] def componentImageFullLayerEquiv
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    originalImageFullLayer n S e K ≃*
      CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
        Subgroup.center (centralizerOddCoreQuotient n S e)) :=
  ((originalImageFullLayer n S e K).equivMapOfInjective
    (componentImageFullCenterInclusion hnonab n hn S e hfour K hcover)
    (component_image_full_center_layer_map hnonab n hn S e hfour K hcover).1).trans
      (MulEquiv.subgroupCongr
        (component_image_full_center_layer_map hnonab n hn S e hfour K hcover).2)

theorem componentImageFullLayerEquiv_coe
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (a : originalImageFullLayer n S e K) :
    (componentImageFullLayerEquiv hnonab n hn S e hfour K hcover a :
        centralizerOddCoreQuotient n S e ⧸
          Subgroup.center (centralizerOddCoreQuotient n S e)) =
      componentImageFullCenterInclusion hnonab n hn S e hfour K hcover (a : _) := rfl

theorem componentImageFullLayerEquiv_symm_coe
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (a : CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e))) :
    componentImageFullCenterInclusion hnonab n hn S e hfour K hcover
        ((componentImageFullLayerEquiv hnonab n hn S e hfour K hcover).symm a : _) =
      (a : _) := by
  rw [← componentImageFullLayerEquiv_coe, MulEquiv.apply_symm_apply]

@[expose] def componentImageStatedLayerEquiv
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    originalImageFullLayer n S e K ≃* centralizerSimpleLayer n hn S e :=
  (componentImageFullLayerEquiv hnonab n hn S e hfour K hcover).trans
    (originalFullCenterLayerEquiv hnonab n hn S e hfour)

theorem componentImageStatedLayerEquiv_coe
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (a : originalImageFullLayer n S e K) :
    (componentImageStatedLayerEquiv hnonab n hn S e hfour K hcover a :
        centralizerFullQuotient n hn S e) =
      originalFullCenterQuotientEquiv n hn S e
        (componentImageFullCenterInclusion hnonab n hn S e hfour K hcover (a : _)) := by
  change (originalFullCenterLayerEquiv hnonab n hn S e hfour
    (componentImageFullLayerEquiv hnonab n hn S e hfour K hcover a) :
      centralizerFullQuotient n hn S e) = _
  rw [originalFullCenterLayerEquiv_coe, componentImageFullLayerEquiv_coe]

end CFSG.Wreathed.ComponentCoveringLocal
