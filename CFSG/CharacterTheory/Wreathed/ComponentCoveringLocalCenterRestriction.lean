module

public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalFullCenter

public noncomputable section

namespace CFSG.Wreathed.ComponentCoveringLocal

open NormalOddIndexFullCenterLayer SmallerRecognitionOriginalField

variable {G : Type} [Group G] [Finite G]

abbrev originalImageAmbientCenterQuotient (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :=
  originalImage n S e K ⧸ (Subgroup.center (centralizerOddCoreQuotient n S e)).subgroupOf
    (originalImage n S e K)

abbrev originalImageAmbientCenterLayer (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :=
  CFSG.generalizedFitting (originalImageAmbientCenterQuotient n S e K)

@[expose] def componentImageAmbientCenterInclusion (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    originalImageAmbientCenterQuotient n S e K →*
      centralizerOddCoreQuotient n S e ⧸ Subgroup.center (centralizerOddCoreQuotient n S e) :=
  quotientInclusion (originalImage n S e K)

omit [Finite G] in
theorem componentImageAmbientCenterInclusion_mk (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (d : originalImage n S e K) :
    componentImageAmbientCenterInclusion n S e K
        (QuotientGroup.mk' ((Subgroup.center (centralizerOddCoreQuotient n S e)).subgroupOf
          (originalImage n S e K)) d) =
      QuotientGroup.mk' (Subgroup.center (centralizerOddCoreQuotient n S e)) (d : _) := rfl

omit [Finite G] in
theorem componentImageAmbientCenterInclusion_injective (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    Function.Injective (componentImageAmbientCenterInclusion n S e K) :=
  quotientInclusion_injective (originalImage n S e K)

variable [IsSimpleGroup G]

@[expose] def componentImageAmbientCenterQuotientEquiv
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    originalImageAmbientCenterQuotient n S e K ≃* originalImageFullQuotient n S e K :=
  QuotientGroup.quotientMulEquivOfEq (center_subgroupOf_eq _ _ hcover
    (original_centralizer_layer_inputs hnonab n hn S e hfour).2.2.2.2)

theorem componentImageAmbientCenterQuotientEquiv_mk
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (d : originalImage n S e K) :
    componentImageAmbientCenterQuotientEquiv hnonab n hn S e hfour K hcover
        (QuotientGroup.mk' ((Subgroup.center (centralizerOddCoreQuotient n S e)).subgroupOf
          (originalImage n S e K)) d) =
      QuotientGroup.mk' (Subgroup.center (originalImage n S e K)) d := rfl

theorem componentImageAmbientCenterInclusion_eq
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    componentImageAmbientCenterInclusion n S e K =
      (componentImageFullCenterInclusion hnonab n hn S e hfour K hcover).comp
        (componentImageAmbientCenterQuotientEquiv hnonab n hn S e hfour K hcover).toMonoidHom := by
  apply MonoidHom.ext
  intro a
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective
    ((Subgroup.center (centralizerOddCoreQuotient n S e)).subgroupOf (originalImage n S e K)) a
  rfl

theorem component_image_full_layer_simple
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    IsSimpleGroup (originalImageFullLayer n S e K) ∧
      (∃ a b : originalImageFullLayer n S e K, a * b ≠ b * a) ∧
      Subgroup.centralizer (originalImageFullLayer n S e K :
        Set (originalImageFullQuotient n S e K)) = ⊥ := by
  obtain ⟨hs, hab, _⟩ := original_full_center_layer_simple hnonab n hn S e hfour
  let : IsSimpleGroup (CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
    Subgroup.center (centralizerOddCoreQuotient n S e))) := hs
  let E := componentImageFullLayerEquiv hnonab n hn S e hfour K hcover
  obtain ⟨hMN, hM, _, _, hc⟩ := original_centralizer_layer_inputs hnonab n hn S e hfour
  let : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := hMN
  exact ⟨E.isSimpleGroup, CFSG.ComponentClassification.Helpers.nonabelian_of_equiv E hab,
    local_layer_centralizer _ _ hM hcover hc⟩

@[expose] def componentImageCenterDenominatorLayerEquiv
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    originalImageFullLayer n S e K ≃* originalImageAmbientCenterLayer n S e K := by
  obtain ⟨hs, hab, hc⟩ := component_image_full_layer_simple hnonab n hn S e hfour K hcover
  let : IsSimpleGroup (originalImageFullLayer n S e K) := hs
  exact DegreeThreeModelFullCenter.generalizedFittingSimpleEquiv
    (componentImageAmbientCenterQuotientEquiv hnonab n hn S e hfour K hcover).symm hab hc

theorem componentImageCenterDenominatorLayerEquiv_coe
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (a : originalImageFullLayer n S e K) :
    (componentImageCenterDenominatorLayerEquiv hnonab n hn S e hfour K hcover a :
        originalImageAmbientCenterQuotient n S e K) =
      (componentImageAmbientCenterQuotientEquiv hnonab n hn S e hfour K hcover).symm (a : _) :=
  rfl

@[expose] def componentImageAmbientCenterLayerEquiv
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    originalImageAmbientCenterLayer n S e K ≃*
      CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
        Subgroup.center (centralizerOddCoreQuotient n S e)) :=
  (componentImageCenterDenominatorLayerEquiv hnonab n hn S e hfour K hcover).symm.trans
    (componentImageFullLayerEquiv hnonab n hn S e hfour K hcover)

theorem componentImageAmbientCenterLayerEquiv_coe
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (a : originalImageAmbientCenterLayer n S e K) :
    (componentImageAmbientCenterLayerEquiv hnonab n hn S e hfour K hcover a :
        centralizerOddCoreQuotient n S e ⧸
          Subgroup.center (centralizerOddCoreQuotient n S e)) =
      componentImageAmbientCenterInclusion n S e K (a : _) := by
  let E := componentImageAmbientCenterQuotientEquiv hnonab n hn S e hfour K hcover
  let D := componentImageCenterDenominatorLayerEquiv hnonab n hn S e hfour K hcover
  have hpre : (D.symm a : originalImageFullQuotient n S e K) = E (a : _) := by
    apply E.symm.injective
    rw [← componentImageCenterDenominatorLayerEquiv_coe, D.apply_symm_apply,
      E.symm_apply_apply]
  change (componentImageFullLayerEquiv hnonab n hn S e hfour K hcover (D.symm a) :
    centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) = _
  rw [componentImageFullLayerEquiv_coe, hpre, componentImageAmbientCenterInclusion_eq]
  rfl

theorem componentImageAmbientCenterLayerEquiv_symm_coe
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (a : CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e))) :
    componentImageAmbientCenterInclusion n S e K
        ((componentImageAmbientCenterLayerEquiv hnonab n hn S e hfour K hcover).symm a : _) =
      (a : _) := by
  let E := componentImageAmbientCenterLayerEquiv hnonab n hn S e hfour K hcover
  exact (componentImageAmbientCenterLayerEquiv_coe hnonab n hn S e hfour K hcover
    (E.symm a)).symm.trans (congrArg Subtype.val (E.apply_symm_apply a))

theorem component_image_ambient_center_generalizedFitting_map
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    (originalImageAmbientCenterLayer n S e K).map (componentImageAmbientCenterInclusion n S e K) =
      CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
        Subgroup.center (centralizerOddCoreQuotient n S e)) := by
  let E := componentImageAmbientCenterLayerEquiv hnonab n hn S e hfour K hcover
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (componentImageAmbientCenterLayerEquiv_coe hnonab n hn S e hfour K hcover
      ⟨a, ha⟩) ▸ (E ⟨a, ha⟩).property
  · intro hx
    obtain ⟨a, ha⟩ := E.surjective ⟨x, hx⟩
    refine ⟨a.val, a.property, ?_⟩
    exact (componentImageAmbientCenterLayerEquiv_coe hnonab n hn S e hfour K hcover a).symm.trans
      (congrArg Subtype.val ha)

end CFSG.Wreathed.ComponentCoveringLocal
