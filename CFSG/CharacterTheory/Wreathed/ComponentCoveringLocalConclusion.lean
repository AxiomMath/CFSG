module

public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalAlternative
public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalAmbient
public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalCenterRestriction

public noncomputable section

namespace CFSG.Wreathed.ComponentCoveringLocal

open FullSylowCoveringObstruction SmallerRecognitionOriginalField
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

variable [IsSimpleGroup G]

@[expose] def componentImageAmbientCenterStatedLayerEquiv
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    originalImageAmbientCenterLayer n S e K ≃* centralizerSimpleLayer n hn S e :=
  (componentImageAmbientCenterLayerEquiv hnonab n hn S e hfour K hcover).trans
    (originalFullCenterLayerEquiv hnonab n hn S e hfour)

theorem componentImageAmbientCenterStatedLayerEquiv_coe
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (a : originalImageAmbientCenterLayer n S e K) :
    (componentImageAmbientCenterStatedLayerEquiv hnonab n hn S e hfour K hcover a :
        centralizerFullQuotient n hn S e) =
      originalFullCenterQuotientEquiv n hn S e
        (componentImageAmbientCenterInclusion n S e K (a : _)) := by
  change (originalFullCenterLayerEquiv hnonab n hn S e hfour
    (componentImageAmbientCenterLayerEquiv hnonab n hn S e hfour K hcover a) :
      centralizerFullQuotient n hn S e) = _
  rw [originalFullCenterLayerEquiv_coe, componentImageAmbientCenterLayerEquiv_coe]

theorem componentImageAmbientCenterStatedLayerEquiv_symm_coe
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (a : centralizerSimpleLayer n hn S e) :
    originalFullCenterQuotientEquiv n hn S e
        (componentImageAmbientCenterInclusion n S e K
          ((componentImageAmbientCenterStatedLayerEquiv hnonab n hn S e hfour K hcover).symm
            a : _)) = (a : _) := by
  let E := componentImageAmbientCenterStatedLayerEquiv hnonab n hn S e hfour K hcover
  exact (componentImageAmbientCenterStatedLayerEquiv_coe hnonab n hn S e hfour K hcover
    (E.symm a)).symm.trans (congrArg Subtype.val (E.apply_symm_apply a))

theorem componentImageAmbientCenterStatedLayerEquiv_mk
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (d : originalImage n S e K)
    (hd : QuotientGroup.mk'
      ((Subgroup.center (centralizerOddCoreQuotient n S e)).subgroupOf (originalImage n S e K))
        d ∈ originalImageAmbientCenterLayer n S e K) :
    (componentImageAmbientCenterStatedLayerEquiv hnonab n hn S e hfour K hcover
        ⟨_, hd⟩ : centralizerFullQuotient n hn S e) =
      centralizerFullQuotientMap n hn S e (d : _) := by
  rw [componentImageAmbientCenterStatedLayerEquiv_coe,
    componentImageAmbientCenterInclusion_mk, originalFullCenterQuotientEquiv_mk]

theorem componentImageAmbientCenterStatedLayerEquiv_every_inverse
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (a : centralizerSimpleLayer n hn S e) :
    ∃ d : originalImage n S e K,
      QuotientGroup.mk' ((Subgroup.center (centralizerOddCoreQuotient n S e)).subgroupOf
          (originalImage n S e K)) d =
        ((componentImageAmbientCenterStatedLayerEquiv hnonab n hn S e hfour K hcover).symm
          a : originalImageAmbientCenterQuotient n S e K) ∧
      centralizerFullQuotientMap n hn S e (d : _) = (a : _) := by
  let E := componentImageAmbientCenterStatedLayerEquiv hnonab n hn S e hfour K hcover
  obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective
    ((Subgroup.center (centralizerOddCoreQuotient n S e)).subgroupOf (originalImage n S e K))
      (E.symm a : originalImageAmbientCenterQuotient n S e K)
  refine ⟨d, hd, ?_⟩
  have ha := componentImageAmbientCenterStatedLayerEquiv_symm_coe
    hnonab n hn S e hfour K hcover a
  rw [← hd, componentImageAmbientCenterInclusion_mk, originalFullCenterQuotientEquiv_mk] at ha
  exact ha

omit [IsSimpleGroup G] in
structure ComponentCoveringLocalConclusion (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) : Prop where
  actual_intersection : originalAmbientCentralizerSubgroup n S e K =
    (Subgroup.centralizer ({coveringInvolution n S e K hSK} : Set K)).map K.subtype
  image_normal : (originalImage n S e K).Normal
  image_odd_index : Odd (originalImage n S e K).index
  image_sylow : (centralizerOddCoreSylow n hn S e :
    Subgroup (centralizerOddCoreQuotient n S e)) ≤ originalImage n S e K
  derived_eq_layer : commutator (centralizerOddCoreQuotient n S e) =
    CFSG.layer (centralizerOddCoreQuotient n S e)
  odd_core : CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K) =
    ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype).subgroupOf
      (originalAmbientCentralizerSubgroup n S e K)
  ambient_odd_core : (CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K)).map
      (originalAmbientCentralizerSubgroup n S e K).subtype =
    (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
      originalAmbientCentralizerSubgroup n S e K
  inclusion_quotient :
    ∃ E : originalAmbientCentralizerSubgroup n S e K ⧸
        CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K) ≃* originalImage n S e K,
      (∀ b : originalAmbientCentralizerSubgroup n S e K,
        E (QuotientGroup.mk' (CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K)) b) =
          ambientOriginalImageMap n S e K b ∧
        (E (QuotientGroup.mk' (CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K)) b) :
            centralizerOddCoreQuotient n S e) =
          centralizerOddCoreMap n S e (Subgroup.inclusion inf_le_right b)) ∧
      (∀ b : originalAmbientCentralizerSubgroup n S e K,
        E.symm (ambientOriginalImageMap n S e K b) =
          QuotientGroup.mk' (CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K)) b) ∧
      (∀ d : originalImage n S e K, ∃ b : originalAmbientCentralizerSubgroup n S e K,
        ambientOriginalImageMap n S e K b = d ∧
        E.symm d = QuotientGroup.mk'
          (CFSG.oddCore (originalAmbientCentralizerSubgroup n S e K)) b)
  ambient_center_le : Subgroup.center (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K
  image_center : (Subgroup.center (originalImage n S e K)).map
      (originalImage n S e K).subtype = Subgroup.center (centralizerOddCoreQuotient n S e)
  center_denominator : (Subgroup.center (centralizerOddCoreQuotient n S e)).subgroupOf
      (originalImage n S e K) = Subgroup.center (originalImage n S e K)
  center_inclusion_injective : Function.Injective (componentImageAmbientCenterInclusion n S e K)
  center_inclusion_mk : ∀ d : originalImage n S e K,
    componentImageAmbientCenterInclusion n S e K
        (QuotientGroup.mk' ((Subgroup.center (centralizerOddCoreQuotient n S e)).subgroupOf
          (originalImage n S e K)) d) =
      QuotientGroup.mk' (Subgroup.center (centralizerOddCoreQuotient n S e)) (d : _)
  generalizedFitting_image : (originalImageAmbientCenterLayer n S e K).map
      (componentImageAmbientCenterInclusion n S e K) =
    CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e))
  inclusion_layer :
    ∃ E : originalImageAmbientCenterLayer n S e K ≃*
        CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
          Subgroup.center (centralizerOddCoreQuotient n S e)),
      (∀ a : originalImageAmbientCenterLayer n S e K,
        (E a : _) = componentImageAmbientCenterInclusion n S e K (a : _)) ∧
      (∀ a : CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
          Subgroup.center (centralizerOddCoreQuotient n S e)),
        componentImageAmbientCenterInclusion n S e K (E.symm a : _) = (a : _))
  original_stated_layer :
    ∃ E : originalImageAmbientCenterLayer n S e K ≃* centralizerSimpleLayer n hn S e,
      (∀ a : originalImageAmbientCenterLayer n S e K,
        (E a : centralizerFullQuotient n hn S e) = originalFullCenterQuotientEquiv n hn S e
          (componentImageAmbientCenterInclusion n S e K (a : _))) ∧
      (∀ a : centralizerSimpleLayer n hn S e,
        originalFullCenterQuotientEquiv n hn S e
          (componentImageAmbientCenterInclusion n S e K (E.symm a : _)) = (a : _)) ∧
      (∀ a : centralizerSimpleLayer n hn S e, ∃ d : originalImage n S e K,
        QuotientGroup.mk' ((Subgroup.center (centralizerOddCoreQuotient n S e)).subgroupOf
            (originalImage n S e K)) d =
          (E.symm a : originalImageAmbientCenterQuotient n S e K) ∧
        centralizerFullQuotientMap n hn S e (d : _) = (a : _))
  v_denominator_product :
    (((modelV S e).subgroupOf K ⊔
      Subgroup.centralizer ((modelV S e).subgroupOf K : Set K) : Subgroup K) : Set K) =
    ((modelV S e).subgroupOf K : Set K) *
      (Subgroup.centralizer ((modelV S e).subgroupOf K : Set K) : Set K)
  v_sym3 : Nonempty (coveringVQuotient S e K ≃* Equiv.Perm (Fin 3))
  alternatives : CoveringFactorizationBranch n S e K hSK ∨ CoveringTypeIObstruction n S e K
  mutually_exclusive :
    ¬ (CoveringFactorizationBranch n S e K hSK ∧ CoveringTypeIObstruction n S e K)

theorem component_covering_full_Sylow_subgroup_local_layer_and_fusion_alternative
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    ComponentCoveringLocalConclusion n hn S e K hSK := by
  obtain ⟨hN, hodd⟩ := component_cover_image_normal_odd_index
    hnonab n hn S e hfour p f hp hpodd hf hmodel K hSK hcover
  have hc := component_image_full_center hnonab n hn S e hfour K hcover hN hodd
  obtain ⟨halt, hexclusive⟩ := component_cover_full_alternatives
    hnonab n hn S e hfour p f hp hpodd hf hmodel K hSK hcover
  refine {
    actual_intersection := covering_intersection_eq_centralizer n S e K hSK
    image_normal := hN
    image_odd_index := hodd
    image_sylow := original_quotient_sylow_le_image n hn S e K hSK
    derived_eq_layer := original_derived_eq_layer hnonab n hn S e hfour p f hp hpodd hf hmodel
    odd_core := ambient_original_centralizer_odd_core_eq_kernel n S e K hN
    ambient_odd_core := ambient_original_centralizer_odd_core_map n S e K hN
    inclusion_quotient := ?_
    ambient_center_le := hc.1
    image_center := hc.2.1
    center_denominator := hc.2.2
    center_inclusion_injective := componentImageAmbientCenterInclusion_injective n S e K
    center_inclusion_mk := componentImageAmbientCenterInclusion_mk n S e K
    generalizedFitting_image :=
      component_image_ambient_center_generalizedFitting_map hnonab n hn S e hfour K hcover
    inclusion_layer := ⟨componentImageAmbientCenterLayerEquiv hnonab n hn S e hfour K hcover,
      componentImageAmbientCenterLayerEquiv_coe hnonab n hn S e hfour K hcover,
      componentImageAmbientCenterLayerEquiv_symm_coe hnonab n hn S e hfour K hcover⟩
    original_stated_layer :=
      ⟨componentImageAmbientCenterStatedLayerEquiv hnonab n hn S e hfour K hcover,
        componentImageAmbientCenterStatedLayerEquiv_coe hnonab n hn S e hfour K hcover,
        componentImageAmbientCenterStatedLayerEquiv_symm_coe hnonab n hn S e hfour K hcover,
        componentImageAmbientCenterStatedLayerEquiv_every_inverse
          hnonab n hn S e hfour K hcover⟩
    v_denominator_product := covering_v_denominator_product S e K
    v_sym3 := component_v_quotient_sym3 hnonab n hn S e K hSK hN hodd
    alternatives := halt
    mutually_exclusive := hexclusive }
  refine ⟨ambientOriginalCoreQuotientEquiv n S e K hN, ?_,
    ambientOriginalCoreQuotientEquiv_symm_map n S e K hN,
    ambientOriginalCoreQuotientEquiv_every_inverse n S e K hN⟩
  intro b
  have hb := ambientOriginalCoreQuotientEquiv_mk n S e K hN b
  exact ⟨hb, (congrArg Subtype.val hb).trans (ambientOriginalImageMap_coe n S e K b)⟩

end CFSG.Wreathed.ComponentCoveringLocal
