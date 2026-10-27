module

public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalQuotient

public noncomputable section

namespace CFSG.Wreathed.ComponentCoveringLocal

open FullSylowCoveringObstruction

universe u v

theorem symmetric_normal_odd_index_eq_top
    {α : Type u} [DecidableEq α] [Finite α]
    (D : Subgroup (Equiv.Perm α)) [D.Normal] (hodd : Odd D.index) : D = ⊤ := by
  apply top_unique
  rw [← Equiv.Perm.closure_isSwap]
  apply (Subgroup.closure_le D).mpr
  intro σ hσ
  have htwo : IsPGroup 2 (Subgroup.zpowers σ) :=
    IsPGroup.of_card (show Nat.card (Subgroup.zpowers σ) = 2 ^ 1 by
      rw [Nat.card_zpowers, Equiv.Perm.IsSwap.orderOf hσ]
      norm_num)
  exact OddIndexCentralCoreAction.two_subgroup_le_normal_of_odd_index
    D (Subgroup.zpowers σ) hodd htwo (Subgroup.mem_zpowers σ)

theorem symmetric_three_restriction_surjective
    {X : Type u} [Group X] (D : Subgroup X) [D.Normal]
    (hodd : Odd D.index) (f : X →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f) : Function.Surjective (f.comp D.subtype) := by
  let : (D.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hmap : D.map f = ⊤ := symmetric_normal_odd_index_eq_top (D.map f)
    (hodd.of_dvd_nat (Subgroup.index_map_dvd D hf))
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]

variable {G : Type} [Group G] [Finite G]

abbrev originalPreimage (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :=
  (originalImage n S e K).comap (centralizerOddCoreMap n S e)

omit [Finite G] in
theorem original_preimage_eq_kernel_sup (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    originalPreimage n S e K =
      centralizerOddCore n S e ⊔ originalCentralizerSubgroup n S e K := by
  rw [originalPreimage, originalImage, Subgroup.comap_map_eq]
  rw [show (centralizerOddCoreMap n S e).ker = centralizerOddCore n S e from
    QuotientGroup.ker_mk' _]
  exact sup_comm _ _

theorem original_preimage_quaternion_quotient_surjective [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hnormal : (originalImage n S e K).Normal)
    (hodd : Odd (originalImage n S e K).index) :
    ∀ g : Subgroup.normalizer (modelV S e : Set G),
      ∃ b : Subgroup.normalizer (modelV S e : Set G),
        centralizerOddCoreMap n S e
          ⟨(b : G), modelVNormalizer_le_involutionCentralizer n hn S e b.property⟩ ∈
            originalImage n S e K ∧
        QuotientGroup.mk' (modelVInnerCentralizer S e) b =
          QuotientGroup.mk' (modelVInnerCentralizer S e) g := by
  let D := originalPreimage n S e K
  let : (originalImage n S e K).Normal := hnormal
  let : D.Normal := inferInstance
  have hDodd : Odd D.index := by
    rw [Subgroup.index_comap_of_surjective _ (centralizerOddCoreMap_surjective n S e)]
    exact hodd
  let j := Subgroup.inclusion (modelVNormalizer_le_involutionCentralizer n hn S e)
  let E := D.comap j
  let : E.Normal := inferInstance
  have hEodd : Odd E.index := by
    rw [Subgroup.index_comap]
    exact hDodd.of_dvd_nat (Subgroup.relIndex_dvd_index_of_normal D j.range)
  obtain ⟨e3⟩ := modelVNormalizerQuotient_sym3_of_simple hnonab n hn S e
  let f := e3.toMonoidHom.comp (QuotientGroup.mk' (modelVInnerCentralizer S e))
  have hf : Function.Surjective f :=
    e3.surjective.comp (QuotientGroup.mk'_surjective _)
  have hsurj := symmetric_three_restriction_surjective E hEodd f hf
  intro g
  obtain ⟨b, hb⟩ := hsurj (f g)
  exact ⟨b, b.property, e3.injective hb⟩

theorem odd_kernel_partial_cover_preserves_normalizer_actions
    {X : Type u} [Group X] [Finite X]
    (R B V : Subgroup X) [R.Normal] (hR : Odd (Nat.card R))
    (hVB : V ≤ B) (hV : IsPGroup 2 V)
    (g : X) (hg : g ∈ Subgroup.normalizer (V : Set X)) (hgP : g ∈ R ⊔ B) :
    ∃ b ∈ B ⊓ Subgroup.normalizer (V : Set X),
      ∀ v ∈ V, b⁻¹ * v * b = g⁻¹ * v * g := by
  let P := R ⊔ B
  let Rp := R.subgroupOf P
  let Bp := B.subgroupOf P
  let Vp := V.subgroupOf P
  have hVP : V ≤ P := hVB.trans le_sup_right
  have hcover : Rp ⊔ Bp = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right, Subgroup.map_top,
      Subgroup.range_subtype]
  have hodd : Odd (Nat.card Rp) := hR.of_dvd_nat
    (Subgroup.card_comap_dvd_of_injective R P.subtype P.subtype_injective)
  let gp : P := ⟨g, hgP⟩
  have hgn : gp ∈ Subgroup.normalizer (Vp : Set P) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hVP]
    exact hg
  obtain ⟨b, hb, hact⟩ := odd_kernel_cover_preserves_two_subgroup_normalizer_actions
    Rp Bp Vp hodd hcover (Subgroup.comap_mono hVB) hV.comap_subtype gp hgn
  have hbn : (b : X) ∈ Subgroup.normalizer (V : Set X) := by
    have h := hb.2
    rw [← Subgroup.subgroupOf_normalizer_eq hVP] at h
    exact h
  exact ⟨b, ⟨hb.1, hbn⟩, fun v hv =>
    congrArg Subtype.val (hact ⟨v, hVP hv⟩ hv)⟩

theorem partial_cover_action_inside_overgroup
    (N K V : Subgroup G) (R : Subgroup N) [R.Normal]
    (hR : Odd (Nat.card R)) (hVK : V ≤ K) (hVN : V ≤ N) (hV : IsPGroup 2 V)
    (g : N) (hg : (g : G) ∈ Subgroup.normalizer (V : Set G))
    (hgP : g ∈ R ⊔ K.subgroupOf N) :
    ∃ b ∈ K ⊓ Subgroup.normalizer (V : Set G),
      ∀ v ∈ V, b⁻¹ * v * b = (g : G)⁻¹ * v * g := by
  let W := V.subgroupOf N
  have hgn : g ∈ Subgroup.normalizer (W : Set N) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hVN]
    exact hg
  obtain ⟨b, hb, hact⟩ := odd_kernel_partial_cover_preserves_normalizer_actions
    R (K.subgroupOf N) W hR (Subgroup.comap_mono hVK) hV.comap_subtype g hgn hgP
  have hbn : (b : G) ∈ Subgroup.normalizer (V : Set G) := by
    have h := hb.2
    rw [← Subgroup.subgroupOf_normalizer_eq hVN] at h
    exact h
  exact ⟨b, ⟨hb.1, hbn⟩, fun v hv =>
    congrArg Subtype.val (hact ⟨v, hVN hv⟩ hv)⟩

theorem component_subgroup_quaternion_quotient_action_range [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (hodd : Odd (originalImage n S e K).index) :
    (modelVQuotientAction (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK)).range = (modelVQuotientAction S e).range := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rw [subgroupVQuotientAction_eq]
    exact ⟨subgroupVNormalizerInclusion S e K hSK g, rfl⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨b, hb, hbq⟩ := original_preimage_quaternion_quotient_surjective
      hnonab n hn S e K hnormal hodd g
    have hVK := (modelV_le_sylow S e).trans hSK
    have hVN := (modelV_le_sylow S e).trans (sylow_le_involutionCentralizer n hn S e)
    have hV : IsPGroup 2 (modelV S e) :=
      S.isPGroup'.of_injective (Subgroup.inclusion (modelV_le_sylow S e))
        (Subgroup.inclusion_injective _)
    let bN : involutionCentralizer n S e :=
      ⟨(b : G), modelVNormalizer_le_involutionCentralizer n hn S e b.property⟩
    have hbP : bN ∈ centralizerOddCore n S e ⊔ originalCentralizerSubgroup n S e K := by
      rw [← original_preimage_eq_kernel_sup]
      exact hb
    obtain ⟨k, hk, hact⟩ := partial_cover_action_inside_overgroup
      (involutionCentralizer n S e) K (modelV S e) (centralizerOddCore n S e)
      (centralizerOddCore_card_odd n S e) hVK hVN hV bN⁻¹
      ((Subgroup.normalizer (modelV S e : Set G)).inv_mem b.property)
      ((centralizerOddCore n S e ⊔ originalCentralizerSubgroup n S e K).inv_mem hbP)
    let kK : K := ⟨k⁻¹, K.inv_mem hk.1⟩
    have hkn : kK ∈ Subgroup.normalizer (modelV (subgroupSylow S K hSK)
        (subgroupCoordinates S e K hSK) : Set K) := by
      rw [subgroupModelV_eq, ← Subgroup.subgroupOf_normalizer_eq hVK]
      exact (Subgroup.normalizer (modelV S e : Set G)).inv_mem hk.2
    let kNorm := (⟨kK, hkn⟩ : Subgroup.normalizer
      (modelV (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) : Set K))
    have haction : modelVAction (subgroupSylow S K hSK)
        (subgroupCoordinates S e K hSK) kNorm = modelVAction S e b := by
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      apply wreathModelHom_injective S e
      rw [subgroupVAction_eq, modelVAction_coe, modelVAction_coe,
        subgroupVNormalizerInclusion_coe]
      have hv : wreathModelHom S e v.val ∈ modelV S e :=
        Subgroup.mem_map_of_mem (wreathModelHom S e) v.property
      simpa only [kNorm, kK, bN, Subgroup.coe_inv, inv_inv] using hact _ hv
    have hbaction : modelVQuotientAction S e b = modelVQuotientAction S e g := by
      have h := congrArg (fun q => (modelVNormalizerQuotientEquiv n hn S e q :
        MulAut (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))))) hbq
      exact h
    refine ⟨kNorm, ?_⟩
    change (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
      (Subgroup.center (Original.V (2 ^ n))))
        (modelVAction (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) kNorm) = _
    rw [haction]
    exact hbaction

theorem component_v_quotient_sym3 [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (hodd : Odd (originalImage n S e K).index) :
    Nonempty (coveringVQuotient S e K ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e3⟩ := modelVNormalizerQuotient_sym3_of_simple hnonab n hn S e
  let erange := MulEquiv.subgroupCongr
    (component_subgroup_quaternion_quotient_action_range hnonab n hn S e K hSK hnormal hodd)
  exact ⟨(subgroupVQuotientEquiv S e K hSK).symm.trans
    ((modelVNormalizerQuotientEquiv n hn _ _).trans
      (erange.trans ((modelVNormalizerQuotientEquiv n hn S e).symm.trans e3)))⟩

theorem component_cover_v_quotient_sym3
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K) :
    Nonempty (coveringVQuotient S e K ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨hnormal, hodd⟩ := component_cover_image_normal_odd_index
    hnonab n hn S e hfour p f hp hpodd hf hmodel K hSK hcover
  exact component_v_quotient_sym3 hnonab n hn S e K hSK hnormal hodd

end CFSG.Wreathed.ComponentCoveringLocal
