module

public import CFSG.CharacterTheory.Wreathed.FullCenterOddCore
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public noncomputable section
open scoped Classical Pointwise commutatorElement
namespace CFSG.Wreathed.FullSylowCoveringObstruction
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem normalizer_map_of_surjective_coprime_kernel [Finite G]
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (V : Subgroup G) (hV : IsPGroup p V)
    (hcop : Nat.Coprime p (Nat.card f.ker)) :
    Subgroup.normalizer (V.map f : Set H) =
      (Subgroup.normalizer (V : Set G)).map f := by
  let q := QuotientGroup.mk' f.ker
  let E := QuotientGroup.quotientKerEquivOfSurjective f hf
  let : Fact (IsPGroup p V) := ⟨hV⟩
  have hcomp : E.toMonoidHom.comp q = f := by
    ext x
    rfl
  calc
    Subgroup.normalizer (V.map f : Set H) =
        Subgroup.normalizer ((V.map q).map E.toMonoidHom : Set H) := by
      rw [Subgroup.map_map, hcomp]
    _ = (Subgroup.normalizer (V.map q : Set (G ⧸ f.ker))).map E.toMonoidHom :=
      (Subgroup.map_equiv_normalizer_eq (V.map q) E).symm
    _ = ((Subgroup.normalizer (V : Set G)).map q).map E.toMonoidHom := by
      rw [CFSG.normalizer_map_quotient_eq_map_normalizer p V f.ker inferInstance hcop]
    _ = (Subgroup.normalizer (V : Set G)).map f := by
      rw [Subgroup.map_map, hcomp]

theorem covering_quotient_restriction_surjective
    (R B : Subgroup G) [R.Normal] (hcover : R ⊔ B = ⊤) :
    Function.Surjective ((QuotientGroup.mk' R).comp B.subtype) := by
  let q := QuotientGroup.mk' R
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R y
  have hg : g ∈ B ⊔ R := by
    rw [sup_comm, hcover]
    exact Subgroup.mem_top g
  obtain ⟨b, hb, r, hr, hbr⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  refine ⟨⟨b, hb⟩, ?_⟩
  change q b = q g
  have hqr : q r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  rw [← hbr, map_mul, hqr, mul_one]

theorem odd_quotient_injective_on_two_subgroup [Finite G]
    (R V : Subgroup G) [R.Normal] (hR : Odd (Nat.card R))
    (hV : IsPGroup 2 V) :
    Function.Injective ((QuotientGroup.mk' R).comp V.subtype) := by
  let q := (QuotientGroup.mk' R).comp V.subtype
  have hcop : Nat.Coprime (Nat.card V) (Nat.card R) := by
    obtain ⟨n, hn⟩ := hV.exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr hR).pow_left n
  have hd : Disjoint V R := Subgroup.disjoint_of_coprime_natCard hcop
  apply q.ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro x hx
  have hxR : (x : G) ∈ R := (QuotientGroup.eq_one_iff (x : G)).mp hx
  exact Subtype.ext (Subgroup.disjoint_def.mp hd x.property hxR)


theorem odd_kernel_cover_preserves_two_subgroup_normalizer_actions [Finite G]
    (R B V : Subgroup G) [R.Normal] (hR : Odd (Nat.card R))
    (hcover : R ⊔ B = ⊤) (hVB : V ≤ B) (hV : IsPGroup 2 V)
    (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    ∃ b ∈ B ⊓ Subgroup.normalizer (V : Set G),
      ∀ x ∈ V, b⁻¹ * x * b = g⁻¹ * x * g := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := QuotientGroup.mk' R
  let f := q.comp B.subtype
  let W := V.subgroupOf B
  have hf : Function.Surjective f := covering_quotient_restriction_surjective R B hcover
  have hker : f.ker = R.subgroupOf B := by
    ext b
    exact QuotientGroup.eq_one_iff (b : G)
  have hoddker : Odd (Nat.card f.ker) := by
    rw [hker]
    exact hR.of_dvd_nat (Subgroup.card_comap_dvd_of_injective R B.subtype
      B.subtype_injective)
  have hmap : W.map f = V.map q := by
    change (V.subgroupOf B).map (q.comp B.subtype) = V.map q
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hVB]
  have hnorm := normalizer_map_of_surjective_coprime_kernel 2 f hf W
    hV.comap_subtype (Nat.coprime_two_left.mpr hoddker)
  rw [hmap] at hnorm
  have hqg : q g ∈ Subgroup.normalizer (V.map q : Set (G ⧸ R)) :=
    Subgroup.le_normalizer_map q (Subgroup.mem_map_of_mem q hg)
  rw [hnorm] at hqg
  obtain ⟨b, hb, hbg⟩ := Subgroup.mem_map.mp hqg
  have hbn : (b : G) ∈ Subgroup.normalizer (V : Set G) := by
    have hnormalizer : (Subgroup.normalizer (V : Set G)).subgroupOf B =
        Subgroup.normalizer (W : Set B) := by
      exact Subgroup.comap_normalizer_eq_of_le_range
        (hVB.trans_eq B.range_subtype.symm)
    rw [← hnormalizer] at hb
    exact hb
  refine ⟨b, ⟨b.property, hbn⟩, ?_⟩
  intro x hx
  have hbx : (b : G)⁻¹ * x * b ∈ V :=
    (Subgroup.mem_normalizer_iff''.mp hbn x).mp hx
  have hgx : g⁻¹ * x * g ∈ V :=
    (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
  have heq : q ((b : G)⁻¹ * x * b) = q (g⁻¹ * x * g) := by
    change q (b : G) = q g at hbg
    simp only [map_mul, map_inv, hbg]
  have hinj := odd_quotient_injective_on_two_subgroup R V hR hV
  exact congrArg Subtype.val (hinj (show ((q.comp V.subtype)
    ⟨(b : G)⁻¹ * x * b, hbx⟩) = ((q.comp V.subtype) ⟨g⁻¹ * x * g, hgx⟩) from heq))


@[expose] def internalNormalizerAction (B V : Subgroup G) :
    ↥(B ⊓ Subgroup.normalizer (V : Set G)) →* MulAut V :=
  V.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)

theorem odd_kernel_cover_normalizer_action_range [Finite G]
    (R B V : Subgroup G) [R.Normal] (hR : Odd (Nat.card R))
    (hcover : R ⊔ B = ⊤) (hVB : V ≤ B) (hV : IsPGroup 2 V) :
    (internalNormalizerAction B V).range = V.normalizerMonoidHom.range := by
  apply le_antisymm
  · rintro _ ⟨b, rfl⟩
    exact ⟨Subgroup.inclusion inf_le_right b, rfl⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨b, hb, haction⟩ := odd_kernel_cover_preserves_two_subgroup_normalizer_actions
      R B V hR hcover hVB hV (g : G)⁻¹
      ((Subgroup.normalizer (V : Set G)).inv_mem g.property)
    refine ⟨⟨b⁻¹, (B ⊓ Subgroup.normalizer (V : Set G)).inv_mem hb⟩, ?_⟩
    ext x
    change b⁻¹ * (x : G) * (b⁻¹)⁻¹ = (g : G) * (x : G) * (g : G)⁻¹
    simpa only [inv_inv] using haction x x.property

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

theorem covering_odd_core_eq_kernel_intersection [Finite G]
    (B : Subgroup G) (hcover : CFSG.oddCore G ⊔ B = ⊤) :
    CFSG.oddCore B = (CFSG.oddCore G).subgroupOf B := by
  let R := CFSG.oddCore G
  let q := QuotientGroup.mk' R
  let f := q.comp B.subtype
  have hf : Function.Surjective f := covering_quotient_restriction_surjective R B hcover
  have hcorefree : CFSG.oddCore (G ⧸ R) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree G
  have hnormal : ((CFSG.oddCore B).map f).Normal :=
    Subgroup.Normal.map inferInstance f hf
  have hodd : Odd (Nat.card ((CFSG.oddCore B).map f)) :=
    (CFSG.ComponentClassification.OddCore.odd_card B).of_dvd_nat
      (Subgroup.card_map_dvd (CFSG.oddCore B) f)
  have hle : (CFSG.oddCore B).map f ≤ CFSG.oddCore (G ⧸ R) := le_sSup ⟨hnormal, hodd⟩
  have hbot : (CFSG.oddCore B).map f = ⊥ := le_antisymm (hle.trans_eq hcorefree) bot_le
  have hker : f.ker = R.subgroupOf B := by
    ext b
    exact QuotientGroup.eq_one_iff (b : G)
  apply le_antisymm
  · have h := (Subgroup.map_eq_bot_iff (CFSG.oddCore B)).mp hbot
    rwa [hker] at h
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    exact (CFSG.ComponentClassification.OddCore.odd_card G).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective R B.subtype B.subtype_injective)

theorem covering_odd_core_quotient_equiv [Finite G]
    (B : Subgroup G) (hcover : CFSG.oddCore G ⊔ B = ⊤) :
    ∃ E : B ⧸ CFSG.oddCore B ≃* G ⧸ CFSG.oddCore G,
      ∀ b : B, E ((QuotientGroup.mk' (CFSG.oddCore B)) b) =
        (QuotientGroup.mk' (CFSG.oddCore G)) b := by
  let f := (QuotientGroup.mk' (CFSG.oddCore G)).comp B.subtype
  have hf : Function.Surjective f :=
    covering_quotient_restriction_surjective (CFSG.oddCore G) B hcover
  have hker : f.ker = CFSG.oddCore B := by
    rw [covering_odd_core_eq_kernel_intersection B hcover]
    ext b
    exact QuotientGroup.eq_one_iff (b : G)
  let E := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨E, ?_⟩
  intro b
  rfl

@[expose] def subgroupSylow (S : Sylow 2 G) (K : Subgroup G)
    (hSK : (S : Subgroup G) ≤ K) : Sylow 2 K := S.subtype hSK

@[expose] def subgroupCoordinates {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) : subgroupSylow S K hSK ≃* Wreath m :=
  (Subgroup.subgroupOfEquivOfLe hSK).trans e

theorem subgroupModelHom_comp {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    K.subtype.comp (wreathModelHom (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK)) = wreathModelHom S e := rfl

theorem subgroupModelV_eq {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    modelV (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) =
      (modelV S e).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [modelV, Subgroup.map_map, subgroupModelHom_comp,
    Subgroup.map_subgroupOf_eq_of_le ((modelV_le_sylow S e).trans hSK)]
  rfl

theorem subgroupModelBase_eq {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    modelBase (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) =
      (modelBase S e).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [modelBase, Subgroup.map_map, subgroupModelHom_comp,
    Subgroup.map_subgroupOf_eq_of_le ((modelBase_le_sylow S e).trans hSK)]
  rfl

theorem covering_action_inside_overgroup [Finite G]
    (N K V : Subgroup G) (R : Subgroup N) [R.Normal]
    (hR : Odd (Nat.card R)) (hcover : R ⊔ K.subgroupOf N = ⊤)
    (hVK : V ≤ K) (hVN : V ≤ N) (hV : IsPGroup 2 V)
    (hNV : Subgroup.normalizer (V : Set G) ≤ N)
    (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    ∃ b ∈ K ⊓ Subgroup.normalizer (V : Set G),
      ∀ v ∈ V, b⁻¹ * v * b = g⁻¹ * v * g := by
  let W := V.subgroupOf N
  let B := K.subgroupOf N
  let gN : N := ⟨g, hNV hg⟩
  have hgn : gN ∈ Subgroup.normalizer (W : Set N) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hVN]
    exact hg
  have hWB : W ≤ B := Subgroup.comap_mono hVK
  obtain ⟨b, hb, hact⟩ := odd_kernel_cover_preserves_two_subgroup_normalizer_actions
    R B W hR hcover hWB hV.comap_subtype gN hgn
  have hbn : (b : G) ∈ Subgroup.normalizer (V : Set G) := by
    have ht := hb.2
    rw [← Subgroup.subgroupOf_normalizer_eq hVN] at ht
    exact ht
  refine ⟨b, ⟨hb.1, hbn⟩, ?_⟩
  intro v hv
  exact congrArg Subtype.val (hact ⟨v, hVN hv⟩ hv)


theorem modelCenter_weakly_closed_of_base_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2) :
    ∀ a ∈ modelCenter S e, ∀ g : G,
      g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g = a := by
  rintro a ⟨w, hw, rfl⟩ g hg
  let P := Subgroup.zpowers (wreathModelHom S e w)
  have hwP : wreathModelHom S e w ∈ P := Subgroup.mem_zpowers _
  have hPS : P ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr (e.symm w).property
  have hgP : rightConjugate P g ≤ (S : Subgroup G) := by
    rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
    apply Subgroup.zpowers_le.mpr
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hg
  obtain ⟨h, hchain, _, hhg⟩ := wreathed_fusion_decomposition S n hn e P hPS g hgP
  have hfix := wreathedFusionDecomposition_fixes_original_center_of_base_order_two
    n hn S e hcard P w hw hwP hchain
  exact (hhg _ hwP).symm.trans hfix

theorem base_order_two_original_involution_factorization [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2) :
    CFSG.oddCore G ⊔ involutionCentralizer n S e = ⊤ ∧
      (QuotientGroup.mk' (CFSG.oddCore G))
        (wreathModelHom S e (Original.x (2 ^ n))) ∈
          Subgroup.center (G ⧸ CFSG.oddCore G) := by
  let A := modelCenter S e
  let : IsCyclic A := by
    change IsCyclic ((Subgroup.zpowers (Original.a (2 ^ n))).map (wreathModelHom S e))
    rw [MonoidHom.map_zpowers]
    infer_instance
  have hAS : A ≤ (S : Subgroup G) := by
    rintro _ ⟨w, _, rfl⟩
    exact (e.symm w).property
  have hAC : A ≤ Subgroup.centralizer (S : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    have hfix := model_center_sylow_conjugation n hn S e w hw s hs
    calc
      s * wreathModelHom S e w = s * (s⁻¹ * wreathModelHom S e w * s) := by rw [hfix]
      _ = wreathModelHom S e w * s := by group
  have hfull := cyclic_weakly_closed_central_sylow_subgroup_central_mod_odd_core
    S A hAS hAC (modelCenter_weakly_closed_of_base_order_two n hn S e hcard)
  have hxA : wreathModelHom S e (Original.x (2 ^ n)) ∈ A :=
    Subgroup.mem_map_of_mem (wreathModelHom S e)
      ((Original.Z _).pow_mem (Subgroup.mem_zpowers _) _)
  refine ⟨?_, hfull.1 (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.oddCore G)) hxA)⟩
  apply (Subgroup.eq_top_iff' _).mpr
  intro g
  obtain ⟨r, hr, c, hc, hrc⟩ := hfull.2 g
  rw [hrc]
  have hcN : c ∈ involutionCentralizer n S e :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hc) _ hxA).symm
  exact Subgroup.mul_mem_sup hr hcN

@[expose] def subgroupVNormalizerInclusion {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    Subgroup.normalizer (modelV (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) : Set K) →*
      Subgroup.normalizer (modelV S e : Set G) where
  toFun g := ⟨g.val.val, by
    have hnorm : Subgroup.normalizer (modelV (subgroupSylow S K hSK)
        (subgroupCoordinates S e K hSK) : Set K) =
        (Subgroup.normalizer (modelV S e : Set G)).subgroupOf K := by
      rw [subgroupModelV_eq, ← Subgroup.subgroupOf_normalizer_eq
        ((modelV_le_sylow S e).trans hSK)]
    exact hnorm.le g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem subgroupVNormalizerInclusion_coe {m : ℕ} (S : Sylow 2 G)
    (e : S ≃* Wreath m) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (g : Subgroup.normalizer (modelV (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) : Set K)) :
    (subgroupVNormalizerInclusion S e K hSK g).val = g.val.val := rfl

theorem subgroupVAction_eq {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (g : Subgroup.normalizer (modelV (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) : Set K)) :
    modelVAction (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) g =
      modelVAction S e (subgroupVNormalizerInclusion S e K hSK g) := by
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  apply wreathModelHom_injective S e
  have hleft := congrArg K.subtype
    (modelVAction_coe (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) g v)
  rw [map_mul, map_mul, map_inv] at hleft
  change wreathModelHom S e
      (modelVAction (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) g v).val =
    g.val.val * wreathModelHom S e v.val * g.val.val⁻¹ at hleft
  rw [modelVAction_coe, subgroupVNormalizerInclusion_coe]
  exact hleft

theorem subgroupVQuotientAction_eq {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    modelVQuotientAction (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) =
      (modelVQuotientAction S e).comp (subgroupVNormalizerInclusion S e K hSK) := by
  apply MonoidHom.ext
  intro g
  change CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
    (Subgroup.center (Original.V m))
    (modelVAction (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) g) = _
  rw [subgroupVAction_eq]
  rfl

theorem covering_subgroupVAction_range [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔
      K.subgroupOf (involutionCentralizer n S e) = ⊤) :
    (modelVAction (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK)).range =
      (modelVAction S e).range := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact ⟨subgroupVNormalizerInclusion S e K hSK g, (subgroupVAction_eq S e K hSK g).symm⟩
  · rintro _ ⟨g, rfl⟩
    have hVK := (modelV_le_sylow S e).trans hSK
    have hVN := (modelV_le_sylow S e).trans (sylow_le_involutionCentralizer n hn S e)
    have hV : IsPGroup 2 (modelV S e) :=
      S.isPGroup'.of_injective (Subgroup.inclusion (modelV_le_sylow S e))
        (Subgroup.inclusion_injective _)
    obtain ⟨b, hb, hact⟩ := covering_action_inside_overgroup
      (involutionCentralizer n S e) K (modelV S e) (centralizerOddCore n S e)
      (centralizerOddCore_card_odd n S e) hcover hVK hVN hV
      (modelVNormalizer_le_involutionCentralizer n hn S e) (g : G)⁻¹
      ((Subgroup.normalizer (modelV S e : Set G)).inv_mem g.property)
    let bK : K := ⟨b⁻¹, K.inv_mem hb.1⟩
    have hbn : bK ∈ Subgroup.normalizer (modelV (subgroupSylow S K hSK)
        (subgroupCoordinates S e K hSK) : Set K) := by
      rw [subgroupModelV_eq, ← Subgroup.subgroupOf_normalizer_eq hVK]
      exact (Subgroup.normalizer (modelV S e : Set G)).inv_mem hb.2
    refine ⟨⟨bK, hbn⟩, ?_⟩
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    apply wreathModelHom_injective S e
    rw [subgroupVAction_eq, modelVAction_coe, modelVAction_coe,
      subgroupVNormalizerInclusion_coe]
    have hv : wreathModelHom S e v.val ∈ modelV S e :=
      Subgroup.mem_map_of_mem (wreathModelHom S e) v.property
    simpa only [bK, inv_inv] using hact _ hv

theorem covering_subgroupVQuotientAction_range [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔
      K.subgroupOf (involutionCentralizer n S e) = ⊤) :
    (modelVQuotientAction (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK)).range = (modelVQuotientAction S e).range := by
  change ((CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
      (Subgroup.center (Original.V (2 ^ n)))).comp
      (modelVAction (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK))).range = _
  rw [MonoidHom.range_comp, covering_subgroupVAction_range n hn S e K hSK hcover]
  exact (MonoidHom.range_comp _ _).symm

theorem covering_subgroupVNormalizerQuotient_sym3 [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔
      K.subgroupOf (involutionCentralizer n S e) = ⊤) :
    Nonempty (Subgroup.normalizer (modelV (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) : Set K) ⧸
      modelVInnerCentralizer (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) ≃*
        Equiv.Perm (Fin 3)) := by
  obtain ⟨e3⟩ := modelVNormalizerQuotient_sym3_of_simple hnonab n hn S e
  exact ⟨(modelVNormalizerQuotientEquiv n hn _ _).trans
    ((MulEquiv.subgroupCongr
      (covering_subgroupVQuotientAction_range n hn S e K hSK hcover)).trans
      ((modelVNormalizerQuotientEquiv n hn S e).symm.trans e3))⟩

theorem differences_eq_top_of_frattini_quotient
    {P : Type u} [Group P] [Finite P] {p : ℕ}
    (hP : IsPGroup p P) (a : MulAut P)
    (hsurj : Function.Surjective (fun x : P =>
      (QuotientGroup.mk' (frattini P)) (a x * x⁻¹))) :
    CFSG.Wreathed.automorphismDifferences a = ⊤ := by
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let D := CFSG.Wreathed.automorphismDifferences a
  have htop : D ⊔ frattini P = ⊤ := by
    apply (Subgroup.eq_top_iff' _).mpr
    intro x
    obtain ⟨y, hy⟩ := hsurj ((QuotientGroup.mk' (frattini P)) x)
    have hphi : x / (a y * y⁻¹) ∈ frattini P := QuotientGroup.eq_iff_div_mem.mp hy.symm
    have hd : a y * y⁻¹ ∈ D := Subgroup.subset_closure ⟨y, rfl⟩
    have h := (D ⊔ frattini P).mul_mem
      (Subgroup.mem_sup_right hphi) (Subgroup.mem_sup_left hd)
    simpa only [div_mul_cancel] using h
  exact frattini_nongenerating htop

theorem base_differences_eq_top (n : ℕ) (hn : 1 ≤ n)
    (a : MulAut (baseSubgroup (2 ^ n)))
    (hthree : orderOf (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
      (baseSubgroup (2 ^ n)) a) = 3) :
    automorphismDifferences a = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsKleinFour (baseSubgroup (2 ^ n) ⧸ frattini (baseSubgroup (2 ^ n))) :=
    base_frattini_quotient_isKleinFour n hn
  apply differences_eq_top_of_frattini_quotient
    ((wreath_isPGroup n).to_subgroup (baseSubgroup (2 ^ n))) a
  intro x
  obtain ⟨y, hy⟩ := kleinFour_order_three_difference_surjective
    (baseSubgroup (2 ^ n) ⧸ frattini (baseSubgroup (2 ^ n)))
    (CFSG.LargeEvenClassification.Helpers.frattiniAutAction (baseSubgroup (2 ^ n)) a)
    hthree x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (frattini (baseSubgroup (2 ^ n))) y
  refine ⟨b, ?_⟩
  change (QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n)))) (a b) *
    ((QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n)))) b)⁻¹ = x at hy
  simpa only [map_mul, map_inv] using hy


variable {G : Type u} [Group G]

theorem modelBase_le_commutator_of_reduced_order_three
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelBase S e : Set G))
    (hthree : orderOf (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
      (baseSubgroup (2 ^ n)) (modelBaseAction S e g)) = 3) :
    modelBase S e ≤ commutator G := by
  let a := modelBaseAction S e g
  let f := (wreathModelHom S e).comp (baseSubgroup (2 ^ n)).subtype
  have hgen : automorphismDifferences a ≤ (commutator G).comap f := by
    rw [automorphismDifferences, Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    change f (a b * b⁻¹) ∈ commutator G
    rw [map_mul, map_inv]
    change wreathModelHom S e (a b).val * (wreathModelHom S e b.val)⁻¹ ∈ _
    rw [modelBaseAction_coe]
    change ⁅(g : G), wreathModelHom S e b.val⁆ ∈ commutator G
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [base_differences_eq_top n hn a hthree] at hgen
  rintro _ ⟨b, hb, rfl⟩
  exact hgen (Subgroup.mem_top (⟨b, hb⟩ : baseSubgroup (2 ^ n)))

theorem modelBase_le_commutator_of_sym3 [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3))) :
    modelBase S e ≤ commutator G := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨esix⟩ := hsix
  let er := (modelBaseNormalizerQuotientEquiv S e).symm.trans esix
  have hcard : Nat.card (modelBaseAction S e).range = 6 := by
    rw [Nat.card_congr er.toEquiv, Nat.card_perm]
    norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := (modelBaseAction S e).range) 3
    (by rw [hcard]; norm_num)
  obtain ⟨g, hg⟩ := a.property
  let red := (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
    (baseSubgroup (2 ^ n))).domRestrict (modelBaseAction S e).range
  have hred : orderOf (red a) = 3 := by
    rw [orderOf_injective red (modelBaseAction_range_reduction_injective n hn S e)]
    exact ha
  apply modelBase_le_commutator_of_reduced_order_three n hn S e g
  change orderOf (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
    (baseSubgroup (2 ^ n)) (a : MulAut _)) = 3 at hred
  simpa only [← hg] using hred

def intersectionInclusionEquiv (K N : Subgroup G) :
    K.subgroupOf N ≃* N.subgroupOf K where
  toFun b := ⟨⟨b.val.val, b.property⟩, b.val.property⟩
  invFun b := ⟨⟨b.val.val, b.property⟩, b.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem intersection_odd_core_mem_iff {K N : Subgroup G}
    {b : K.subgroupOf N} :
    b ∈ CFSG.oddCore (K.subgroupOf N) ↔
      intersectionInclusionEquiv K N b ∈ CFSG.oddCore (N.subgroupOf K) := by
  have h : (CFSG.oddCore (K.subgroupOf N)).map
      (intersectionInclusionEquiv K N).toMonoidHom = CFSG.oddCore (N.subgroupOf K) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant (intersectionInclusionEquiv K N)
  rw [← h]
  exact Subgroup.mem_map_iff_mem (intersectionInclusionEquiv K N).injective |>.symm

theorem covering_factorization_core_intersection [Finite G] (K N : Subgroup G)
    (hN : CFSG.oddCore N ⊔ K.subgroupOf N = ⊤)
    (hK : CFSG.oddCore K ⊔ N.subgroupOf K = ⊤) :
    (CFSG.oddCore K).map K.subtype ⊓ N = (CFSG.oddCore N).map N.subtype ⊓ K := by
  have hcoreN := covering_odd_core_eq_kernel_intersection (K.subgroupOf N) hN
  have hcoreK := covering_odd_core_eq_kernel_intersection (N.subgroupOf K) hK
  ext g
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hn⟩
    let b : K.subgroupOf N := ⟨⟨k.val, hn⟩, k.property⟩
    have hmem : intersectionInclusionEquiv K N b ∈ CFSG.oddCore (N.subgroupOf K) := by
      rw [hcoreK]
      exact hk
    have hb := (intersection_odd_core_mem_iff (K := K) (N := N) (b := b)).mpr hmem
    rw [hcoreN] at hb
    exact ⟨⟨b.val, hb, rfl⟩, k.property⟩
  · rintro ⟨⟨v, hv, rfl⟩, hk⟩
    let b : K.subgroupOf N := ⟨v, hk⟩
    have hb : b ∈ CFSG.oddCore (K.subgroupOf N) := by
      rw [hcoreN]
      exact hv
    have hmem := (intersection_odd_core_mem_iff (K := K) (N := N) (b := b)).mp hb
    rw [hcoreK] at hmem
    exact ⟨⟨(intersectionInclusionEquiv K N b).val, hmem, rfl⟩, v.property⟩

theorem subgroupInvolutionCentralizer_eq (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    involutionCentralizer n (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) =
      (involutionCentralizer n S e).subgroupOf K := by
  ext k
  change k ∈ Subgroup.centralizer ({(wreathModelHom (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) (Original.x (2 ^ n)))} : Set K) ↔
    k.val ∈ Subgroup.centralizer ({(wreathModelHom S e (Original.x (2 ^ n)))} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem covering_base_order_two_core_intersection [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (hcard : Nat.card (Subgroup.normalizer (modelBase (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) : Set K) ⧸
      (Subgroup.centralizer (modelBase (subgroupSylow S K hSK)
        (subgroupCoordinates S e K hSK) : Set K)).subgroupOf
        (Subgroup.normalizer (modelBase (subgroupSylow S K hSK)
          (subgroupCoordinates S e K hSK) : Set K))) = 2) :
    (CFSG.oddCore K).map K.subtype ⊓ involutionCentralizer n S e =
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓ K := by
  have hK := (base_order_two_original_involution_factorization n hn
    (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) hcard).1
  rw [subgroupInvolutionCentralizer_eq] at hK
  exact covering_factorization_core_intersection K (involutionCentralizer n S e) hcover hK

def ambientIntersectionEquiv (K N : Subgroup G) : ↥(K ⊓ N) ≃* K.subgroupOf N where
  toFun b := ⟨⟨b.val, b.property.2⟩, b.property.1⟩
  invFun b := ⟨b.val.val, ⟨b.property, b.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def ambientCoveringQuotientMap (K N : Subgroup G) :
    ↥(K ⊓ N) →* N ⧸ CFSG.oddCore N :=
  (QuotientGroup.mk' (CFSG.oddCore N)).comp (Subgroup.inclusion inf_le_right)

theorem ambientCoveringQuotientMap_surjective (K N : Subgroup G)
    (hcover : CFSG.oddCore N ⊔ K.subgroupOf N = ⊤) :
    Function.Surjective (ambientCoveringQuotientMap K N) := by
  have hcomp : ambientCoveringQuotientMap K N =
      ((QuotientGroup.mk' (CFSG.oddCore N)).comp (K.subgroupOf N).subtype).comp
        (ambientIntersectionEquiv K N).toMonoidHom := rfl
  rw [hcomp]
  exact (covering_quotient_restriction_surjective (CFSG.oddCore N) (K.subgroupOf N)
    hcover).comp (ambientIntersectionEquiv K N).surjective

theorem ambientCoveringQuotientMap_ker (K N : Subgroup G) :
    (ambientCoveringQuotientMap K N).ker =
      ((CFSG.oddCore N).map N.subtype).subgroupOf (K ⊓ N) := by
  ext b
  change (QuotientGroup.mk' (CFSG.oddCore N))
    (Subgroup.inclusion inf_le_right b) = 1 ↔ _
  change ((Subgroup.inclusion inf_le_right b : N) : N ⧸ CFSG.oddCore N) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hb
    exact ⟨Subgroup.inclusion inf_le_right b, hb, rfl⟩
  · rintro ⟨v, hv, heq⟩
    exact (Subtype.ext heq : v = Subgroup.inclusion inf_le_right b) ▸ hv

theorem ambient_covering_odd_core_eq [Finite G] (K N : Subgroup G)
    (hcover : CFSG.oddCore N ⊔ K.subgroupOf N = ⊤) :
    CFSG.oddCore ↥(K ⊓ N) = ((CFSG.oddCore N).map N.subtype).subgroupOf (K ⊓ N) := by
  let E := ambientIntersectionEquiv K N
  have heq : (CFSG.oddCore ↥(K ⊓ N)).map E.toMonoidHom = CFSG.oddCore (K.subgroupOf N) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant E
  rw [covering_odd_core_eq_kernel_intersection (K.subgroupOf N) hcover] at heq
  ext b
  rw [← Subgroup.mem_map_iff_mem (f := E.toMonoidHom) E.injective, heq]
  change E b ∈ (CFSG.oddCore N).subgroupOf (K.subgroupOf N) ↔ _
  constructor
  · intro hb
    exact ⟨(E b).val, hb, rfl⟩
  · rintro ⟨v, hv, heqv⟩
    change (E b).val ∈ CFSG.oddCore N
    exact (Subtype.ext heqv : v = (E b).val) ▸ hv

theorem ambient_covering_odd_core_quotient_equiv [Finite G] (K N : Subgroup G)
    (hcover : CFSG.oddCore N ⊔ K.subgroupOf N = ⊤) :
    ∃ E : ↥(K ⊓ N) ⧸ CFSG.oddCore ↥(K ⊓ N) ≃* N ⧸ CFSG.oddCore N,
      ∀ b : ↥(K ⊓ N), E ((QuotientGroup.mk' (CFSG.oddCore ↥(K ⊓ N))) b) =
        (QuotientGroup.mk' (CFSG.oddCore N)) (Subgroup.inclusion inf_le_right b) := by
  let f := ambientCoveringQuotientMap K N
  have hf := ambientCoveringQuotientMap_surjective K N hcover
  have hker : f.ker = CFSG.oddCore ↥(K ⊓ N) := by
    rw [ambientCoveringQuotientMap_ker, ambient_covering_odd_core_eq K N hcover]
  let E := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨E, fun _ => rfl⟩

theorem internal_odd_core_factorization_iff_ambient_product {K N : Subgroup G} :
    CFSG.oddCore K ⊔ N.subgroupOf K = ⊤ ↔
      (K : Set G) = ((CFSG.oddCore K).map K.subtype : Set G) * (K ⊓ N : Set G) := by
  constructor
  · intro h
    ext g
    constructor
    · intro hg
      have hgK : (⟨g, hg⟩ : K) ∈ CFSG.oddCore K ⊔ N.subgroupOf K := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨o, ho, b, hb, hob⟩ := Subgroup.mem_sup_of_normal_left.mp hgK
      exact Set.mem_mul.mpr ⟨o.val, ⟨o, ho, rfl⟩, b.val, ⟨b.property, hb⟩,
        congrArg Subtype.val hob⟩
    · rintro ⟨o, ⟨v, hv, rfl⟩, b, hb, rfl⟩
      exact K.mul_mem v.property hb.1
  · intro h
    apply (Subgroup.eq_top_iff' _).mpr
    intro k
    have hk : k.val ∈ ((CFSG.oddCore K).map K.subtype : Set G) * (K ⊓ N : Set G) :=
      h ▸ k.property
    obtain ⟨o, ⟨v, hv, rfl⟩, b, hb, hprod⟩ := hk
    have hbK : (⟨b, hb.1⟩ : K) ∈ N.subgroupOf K := hb.2
    have h : v * (⟨b, hb.1⟩ : K) ∈ CFSG.oddCore K ⊔ N.subgroupOf K :=
      Subgroup.mul_mem_sup hv hbK
    exact (Subtype.ext hprod : v * (⟨b, hb.1⟩ : K) = k) ▸ h

theorem mem_commutator_of_isConj {x y : G} (hxy : IsConj x y)
    (hy : y ∈ commutator G) : x ∈ commutator G := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy.symm
  rw [← hg]
  exact (inferInstance : (commutator G).Normal).conj_mem _ hy _

theorem sylow_le_commutator_of_full_local_actions [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)))
    (hv : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3))) :
    (S : Subgroup G) ≤ commutator G := by
  have hB := modelBase_le_commutator_of_sym3 n (by omega) S e hbase
  have hx2 : wreathModelHom S e (Original.x2 (2 ^ n)) ∈ commutator G :=
    hB (Subgroup.mem_map_of_mem (wreathModelHom S e) (by simp))
  have ht : wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) ∈ commutator G :=
    hB (Subgroup.mem_map_of_mem (wreathModelHom S e)
      ((baseSubgroup (2 ^ n)).pow_mem (by simp [Original.t]) _))
  obtain ⟨g, _, hg⟩ := modelVNormalizer_swap_fusion n hn S e hv
  have hz : wreathModelHom S e (Original.z (2 ^ n)) ∈ commutator G := by
    rcases hg with hg | hg
    · exact mem_commutator_of_isConj (isConj_iff.mpr ⟨g, hg⟩) hx2
    · exact mem_commutator_of_isConj (isConj_iff.mpr ⟨g, hg⟩) ht
  rw [← wreathModelHom_range S e]
  have hgen : Subgroup.closure {Original.s (2 ^ n), Original.z (2 ^ n)} = ⊤ :=
    wreath_eq_generated_s_swap (2 ^ n)
  have hall : ⊤ ≤ (commutator G).comap (wreathModelHom S e) := by
    rw [← hgen, Subgroup.closure_le]
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hB (Subgroup.mem_map_of_mem (wreathModelHom S e) (by simp [Original.s]))
    · rw [Set.mem_singleton_iff] at ha
      exact ha ▸ hz
  rintro _ ⟨a, rfl⟩
  exact hall (Subgroup.mem_top a)

theorem no_index_two_subgroup_of_sylow_le_commutator [Finite G]
    (S : Sylow 2 G) (hS : (S : Subgroup G) ≤ commutator G) :
    ∀ T : Subgroup G, T.index ≠ 2 := by
  intro T hT
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : T.Normal := T.normal_of_index_eq_two hT
  have hcard : Nat.card (G ⧸ T) = 2 := T.index_eq_card.symm.trans hT
  let : IsCyclic (G ⧸ T) := isCyclic_of_prime_card hcard
  have hc : commutator G ≤ T :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hdiv : T.index ∣ (S : Subgroup G).index :=
    Subgroup.index_dvd_of_le (hS.trans hc)
  rw [hT] at hdiv
  exact S.not_dvd_index hdiv

theorem modelBase_involutions_conjugate_of_sym3 [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)))
    (x y : G) (hx : x ∈ modelBase S e) (hy : y ∈ modelBase S e)
    (hxorder : orderOf x = 2) (hyorder : orderOf y = 2) : IsConj x y := by
  obtain ⟨g, _, hg⟩ := modelBaseNormalizer_involutions_transitive n hn S e hbase
    x y hx hy hxorder hyorder
  exact isConj_iff.mpr ⟨g, hg⟩

theorem original_x_isConj_x2_of_sym3 [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3))) :
    IsConj (wreathModelHom S e (Original.x (2 ^ n)))
      (wreathModelHom S e (Original.x2 (2 ^ n))) := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  apply modelBase_involutions_conjugate_of_sym3 n (by omega) S e hbase
  · exact Subgroup.mem_map_of_mem (wreathModelHom S e) (by simp)
  · exact Subgroup.mem_map_of_mem (wreathModelHom S e) (by simp)
  · exact (orderOf_injective _ (wreathModelHom_injective S e) _).trans
      hstructure.involution_orders.1
  · exact (orderOf_injective _ (wreathModelHom_injective S e) _).trans
      hstructure.involution_orders.2.1

theorem original_x_isConj_swap_of_full_local_actions [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)))
    (hv : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3))) :
    IsConj (wreathModelHom S e (Original.x (2 ^ n)))
      (wreathModelHom S e (Original.z (2 ^ n))) := by
  obtain ⟨g, _, hg⟩ := modelVNormalizer_swap_fusion n hn S e hv
  have hxx2 := original_x_isConj_x2_of_sym3 n hn S e hbase
  rcases hg with hg | hg
  · exact hxx2.trans (isConj_iff.mpr ⟨g, hg⟩).symm
  · have hx2t : IsConj (Original.x2 (2 ^ n))
        (Original.t (2 ^ n) ^ (2 ^ n / 2)) :=
      (wreath_center_involution_and_quaternion_coordinates n hn).x2_class _ |>.mpr
        (Or.inr rfl)
    exact (hxx2.trans ((wreathModelHom S e).map_isConj hx2t)).trans
      (isConj_iff.mpr ⟨g, hg⟩).symm

theorem model_involution_isConj_original_x_of_full_local_actions [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)))
    (hv : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3)))
    (w : Wreath (2 ^ n)) (hw : orderOf w = 2) :
    IsConj (wreathModelHom S e w) (wreathModelHom S e (Original.x (2 ^ n))) := by
  rcases (wreath_center_involution_and_quaternion_coordinates n hn).involution_classes w hw
      with h | h | h
  · exact (wreathModelHom S e).map_isConj h.symm
  · exact ((wreathModelHom S e).map_isConj h.symm).trans
      (original_x_isConj_x2_of_sym3 n hn S e hbase).symm
  · exact ((wreathModelHom S e).map_isConj h.symm).trans
      (original_x_isConj_swap_of_full_local_actions n hn S e hbase hv).symm

theorem ambient_involution_isConj_original_x_of_full_local_actions [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)))
    (hv : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3)))
    (x : G) (hx : orderOf x = 2) :
    IsConj x (wreathModelHom S e (Original.x (2 ^ n))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨y, hxy⟩ :=
    CFSG.Semidihedral.InvolutionFusion.exists_ambient_conjugate_mem_sylow S x hxp
  have hyG : orderOf (y : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  have hyorder : orderOf (e y) = 2 :=
    (e.orderOf_eq y).trans ((Subgroup.orderOf_coe y).symm.trans hyG)
  have hyx := model_involution_isConj_original_x_of_full_local_actions n hn S e
    hbase hv (e y) hyorder
  have hyactual : wreathModelHom S e (e y) = (y : G) :=
    congrArg Subtype.val (e.symm_apply_apply y)
  rw [hyactual] at hyx
  exact hxy.trans hyx

theorem all_involutions_conjugate_of_full_local_actions [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)))
    (hv : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3)))
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  (ambient_involution_isConj_original_x_of_full_local_actions n hn S e hbase hv x hx).trans
    (ambient_involution_isConj_original_x_of_full_local_actions n hn S e hbase hv y hy).symm

theorem involution_image_central_of_odd_core_factorization
    (x : G) (hfactor : CFSG.oddCore G ⊔ Subgroup.centralizer {x} = ⊤) :
    (QuotientGroup.mk' (CFSG.oddCore G)) x ∈ Subgroup.center (G ⧸ CFSG.oddCore G) := by
  let q := QuotientGroup.mk' (CFSG.oddCore G)
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore G) y
  have hg : g ∈ CFSG.oddCore G ⊔ Subgroup.centralizer {x} := by
    rw [hfactor]
    exact Subgroup.mem_top _
  obtain ⟨r, hr, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  have hqr : q r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  have hcx := Subgroup.mem_centralizer_singleton_iff.mp hc
  change q (r * c) * q x = q x * q (r * c)
  rw [map_mul, hqr, one_mul, ← map_mul, ← map_mul, hcx]

theorem nonfactorization_of_full_base_action [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3))) :
    CFSG.oddCore G ⊔ involutionCentralizer n S e ≠ ⊤ := by
  intro hfactor
  let q := QuotientGroup.mk' (CFSG.oddCore G)
  let x := wreathModelHom S e (Original.x (2 ^ n))
  let y := wreathModelHom S e (Original.x2 (2 ^ n))
  have hxcentral : q x ∈ Subgroup.center (G ⧸ CFSG.oddCore G) :=
    involution_image_central_of_odd_core_factorization x hfactor
  have hxy : q x = q y :=
    ((q.map_isConj (original_x_isConj_x2_of_sym3 n hn S e hbase)).eq_of_left_mem_center
      hxcentral)
  have hinj := odd_quotient_injective_on_two_subgroup (CFSG.oddCore G) (S : Subgroup G)
    (CFSG.ComponentClassification.OddCore.odd_card G) S.isPGroup'
  have hxyactual : x = y := congrArg Subtype.val
    (hinj (show (q.comp (S : Subgroup G).subtype) (e.symm (Original.x (2 ^ n))) =
      (q.comp (S : Subgroup G).subtype) (e.symm (Original.x2 (2 ^ n))) from hxy))
  have hmodel : Original.x (2 ^ n) = Original.x2 (2 ^ n) :=
    wreathModelHom_injective S e hxyactual
  exact (wreath_center_involution_and_quaternion_coordinates n hn).distinct_classes.1
    (hmodel ▸ IsConj.refl _)

theorem base_quotient_two_and_sym3_exclusive
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ¬ (Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2 ∧
      Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
        (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
          (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3))) := by
  rintro ⟨htwo, ⟨E⟩⟩
  have hsix : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 6 := by
    rw [Nat.card_congr E.toEquiv, Nat.card_perm]
    norm_num
  omega

@[expose] def coveringBaseQuotient {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) : Type u :=
  Subgroup.normalizer ((modelBase S e).subgroupOf K : Set K) ⧸
    (Subgroup.centralizer ((modelBase S e).subgroupOf K : Set K)).subgroupOf
      (Subgroup.normalizer ((modelBase S e).subgroupOf K : Set K))

instance coveringBaseQuotientGroup {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) : Group (coveringBaseQuotient S e K) :=
  inferInstanceAs (Group (Subgroup.normalizer ((modelBase S e).subgroupOf K : Set K) ⧸
    (Subgroup.centralizer ((modelBase S e).subgroupOf K : Set K)).subgroupOf
      (Subgroup.normalizer ((modelBase S e).subgroupOf K : Set K))))

@[expose] def coveringVDenominator {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) : Subgroup
      (Subgroup.normalizer ((modelV S e).subgroupOf K : Set K)) :=
  ((modelV S e).subgroupOf K ⊔
    Subgroup.centralizer ((modelV S e).subgroupOf K : Set K)).subgroupOf
      (Subgroup.normalizer ((modelV S e).subgroupOf K : Set K))

instance coveringVDenominator_normal {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) : (coveringVDenominator S e K).Normal := by
  unfold coveringVDenominator
  rw [Subgroup.subgroupOf_sup ((modelV S e).subgroupOf K).le_normalizer
    (Subgroup.centralizer_le_normalizer _)]
  infer_instance

@[expose] def coveringVQuotient {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) : Type u :=
  Subgroup.normalizer ((modelV S e).subgroupOf K : Set K) ⧸ coveringVDenominator S e K

instance coveringVQuotientGroup {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) : Group (coveringVQuotient S e K) :=
  inferInstanceAs (Group
    (Subgroup.normalizer ((modelV S e).subgroupOf K : Set K) ⧸ coveringVDenominator S e K))

@[expose] def normalizerCentralizerQuotientEquivOfEq {U U' : Subgroup G} (h : U = U') :
    Subgroup.normalizer (U : Set G) ⧸
      (Subgroup.centralizer (U : Set G)).subgroupOf (Subgroup.normalizer (U : Set G)) ≃*
    Subgroup.normalizer (U' : Set G) ⧸
      (Subgroup.centralizer (U' : Set G)).subgroupOf (Subgroup.normalizer (U' : Set G)) := by
  subst U'
  exact MulEquiv.refl _

@[expose] def innerCentralizerDenominator (U : Subgroup G) :
    Subgroup (Subgroup.normalizer (U : Set G)) :=
  U.subgroupOf (Subgroup.normalizer (U : Set G)) ⊔
    (Subgroup.centralizer (U : Set G)).subgroupOf (Subgroup.normalizer (U : Set G))

instance innerCentralizerDenominator_normal (U : Subgroup G) :
    (innerCentralizerDenominator U).Normal := by
  unfold innerCentralizerDenominator
  infer_instance

@[expose] def normalizerInnerCentralizerQuotientEquivOfEq {U U' : Subgroup G}
    (h : U = U') :
    Subgroup.normalizer (U : Set G) ⧸ innerCentralizerDenominator U ≃*
      Subgroup.normalizer (U' : Set G) ⧸ innerCentralizerDenominator U' := by
  subst U'
  exact MulEquiv.refl _

@[expose] def subgroupBaseQuotientEquiv {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    Subgroup.normalizer (modelBase (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) : Set K) ⧸
      (Subgroup.centralizer (modelBase (subgroupSylow S K hSK)
        (subgroupCoordinates S e K hSK) : Set K)).subgroupOf
        (Subgroup.normalizer (modelBase (subgroupSylow S K hSK)
          (subgroupCoordinates S e K hSK) : Set K)) ≃* coveringBaseQuotient S e K :=
  normalizerCentralizerQuotientEquivOfEq (subgroupModelBase_eq S e K hSK)

@[expose] def subgroupVQuotientEquiv {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    Subgroup.normalizer (modelV (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) : Set K) ⧸
      modelVInnerCentralizer (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) ≃*
        coveringVQuotient S e K := by
  let E := normalizerInnerCentralizerQuotientEquivOfEq (subgroupModelV_eq S e K hSK)
  have hden : innerCentralizerDenominator ((modelV S e).subgroupOf K) =
      coveringVDenominator S e K := by
    unfold innerCentralizerDenominator coveringVDenominator
    rw [Subgroup.subgroupOf_sup ((modelV S e).subgroupOf K).le_normalizer
      (Subgroup.centralizer_le_normalizer _)]
  exact E.trans (QuotientGroup.quotientMulEquivOfEq hden)

theorem covering_base_quotient_alternatives [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    Nat.card (coveringBaseQuotient S e K) = 2 ∨
      Nonempty (coveringBaseQuotient S e K ≃* Equiv.Perm (Fin 3)) := by
  rcases modelBaseNormalizerQuotient_alternatives n (by omega)
      (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) with htwo | hsix
  · exact Or.inl ((Nat.card_congr (subgroupBaseQuotientEquiv S e K hSK).toEquiv).symm.trans
      htwo)
  · obtain ⟨E⟩ := hsix
    exact Or.inr ⟨(subgroupBaseQuotientEquiv S e K hSK).symm.trans E⟩

theorem covering_v_quotient_sym3 [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤) :
    Nonempty (coveringVQuotient S e K ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨E⟩ := covering_subgroupVNormalizerQuotient_sym3 hnonab n hn S e K hSK hcover
  exact ⟨(subgroupVQuotientEquiv S e K hSK).symm.trans E⟩

@[expose] def coveringInvolution (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) : K :=
  ⟨wreathModelHom S e (Original.x (2 ^ n)), hSK (e.symm (Original.x (2 ^ n))).property⟩

theorem coveringInvolution_coe (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    (coveringInvolution n S e K hSK).val = wreathModelHom S e (Original.x (2 ^ n)) := rfl

theorem coveringInvolution_centralizer (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    Subgroup.centralizer ({(coveringInvolution n S e K hSK)} : Set K) =
      (involutionCentralizer n S e).subgroupOf K :=
  subgroupInvolutionCentralizer_eq n S e K hSK

theorem covering_order_two_factorization [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (hcard : Nat.card (coveringBaseQuotient S e K) = 2) :
    (K : Set G) = ((CFSG.oddCore K).map K.subtype : Set G) *
      (K ⊓ involutionCentralizer n S e : Set G) ∧
    (QuotientGroup.mk' (CFSG.oddCore K)) (coveringInvolution n S e K hSK) ∈
      Subgroup.center (K ⧸ CFSG.oddCore K) ∧
    (CFSG.oddCore K).map K.subtype ⊓ involutionCentralizer n S e =
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓ K := by
  have hcard' : Nat.card (Subgroup.normalizer (modelBase (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) : Set K) ⧸
      (Subgroup.centralizer (modelBase (subgroupSylow S K hSK)
        (subgroupCoordinates S e K hSK) : Set K)).subgroupOf
        (Subgroup.normalizer (modelBase (subgroupSylow S K hSK)
          (subgroupCoordinates S e K hSK) : Set K))) = 2 := by
    exact (Nat.card_congr (subgroupBaseQuotientEquiv S e K hSK).toEquiv).trans hcard
  have hf := base_order_two_original_involution_factorization n hn
    (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) hcard'
  have hfK := hf.1
  rw [subgroupInvolutionCentralizer_eq] at hfK
  exact ⟨internal_odd_core_factorization_iff_ambient_product.mp hfK, hf.2,
    covering_base_order_two_core_intersection n hn S e K hSK hcover hcard'⟩

theorem covering_typeI_obstruction [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hbase : Nonempty (coveringBaseQuotient S e K ≃* Equiv.Perm (Fin 3)))
    (hv : Nonempty (coveringVQuotient S e K ≃* Equiv.Perm (Fin 3))) :
    (S : Subgroup G) ≤ (commutator K).map K.subtype ∧
    (∀ T : Subgroup K, T.index ≠ 2) ∧
    (∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
    (K : Set G) ≠ ((CFSG.oddCore K).map K.subtype : Set G) *
      (K ⊓ involutionCentralizer n S e : Set G) := by
  have hbase' : Nonempty (Subgroup.normalizer (modelBase (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) : Set K) ⧸
      (Subgroup.centralizer (modelBase (subgroupSylow S K hSK)
        (subgroupCoordinates S e K hSK) : Set K)).subgroupOf
        (Subgroup.normalizer (modelBase (subgroupSylow S K hSK)
          (subgroupCoordinates S e K hSK) : Set K)) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨E⟩ := hbase
    exact ⟨(subgroupBaseQuotientEquiv S e K hSK).trans E⟩
  have hv' : Nonempty (Subgroup.normalizer (modelV (subgroupSylow S K hSK)
      (subgroupCoordinates S e K hSK) : Set K) ⧸
      modelVInnerCentralizer (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) ≃*
        Equiv.Perm (Fin 3)) := by
    obtain ⟨E⟩ := hv
    exact ⟨(subgroupVQuotientEquiv S e K hSK).trans E⟩
  have hS := sylow_le_commutator_of_full_local_actions n hn
    (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) hbase' hv'
  have hSambient : (S : Subgroup G) ≤ (commutator K).map K.subtype := by
    intro s hs
    exact ⟨⟨s, hSK hs⟩, hS hs, rfl⟩
  refine ⟨hSambient, no_index_two_subgroup_of_sylow_le_commutator
    (subgroupSylow S K hSK) hS,
    all_involutions_conjugate_of_full_local_actions n hn
      (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) hbase' hv', ?_⟩
  intro hf
  have hfactor := internal_odd_core_factorization_iff_ambient_product.mpr hf
  rw [← subgroupInvolutionCentralizer_eq n S e K hSK] at hfactor
  exact nonfactorization_of_full_base_action n hn
    (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK) hbase' hfactor

theorem covering_intersection_eq_centralizer (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    K ⊓ involutionCentralizer n S e =
      (Subgroup.centralizer ({(coveringInvolution n S e K hSK)} : Set K)).map K.subtype := by
  rw [coveringInvolution_centralizer]
  ext g
  constructor
  · rintro ⟨hgK, hgN⟩
    exact ⟨⟨g, hgK⟩, hgN, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.property, hk⟩

theorem covering_v_denominator_product {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (K : Subgroup G) :
    (((modelV S e).subgroupOf K ⊔
      Subgroup.centralizer ((modelV S e).subgroupOf K : Set K) : Subgroup K) : Set K) =
        ((modelV S e).subgroupOf K : Set K) *
          (Subgroup.centralizer ((modelV S e).subgroupOf K : Set K) : Set K) := by
  apply Subgroup.coe_mul_of_right_le_normalizer_left
  exact Subgroup.centralizer_le_normalizer _

theorem ambient_covering_odd_core_map_eq [Finite G] (K N : Subgroup G)
    (hcover : CFSG.oddCore N ⊔ K.subgroupOf N = ⊤) :
    (CFSG.oddCore ↥(K ⊓ N)).map (K ⊓ N).subtype =
      (CFSG.oddCore N).map N.subtype ⊓ (K ⊓ N) := by
  rw [ambient_covering_odd_core_eq K N hcover]
  ext g
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨hb, b.property⟩
  · rintro ⟨hgR, hgB⟩
    exact ⟨⟨g, hgB⟩, hgR, rfl⟩

structure CoveringFactorizationBranch (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) : Prop where
  base_card_two : Nat.card (coveringBaseQuotient S e K) = 2
  factorization : (K : Set G) = ((CFSG.oddCore K).map K.subtype : Set G) *
    (K ⊓ involutionCentralizer n S e : Set G)
  original_involution_central :
    (QuotientGroup.mk' (CFSG.oddCore K)) (coveringInvolution n S e K hSK) ∈
      Subgroup.center (K ⧸ CFSG.oddCore K)
  core_intersection :
    (CFSG.oddCore K).map K.subtype ⊓ involutionCentralizer n S e =
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓ K

structure CoveringTypeIObstruction (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) : Prop where
  base_sym3 : Nonempty (coveringBaseQuotient S e K ≃* Equiv.Perm (Fin 3))
  sylow_in_derived : (S : Subgroup G) ≤ (commutator K).map K.subtype
  no_index_two : ∀ T : Subgroup K, T.index ≠ 2
  one_involution_class : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y
  nonfactorization : (K : Set G) ≠ ((CFSG.oddCore K).map K.subtype : Set G) *
    (K ⊓ involutionCentralizer n S e : Set G)

theorem covering_branches_mutually_exclusive (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    ¬ (CoveringFactorizationBranch n S e K hSK ∧ CoveringTypeIObstruction n S e K) := by
  rintro ⟨hf, hi⟩
  exact hi.nonfactorization hf.factorization

structure FullSylowCoveringConclusion (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) : Prop where
  actual_intersection : K ⊓ involutionCentralizer n S e =
    (Subgroup.centralizer ({(coveringInvolution n S e K hSK)} : Set K)).map K.subtype
  odd_core : CFSG.oddCore ↥(K ⊓ involutionCentralizer n S e) =
    ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype).subgroupOf
      (K ⊓ involutionCentralizer n S e)
  ambient_odd_core : (CFSG.oddCore ↥(K ⊓ involutionCentralizer n S e)).map
      (K ⊓ involutionCentralizer n S e).subtype =
    (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
      (K ⊓ involutionCentralizer n S e)
  inclusion_quotient :
    ∃ E : ↥(K ⊓ involutionCentralizer n S e) ⧸
        CFSG.oddCore ↥(K ⊓ involutionCentralizer n S e) ≃*
          involutionCentralizer n S e ⧸ centralizerOddCore n S e,
      ∀ b : ↥(K ⊓ involutionCentralizer n S e),
        E ((QuotientGroup.mk' (CFSG.oddCore ↥(K ⊓ involutionCentralizer n S e))) b) =
          (QuotientGroup.mk' (centralizerOddCore n S e)) (Subgroup.inclusion inf_le_right b)
  v_sym3 : Nonempty (coveringVQuotient S e K ≃* Equiv.Perm (Fin 3))
  alternatives : CoveringFactorizationBranch n S e K hSK ∨ CoveringTypeIObstruction n S e K
  mutually_exclusive :
    ¬ (CoveringFactorizationBranch n S e K hSK ∧ CoveringTypeIObstruction n S e K)

theorem full_Sylow_covering_subgroup_conclusion_of_internal_covering
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤) :
    FullSylowCoveringConclusion n S e K hSK := by
  have hv := covering_v_quotient_sym3 hnonab n hn S e K hSK hcover
  refine ⟨covering_intersection_eq_centralizer n S e K hSK,
    ambient_covering_odd_core_eq K (involutionCentralizer n S e) hcover,
    ambient_covering_odd_core_map_eq K (involutionCentralizer n S e) hcover,
    ambient_covering_odd_core_quotient_equiv K (involutionCentralizer n S e) hcover,
    hv, ?_, covering_branches_mutually_exclusive n S e K hSK⟩
  rcases covering_base_quotient_alternatives n hn S e K hSK with htwo | hsix
  · obtain ⟨hfactor, hcentral, hintersection⟩ :=
      covering_order_two_factorization n hn S e K hSK hcover htwo
    exact Or.inl ⟨htwo, hfactor, hcentral, hintersection⟩
  · obtain ⟨hS, hindex, hclass, hnonfactor⟩ :=
      covering_typeI_obstruction n hn S e K hSK hsix hv
    exact Or.inr ⟨hsix, hS, hindex, hclass, hnonfactor⟩

theorem actual_odd_core_covering_iff_product {K N : Subgroup G} :
    CFSG.oddCore N ⊔ K.subgroupOf N = ⊤ ↔
      (N : Set G) = ((CFSG.oddCore N).map N.subtype : Set G) * (K ⊓ N : Set G) := by
  simpa only [inf_comm] using
    (internal_odd_core_factorization_iff_ambient_product (K := N) (N := K))

theorem full_Sylow_covering_subgroup_has_factorization_or_exact_typeI_obstruction
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : (involutionCentralizer n S e : Set G) =
      ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype : Set G) *
        (K ⊓ involutionCentralizer n S e : Set G)) :
    FullSylowCoveringConclusion n S e K hSK :=
  full_Sylow_covering_subgroup_conclusion_of_internal_covering hnonab n hn S e K hSK
    (actual_odd_core_covering_iff_product.mpr hcover)

structure ProperCoveringTypeIObstruction (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) : Prop where
  proper : K < ⊤
  nontrivial_odd_core : CFSG.oddCore K ≠ ⊥
  full_covering : FullSylowCoveringConclusion n S e K hSK
  typeI : CoveringTypeIObstruction n S e K

theorem proper_full_Sylow_covering_typeI_obstruction [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : (involutionCentralizer n S e : Set G) =
      ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype : Set G) *
        (K ⊓ involutionCentralizer n S e : Set G))
    (hproper : K < ⊤) (hcore : CFSG.oddCore K ≠ ⊥)
    (hnonfactor : (K : Set G) ≠ ((CFSG.oddCore K).map K.subtype : Set G) *
      (K ⊓ involutionCentralizer n S e : Set G)) :
    ProperCoveringTypeIObstruction n S e K hSK := by
  have hfull := full_Sylow_covering_subgroup_has_factorization_or_exact_typeI_obstruction
    hnonab n hn S e K hSK hcover
  refine ⟨hproper, hcore, hfull, ?_⟩
  rcases hfull.alternatives with hf | hi
  · exact False.elim (hnonfactor hf.factorization)
  · exact hi

end CFSG.Wreathed.FullSylowCoveringObstruction
