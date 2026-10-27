module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6MinusculeFixedField
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6FiniteToralAction
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoOriginalOuterAction
public import CFSG.LocalAnalysis.StandardType.GGNsq2PairLift
public import CFSG.LocalAnalysis.StandardType.GGFixedTwoKernelTransport
import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction

public noncomputable section

namespace CFSG.StandardType.GGFinModel

open CFSG.Open CFSG.StandardType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP CFSG.LieType.Universal.Unitary
  CFSG.StandardType.CompactA2Pair CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.E6
  CFSG.RankThree.PartOne.TCX.E CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open scoped MatrixGroups commutatorElement

open CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG.GroupTheory

theorem exists_whole_compact_pair_in_original_joined_two_quotient
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark)
    {ht : GGExcFive .twistedE6} (M : GGDatumModel .twistedE6 1 3 ht) :
    ∃ (Ψ : SL(3, actualQuadraticSubfield 1) →*
        e6Data_valid.minGroup (actualQuadraticSubfield 1))
      (ρ : SL(3, actualQuadraticSubfield 1) →*
        adjointGroup Tag.E6 (actualQuadraticSubfield 1))
      (c : e6Data_valid.minGroup GGL)
      (theta : Su (actualQuadraticSubfield 1) 2 1 3 →* (ggU .twistedE6 0 1).K),
      ρ = (e6IsogenyT (actualQuadraticSubfield 1)).comp Ψ ∧
      CFSG.RankThree.PartOne.KF4.IsA2Frame
        ((adjointGroup Tag.E6 (actualQuadraticSubfield 1)).subtype.comp ρ)
        (fun i j => CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 i j) ∧
      ((adjointGroup Tag.E6 (actualQuadraticSubfield 1)).subtype.comp ρ) =
        e6rhoA2₁ (actualQuadraticSubfield 1) ∧
      Function.Injective theta ∧ e6IsogenyAlgebraic c = M.D.g0 ∧
      ((minBC e6Data_valid (ggRatEmb 2)).comp
        (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
          (GaloisField 2 2) (CFSG.LieType.Steinberg.Exceptional.frobQ 2 1)).subtype).comp
        theta = (MulAut.conj c).toMonoidHom.comp
          (((minBC e6Data_valid (actualQuadraticSubfield 1).subtype).comp Ψ).comp
            (CFSG.ClassicalInvolution.Models.suToSL
              (unitaryInvolution (actualQuadraticSubfield 1) 2 1) 3)) ∧
      (ggIotaK .twistedE6 0 1 (by decide)).comp theta =
        (MulAut.conj M.D.g0).toMonoidHom.comp
          (e6IsogenyAlgebraic.comp
            (((minBC e6Data_valid (actualQuadraticSubfield 1).subtype).comp Ψ).comp
              (CFSG.ClassicalInvolution.Models.suToSL
                (unitaryInvolution (actualQuadraticSubfield 1) 2 1) 3))) ∧
      Function.Injective (D.joinedScMap.comp theta) ∧
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f' : ℕ),
        Nat.card K = (2 ^ f') ^ 2 →
        Nat.card ((B12 (actualQuadraticSubfield 1) 2 1).map (D.joinedScMap.comp theta)) =
          2 ^ f' * ((2 ^ f') ^ 2 - 1) →
        UnitaryBlockStandardPair K 2 f' (D.joinedScMap.comp theta).range
          ((B12 (actualQuadraticSubfield 1) 2 1).map (D.joinedScMap.comp theta))
          ((B23 (actualQuadraticSubfield 1) 2 1).map (D.joinedScMap.comp theta)) := by
  exact exists_twisted_originalU_marked_pair_mod_central (n := 0) M
    Nat.prime_three (by decide) (by decide) D.joinedScMap D.joinedScMap_ker_le_center

open CFSG.EvenSmallLie.TwoE6 CFSG.LieType.Chevalley.C2E6Std

@[expose] noncomputable def stdLangEmbedding :
    CFSG.LieType.Chevalley.C2E6Std.stdGroup →* ModGL Tag.E6 GGL :=
  isogenyStd.liftOfSurjective isogenyStd_surjective
    ⟨ggIotaK .twistedE6 0 1 (by decide), by
      exact (ker_isogenyStd_eq_center.trans
        (ggIotaK_twistedE6_ker_eq_center 0 1 (by decide)).symm).le⟩

@[simp] theorem stdLangEmbedding_isogeny (u : twistedE6Group 2 1) :
    stdLangEmbedding (isogenyStd u) = ggIotaK .twistedE6 0 1 (by decide) u := by
  simp only [stdLangEmbedding, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply]
  rfl

theorem stdLangEmbedding_injective : Function.Injective stdLangEmbedding := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 1
  obtain ⟨u, rfl⟩ := isogenyStd_surjective x
  have hu : u ∈ (ggIotaK .twistedE6 0 1 (by decide)).ker := by
    change ggIotaK .twistedE6 0 1 (by decide) u = 1
    exact (stdLangEmbedding_isogeny u).symm.trans hx
  have huc : u ∈ Subgroup.center (twistedE6Group 2 1) :=
    (ggIotaK_twistedE6_ker_eq_center 0 1 (by decide)).le hu
  exact MonoidHom.mem_ker.mp (ker_isogenyStd_eq_center.ge huc)

theorem stdLangEmbedding_eq_field_transport
    (s : CFSG.LieType.Chevalley.C2E6Std.stdGroup) :
    stdLangEmbedding s =
      baseChangeGL ((ggRatEmb 2).comp fieldEquiv.symm.toRingHom)
        (s : ModGL Tag.E6 CFSG.LieType.Chevalley.C2E6Overlap.K) := by
  obtain ⟨u, rfl⟩ := isogenyStd_surjective s
  rw [stdLangEmbedding_isogeny]
  change ggIotaK .twistedE6 0 1 (by decide) u =
    baseChangeGL ((ggRatEmb 2).comp fieldEquiv.symm.toRingHom)
      (baseChangeGL fieldEquiv.toRingHom (e6IsogenyFixed (frobQ 2 1) u))
  have hi := ggIotaK_twistedE6_apply 0 1 (by decide)
    (u : (ggU .twistedE6 0 1).K)
  change ggIotaK .twistedE6 0 1 (by decide) u =
    baseChangeGL (ggRatEmb 2) (e6IsogenyFixed (frobQ 2 1) u) at hi
  rw [hi]
  change baseChangeGL (ggRatEmb 2) (e6IsogenyFixed (frobQ 2 1) u) =
    baseChangeGL ((ggRatEmb 2).comp fieldEquiv.symm.toRingHom)
      (baseChangeGL fieldEquiv.toRingHom (e6IsogenyFixed (frobQ 2 1) u))
  have heq : (((ggRatEmb 2).comp fieldEquiv.symm.toRingHom).comp
      fieldEquiv.toRingHom) = ggRatEmb 2 := by
    ext x
    change ggRatEmb 2 (fieldEquiv.symm (fieldEquiv x)) = ggRatEmb 2 x
    rw [fieldEquiv.symm_apply_apply]
  rw [baseChangeGL_baseChangeGL, heq]

theorem original_joined_quotient_datum
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) (hBs : IsElemAbelian 3 Bs) :
    NsQuot.Datum 3 (X ⊔ Bs)
      (QuotientGroup.mk' (D.twoKernelInG.subgroupOf (X ⊔ Bs))) X Bs D.twoKernelInG := by
  refine
    { prime := Nat.prime_three
      odd := by decide
      surj := QuotientGroup.mk'_surjective _
      ker_eq := QuotientGroup.ker_mk' _
      ZL := D.twoKernelInG_le
      LN := le_sup_left
      BsN := le_sup_right
      Zcent := ?_
      Z2 := ?_
      Bsp := hBs.2 }
  · intro z hz l hl
    exact Subgroup.mem_centralizer_iff.mp (D.twoKernelInG_le_centralizer hz) l hl
  · intro z hz
    obtain ⟨k, hk⟩ := D.twoKernelInG_isPGroup (⟨z, hz⟩ : D.twoKernelInG)
    exact ⟨k, congrArg Subtype.val hk⟩

theorem original_joined_whole_fixed_range_lifts
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) (hBs : IsElemAbelian 3 Bs)
    {U : Type} [Group U] (theta : U →* twistedE6Group 2 1) {r s : MulAut Bs}
    (hfixed : (D.joinedScMap.comp theta).range ≤ Subgroup.centralizer
      (((ggHyperplane Bs r ⊓ ggHyperplane Bs s).subgroupOf Bs).map D.joinedActor :
        Set D.joinedTwoQuotient)) :
    (D.joinedScMap.comp theta).range ≤
      NsQuot.img (X ⊔ Bs) (QuotientGroup.mk' (D.twoKernelInG.subgroupOf (X ⊔ Bs)))
        (X ⊓ Subgroup.centralizer (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G)) := by
  let q := QuotientGroup.mk' (D.twoKernelInG.subgroupOf (X ⊔ Bs))
  let H := ggHyperplane Bs r ⊓ ggHyperplane Bs s
  have hH : H ≤ Bs := inf_le_left.trans (Subgroup.map_subtype_le _)
  have hImgH : NsQuot.img (X ⊔ Bs) q H = (H.subgroupOf Bs).map D.joinedActor := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨(a : G), hH ha⟩, ha, ?_⟩
      rfl
    · rintro ⟨b, hb, rfl⟩
      exact NsQuot.mem_img.mpr ⟨⟨(b : G), (le_sup_right : Bs ≤ X ⊔ Bs) b.2⟩, hb, rfl⟩
  change (D.joinedScMap.comp theta).range ≤
    NsQuot.img (X ⊔ Bs) q (X ⊓ Subgroup.centralizer (H : Set G))
  rw [(original_joined_quotient_datum D hBs).centralizer_img hH, hImgH]
  refine le_inf ?_ hfixed
  rw [MonoidHom.range_comp]
  exact (Subgroup.map_le_range _ _).trans (D.joinedScMap_range.le)

theorem original_joined_compact_pair_lifts_forall_fields
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) (hBs : IsElemAbelian 3 Bs)
    (theta : Su (actualQuadraticSubfield 1) 2 1 3 →* twistedE6Group 2 1)
    (hinj : Function.Injective (D.joinedScMap.comp theta)) {r s : MulAut Bs}
    (hfixed : (D.joinedScMap.comp theta).range ≤ Subgroup.centralizer
      (((ggHyperplane Bs r ⊓ ggHyperplane Bs s).subgroupOf Bs).map D.joinedActor :
        Set D.joinedTwoQuotient))
    (hfree : D.twoKernelInG ⊓ Subgroup.centralizer
      (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) = ⊥)
    (hR : NsQuot.img (X ⊔ Bs)
      (QuotientGroup.mk' (D.twoKernelInG.subgroupOf (X ⊔ Bs))) (ggRankOneIn X Bs r) =
        (B12 (actualQuadraticSubfield 1) 2 1).map (D.joinedScMap.comp theta))
    (hS : NsQuot.img (X ⊔ Bs)
      (QuotientGroup.mk' (D.twoKernelInG.subgroupOf (X ⊔ Bs))) (ggRankOneIn X Bs s) =
        (B23 (actualQuadraticSubfield 1) 2 1).map (D.joinedScMap.comp theta)) :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ),
      Nat.card K = (2 ^ f) ^ 2 →
      Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) →
      ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W
        (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) := by
  let q := QuotientGroup.mk' (D.twoKernelInG.subgroupOf (X ⊔ Bs))
  let hD := original_joined_quotient_datum D hBs
  have hfix : ∀ z ∈ D.twoKernelInG,
      (∀ h ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs s, h * z = z * h) → z = 1 := by
    intro z hz hc
    apply Subgroup.mem_bot.mp
    rw [← hfree]
    exact ⟨hz, Subgroup.mem_centralizer_iff.mpr hc⟩
  have hfixr : ∀ z ∈ D.twoKernelInG,
      (∀ h ∈ ggHyperplane Bs r, h * z = z * h) → z = 1 :=
    fun z hz hc => hfix z hz fun h hh => hc h hh.1
  have hfixs : ∀ z ∈ D.twoKernelInG,
      (∀ h ∈ ggHyperplane Bs s, h * z = z * h) → z = 1 :=
    fun z hz hc => hfix z hz fun h hh => hc h hh.2
  have hmr := (hD.img_rankOneIn hfixr).symm.trans hR
  have hms := (hD.img_rankOneIn hfixs).symm.trans hS
  have hker : (D.joinedScMap.comp theta).ker ≤
      Subgroup.center (Su (actualQuadraticSubfield 1) 2 1 3) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
    exact bot_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpair := CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks hker rfl rfl
  intro K _ _ _ f hK horder
  have hcard : Nat.card ((B12 (actualQuadraticSubfield 1) 2 1).map
      (D.joinedScMap.comp theta)) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [← hmr, hD.card_rankOneIn hfixr, horder]
  have hpairK := ggPhanNSAPairAux_stdPair_of_card
    (card_actualQuadraticSubfield (by decide : 1 ≤ 1)) hK hpair hcard
  rw [← hmr, ← hms] at hpairK
  exact hD.pair_lift hfix hpairK
    (original_joined_whole_fixed_range_lifts D hBs theta hfixed)

set_option linter.style.haveILetI false in
theorem original_joined_rankOne_image_from_source
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) (hBs : IsElemAbelian 3 Bs) (r : MulAut Bs)
    (hfix : ∀ z ∈ D.twoKernelInG,
      (∀ h ∈ ggHyperplane Bs r, h * z = z * h) → z = 1) :
    NsQuot.img (X ⊔ Bs)
      (QuotientGroup.mk' (D.twoKernelInG.subgroupOf (X ⊔ Bs))) (ggRankOneIn X Bs r) =
      (ggOTwoPrime ((⊤ : Subgroup (twistedE6Group 2 1)) ⊓
        ⨅ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)),
          MonoidHom.eqLocus (D.scAction (b : Bs)).toMonoidHom
            (MonoidHom.id (twistedE6Group 2 1)))).map D.joinedScMap := by
  letI : Finite (twistedE6Group 2 1) := finite_twistedE6Group
  let q := QuotientGroup.mk' (D.twoKernelInG.subgroupOf (X ⊔ Bs))
  let hD := original_joined_quotient_datum D hBs
  let Hr := MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)
  have hodd : Odd (Nat.card D.joinedScMap.ker) := by
    rw [ExcTwE6CoverData.joinedScMap,
      MonoidHom.ker_comp_of_injective _ _ D.joinedQuotientMap_injective]
    exact D.scMap_ker_odd
  have hcent :
      (⨅ b : Hr, MonoidHom.eqLocus
        (MulAut.conj (D.joinedActor (b : Bs))).toMonoidHom
        (MonoidHom.id D.joinedTwoQuotient)) =
      Subgroup.centralizer (Hr.map D.joinedActor : Set D.joinedTwoQuotient) := by
    ext x
    constructor
    · intro hx
      apply Subgroup.mem_centralizer_iff.mpr
      rintro a ⟨b, hb, rfl⟩
      have h := Subgroup.mem_iInf.mp hx (⟨b, hb⟩ : Hr)
      change D.joinedActor b * x * (D.joinedActor b)⁻¹ = x at h
      exact mul_inv_eq_iff_eq_mul.mp h
    · intro hx
      apply Subgroup.mem_iInf.mpr
      intro b
      change D.joinedActor (b : Bs) * x * (D.joinedActor (b : Bs))⁻¹ = x
      exact mul_inv_eq_iff_eq_mul.mpr
        (Subgroup.mem_centralizer_iff.mp hx _ (Subgroup.mem_map.mpr ⟨b, b.2, rfl⟩))
  have hImgH : NsQuot.img (X ⊔ Bs) q (ggHyperplane Bs r) = Hr.map D.joinedActor := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hba⟩ := ha
      refine Subgroup.mem_map.mpr ⟨b, hb, ?_⟩
      change q ⟨(b : G), (le_sup_right : Bs ≤ X ⊔ Bs) b.2⟩ = q a
      change (b : G) = (a : G) at hba
      exact congrArg q (Subtype.ext hba)
    · rintro ⟨b, hb, rfl⟩
      exact NsQuot.mem_img.mpr
        ⟨⟨(b : G), (le_sup_right : Bs ≤ X ⊔ Bs) b.2⟩, ⟨b, hb, rfl⟩, rfl⟩
  have hmap := ggOTwoPrime_map_fixedFamily_of_central_odd_kernel
    D.joinedScMap D.joinedScMap_ker_le_center hodd ⊤
    (fun b : Hr => D.scAction (b : Bs))
    (fun b : Hr => MulAut.conj (D.joinedActor (b : Bs)))
    (fun b u => (D.joinedScMap_action (b : Bs) u).symm)
  rw [Subgroup.map_top, hcent] at hmap
  change NsQuot.img (X ⊔ Bs) q
    (ggOTwoPrime (X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G))) = _
  have hHr : ggHyperplane Bs r ≤ Bs := Subgroup.map_subtype_le _
  rw [hD.img_ggOTwoPrime (inf_le_left.trans le_sup_left) (hD.injOn_centralizer hfix),
    hD.centralizer_img hHr, hImgH]
  change ggOTwoPrime (((X.subgroupOf (X ⊔ Bs)).map q) ⊓
    Subgroup.centralizer (Hr.map D.joinedActor : Set D.joinedTwoQuotient)) = _
  rw [← D.joinedScMap_range]
  exact hmap.symm

open CFSG.LieType.Chevalley.C2E6Std CFSG.EvenSmallLie.TwoE6

set_option linter.style.haveILetI false in
theorem original_source_residual_map_native
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) (r : MulAut Bs) :
    (ggOTwoPrime ((⊤ : Subgroup (twistedE6Group 2 1)) ⊓
      ⨅ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)),
        MonoidHom.eqLocus (D.scAction (b : Bs)).toMonoidHom
          (MonoidHom.id (twistedE6Group 2 1)))).map isogenyStd =
      (letI := D.fieldK
       letI := D.finiteK
       ggOTwoPrime ((⊤ : Subgroup stdGroup) ⊓
         ⨅ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)),
           MonoidHom.eqLocus
             (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker (b : Bs)).toMonoidHom
             (MonoidHom.id stdGroup))) := by
  letI := D.fieldK
  letI := D.finiteK
  letI : Finite (twistedE6Group 2 1) := finite_twistedE6Group
  have hodd : Odd (Nat.card isogenyStd.ker) := by
    rw [card_ker_isogenyStd]
    decide
  have hmap := ggOTwoPrime_map_fixedFamily_of_central_odd_kernel
    isogenyStd ker_isogenyStd_le_center hodd ⊤
    (fun b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)) => D.scAction (b : Bs))
    (fun b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)) =>
      originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker (b : Bs))
    (fun b u => D.scAction_spec (b : Bs) u)
  simpa only [Subgroup.map_top, MonoidHom.range_eq_top.mpr isogenyStd_surjective] using hmap

set_option linter.style.haveILetI false in
theorem original_source_residual_eq_of_native_marking
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) (r : MulAut Bs)
    (S : Subgroup (twistedE6Group 2 1)) (hS : ggOTwoPrime S = S)
    (hNative :
      (letI := D.fieldK
       letI := D.finiteK
       ggOTwoPrime ((⊤ : Subgroup stdGroup) ⊓
         ⨅ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)),
           MonoidHom.eqLocus
             (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker (b : Bs)).toMonoidHom
             (MonoidHom.id stdGroup))) = S.map isogenyStd) :
    ggOTwoPrime ((⊤ : Subgroup (twistedE6Group 2 1)) ⊓
      ⨅ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)),
        MonoidHom.eqLocus (D.scAction (b : Bs)).toMonoidHom
          (MonoidHom.id (twistedE6Group 2 1))) = S := by
  letI := D.fieldK
  letI := D.finiteK
  letI : Finite (twistedE6Group 2 1) := finite_twistedE6Group
  have hodd : Odd (Nat.card isogenyStd.ker) := by
    rw [card_ker_isogenyStd]
    decide
  exact ggOTwoPrime_eq_of_map_eq_of_central_odd_kernel
    isogenyStd ker_isogenyStd_le_center hodd _ S hS
      ((original_source_residual_map_native D r).trans hNative)

set_option linter.style.haveILetI false in
theorem original_joined_rankOne_image_of_native_marking
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) (hBs : IsElemAbelian 3 Bs) (r : MulAut Bs)
    (hfix : ∀ z ∈ D.twoKernelInG,
      (∀ h ∈ ggHyperplane Bs r, h * z = z * h) → z = 1)
    (S : Subgroup (twistedE6Group 2 1)) (hS : ggOTwoPrime S = S)
    (hNative :
      (letI := D.fieldK
       letI := D.finiteK
       ggOTwoPrime ((⊤ : Subgroup stdGroup) ⊓
         ⨅ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)),
           MonoidHom.eqLocus
             (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker (b : Bs)).toMonoidHom
             (MonoidHom.id stdGroup))) = S.map isogenyStd) :
    NsQuot.img (X ⊔ Bs)
      (QuotientGroup.mk' (D.twoKernelInG.subgroupOf (X ⊔ Bs))) (ggRankOneIn X Bs r) =
      S.map D.joinedScMap := by
  rw [original_joined_rankOne_image_from_source D hBs r hfix,
    original_source_residual_eq_of_native_marking D r S hS hNative]

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary

set_option linter.style.haveILetI false in
theorem original_joined_compact_pair_of_native_markings_forall_fields
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) (hBs : IsElemAbelian 3 Bs)
    (theta : Su (actualQuadraticSubfield 1) 2 1 3 →* twistedE6Group 2 1)
    (hinj : Function.Injective (D.joinedScMap.comp theta)) {r s : MulAut Bs}
    (hfixed : (D.joinedScMap.comp theta).range ≤ Subgroup.centralizer
      (((ggHyperplane Bs r ⊓ ggHyperplane Bs s).subgroupOf Bs).map D.joinedActor :
        Set D.joinedTwoQuotient))
    (hfree : D.twoKernelInG ⊓ Subgroup.centralizer
      (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) = ⊥)
    (hNativeR :
      (letI := D.fieldK
       letI := D.finiteK
       ggOTwoPrime ((⊤ : Subgroup stdGroup) ⊓
         ⨅ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)),
           MonoidHom.eqLocus
             (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker (b : Bs)).toMonoidHom
             (MonoidHom.id stdGroup))) =
        (B12 (actualQuadraticSubfield 1) 2 1).map (isogenyStd.comp theta))
    (hNativeS :
      (letI := D.fieldK
       letI := D.finiteK
       ggOTwoPrime ((⊤ : Subgroup stdGroup) ⊓
         ⨅ b : ↥(MonoidHom.eqLocus (s : Bs →* Bs) (MonoidHom.id Bs)),
           MonoidHom.eqLocus
             (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker (b : Bs)).toMonoidHom
             (MonoidHom.id stdGroup))) =
        (B23 (actualQuadraticSubfield 1) 2 1).map (isogenyStd.comp theta)) :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ),
      Nat.card K = (2 ^ f) ^ 2 →
      Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) →
      ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W
        (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) := by
  have hfix : ∀ z ∈ D.twoKernelInG,
      (∀ h ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs s, h * z = z * h) → z = 1 := by
    intro z hz hc
    apply Subgroup.mem_bot.mp
    rw [← hfree]
    exact ⟨hz, Subgroup.mem_centralizer_iff.mpr hc⟩
  have hfixr : ∀ z ∈ D.twoKernelInG,
      (∀ h ∈ ggHyperplane Bs r, h * z = z * h) → z = 1 :=
    fun z hz hc => hfix z hz fun h hh => hc h hh.1
  have hfixs : ∀ z ∈ D.twoKernelInG,
      (∀ h ∈ ggHyperplane Bs s, h * z = z * h) → z = 1 :=
    fun z hz hc => hfix z hz fun h hh => hc h hh.2
  have hRgen : ggOTwoPrime ((B12 (actualQuadraticSubfield 1) 2 1).map theta) =
      (B12 (actualQuadraticSubfield 1) 2 1).map theta := by
    have h := ggSu_ggOTwoPrime_range
      (card_actualQuadraticSubfield (by decide : 1 ≤ 1)) (by decide : 2 ≤ 2)
      (theta.comp (embSUid (unitaryInvolution (actualQuadraticSubfield 1) 2 1) 2))
    rw [MonoidHom.range_comp] at h
    exact h
  have hSgen : ggOTwoPrime ((B23 (actualQuadraticSubfield 1) 2 1).map theta) =
      (B23 (actualQuadraticSubfield 1) 2 1).map theta := by
    have h := ggSu_ggOTwoPrime_range
      (card_actualQuadraticSubfield (by decide : 1 ≤ 1)) (by decide : 2 ≤ 2)
      (theta.comp (embSUid (unitaryInvolution (actualQuadraticSubfield 1) 2 1) 0))
    rw [MonoidHom.range_comp] at h
    exact h
  have hR := original_joined_rankOne_image_of_native_marking D hBs r hfixr
    ((B12 (actualQuadraticSubfield 1) 2 1).map theta) hRgen (by
      rw [Subgroup.map_map]
      exact hNativeR)
  have hS := original_joined_rankOne_image_of_native_marking D hBs s hfixs
    ((B23 (actualQuadraticSubfield 1) 2 1).map theta) hSgen (by
      rw [Subgroup.map_map]
      exact hNativeS)
  rw [Subgroup.map_map] at hR hS
  exact original_joined_compact_pair_lifts_forall_fields D hBs theta hinj
    hfixed hfree hR hS

set_option linter.style.haveILetI false in
theorem original_residuals_commute_of_native
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) (hBs : IsElemAbelian 3 Bs) (r s : MulAut Bs)
    (hfree : D.twoKernelInG ⊓ Subgroup.centralizer
      (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) = ⊥)
    (hNative :
      letI := D.fieldK
      letI := D.finiteK
      ∀ a ∈ ggOTwoPrime ((⊤ : Subgroup stdGroup) ⊓
        ⨅ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)),
          MonoidHom.eqLocus
            (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker (b : Bs)).toMonoidHom
            (MonoidHom.id stdGroup)),
      ∀ c ∈ ggOTwoPrime ((⊤ : Subgroup stdGroup) ⊓
        ⨅ b : ↥(MonoidHom.eqLocus (s : Bs →* Bs) (MonoidHom.id Bs)),
          MonoidHom.eqLocus
            (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker (b : Bs)).toMonoidHom
            (MonoidHom.id stdGroup)), a * c = c * a) :
    ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs s, a * b = b * a := by
  letI := D.fieldK
  letI := D.finiteK
  letI : Finite (twistedE6Group 2 1) := finite_twistedE6Group
  let R := (⊤ : Subgroup (twistedE6Group 2 1)) ⊓
    ⨅ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)),
      MonoidHom.eqLocus (D.scAction (b : Bs)).toMonoidHom
        (MonoidHom.id (twistedE6Group 2 1))
  let S := (⊤ : Subgroup (twistedE6Group 2 1)) ⊓
    ⨅ b : ↥(MonoidHom.eqLocus (s : Bs →* Bs) (MonoidHom.id Bs)),
      MonoidHom.eqLocus (D.scAction (b : Bs)).toMonoidHom
        (MonoidHom.id (twistedE6Group 2 1))
  have hodd : Odd (Nat.card isogenyStd.ker) := by
    rw [card_ker_isogenyStd]
    decide
  have hcomm := ggOTwoPrime_commutation_of_map_of_central_odd_kernel
    isogenyStd ker_isogenyStd_le_center hodd R S (by
      rw [original_source_residual_map_native D r, original_source_residual_map_native D s]
      exact hNative)
  let hD := original_joined_quotient_datum D hBs
  have hfix : ∀ z ∈ D.twoKernelInG,
      (∀ h ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs s, h * z = z * h) → z = 1 := by
    intro z hz hc
    apply Subgroup.mem_bot.mp
    rw [← hfree]
    exact ⟨hz, Subgroup.mem_centralizer_iff.mpr hc⟩
  have hfixr : ∀ z ∈ D.twoKernelInG,
      (∀ h ∈ ggHyperplane Bs r, h * z = z * h) → z = 1 :=
    fun z hz hc => hfix z hz fun h hh => hc h hh.1
  have hfixs : ∀ z ∈ D.twoKernelInG,
      (∀ h ∈ ggHyperplane Bs s, h * z = z * h) → z = 1 :=
    fun z hz hc => hfix z hz fun h hh => hc h hh.2
  apply hD.commute_lift hfix
  rw [← hD.img_rankOneIn hfixr, ← hD.img_rankOneIn hfixs,
    original_joined_rankOne_image_from_source D hBs r hfixr,
    original_joined_rankOne_image_from_source D hBs s hfixs]
  rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
  exact (map_mul D.joinedScMap a' b').symm.trans
    ((congrArg D.joinedScMap (hcomm a' ha' b' hb')).trans (map_mul D.joinedScMap b' a'))

end CFSG.StandardType.GGFinModel
