module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenOneI
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.Base
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenCompGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenLayerGen
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateLinear
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.PartOne.KF.F128Count
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate16005
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8052

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

private theorem starImg_sSup (p : ℕ) (H : Subgroup G) (S : Set (Subgroup G))
    (hS : ∀ Y ∈ S, Y ≤ H) : starImg p H (sSup S) = sSup (starImg p H '' S) := by
  have hsup : sSup S ≤ H := sSup_le hS
  have hsub : (sSup S).subgroupOf H = sSup ((·.subgroupOf H) '' S) := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hsup,
      (Subgroup.gc_map_comap H.subtype).l_sSup_eq_sSup_image]
    congr 1
    ext Y
    constructor
    · intro hY
      exact ⟨Y.subgroupOf H, ⟨Y, hY, rfl⟩,
        Subgroup.map_subgroupOf_eq_of_le (hS Y hY)⟩
    · rintro ⟨Z, ⟨W, hW, rfl⟩, hZY⟩
      rw [Subgroup.map_subgroupOf_eq_of_le (hS W hW)] at hZY
      rwa [← hZY]
  unfold starImg
  rw [hsub, (Subgroup.gc_map_comap
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))).l_sSup_eq_sSup_image]
  congr 1
  ext Y
  constructor
  · rintro ⟨W, ⟨Z, hZ, rfl⟩, rfl⟩
    exact ⟨Z, hZ, rfl⟩
  · rintro ⟨Z, hZ, rfl⟩
    exact ⟨Z.subgroupOf H, ⟨Z, hZ, rfl⟩, rfl⟩

private theorem inf_sup_le_of_normal_right {X : Type*} [Group X] {K B D : Subgroup X}
    (hK : K.Normal) (hDB : D ≤ B) : B ⊓ (K ⊔ D) ≤ (B ⊓ K) ⊔ D := by
  letI := hK
  intro x hx
  have hxK : x ∈ K ⊔ D := hx.2
  change x ∈ (↑(K ⊔ D) : Set X) at hxK
  rw [Subgroup.normal_mul K D] at hxK
  obtain ⟨k, hk, d, hd, rfl⟩ := hxK
  have hdB : d ∈ B := hDB hd
  have hkB : k ∈ B := by
    have h1 : (k * d) * d⁻¹ ∈ B := B.mul_mem hx.1 (B.inv_mem hdB)
    simpa [mul_assoc] using h1
  exact Subgroup.mul_subset (SetLike.coe_subset_coe.mpr le_sup_left)
    (SetLike.coe_subset_coe.mpr le_sup_right) ⟨k, ⟨hkB, hk⟩, d, hd, rfl⟩

namespace NineSettingGen

theorem kStar_eq_sSup_of_not_le (h : NineSettingGen G M p Q H E k) (hL : ¬ pLayerIn p H ≤ M) :
    kStar p M H =
      sSup {C : Subgroup (StarGroup p H) | CFSG.IsComponent C ∧ ¬ C ≤ starImg p H M} := by
  have hkSub : kSub p M H = sSup {Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M} := by
    unfold kSub
    rw [if_neg hL]
  rw [kStar_eq_starImg, hkSub,
    starImg_sSup p H _ (fun Y hY => hY.1.1)]
  congr 1
  ext C
  constructor
  · rintro ⟨J, hJ, rfl⟩
    exact ⟨isComponent_starImg hJ.1,
      fun hle => hJ.2 ((h.le_iff_starImg_le hJ.1.1).mpr hle)⟩
  · rintro ⟨hC, hCM⟩
    obtain ⟨J, hJ, hJeq⟩ := exists_isPComponentIn_starImg_eq h.prime hC
    exact ⟨J, ⟨hJ, fun hJM => hCM (hJeq ▸ (h.le_iff_starImg_le hJ.1).mp hJM)⟩, hJeq⟩

theorem layer_eq_kStar_sup_of_not_le (h : NineSettingGen G M p Q H E k)
    (hL : ¬ pLayerIn p H ≤ M) :
    CFSG.layer (StarGroup p H) = kStar p M H ⊔
      sSup {C : Subgroup (StarGroup p H) | CFSG.IsComponent C ∧ C ≤ starImg p H M} := by
  rw [CFSG.layer.eq_sSup, h.kStar_eq_sSup_of_not_le hL, ← sSup_union]
  congr 1
  ext C
  simp only [Set.mem_setOf_eq, Set.mem_union]
  tauto

theorem kSub_normal_of_top_le (h : NineSettingGen G M p Q H E k) (hL : ¬ pLayerIn p H ≤ M)
    (hH : (⊤ : Subgroup (StarGroup p H)) ≤ (CFSG.layer (StarGroup p H) ⊔
      centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))) ⊔ starImg p H M) :
    ((kSub p M H).subgroupOf H).Normal := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  let Lstar : Subgroup (StarGroup p H) := CFSG.layer (StarGroup p H)
  let Ystar : Subgroup (StarGroup p H) :=
    centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))
  let Mstar : Subgroup (StarGroup p H) := starImg p H M
  let Ustar : Subgroup (StarGroup p H) := Lstar ⊔ Ystar
  let U : Subgroup G := (Ustar.comap π).map H.subtype
  have hH' : (⊤ : Subgroup (StarGroup p H)) ≤ Ustar ⊔ Mstar := hH
  have hcomap : (⊤ : Subgroup ↥H) ≤ Ustar.comap π ⊔ Mstar.comap π := by
    have hmono := Subgroup.comap_mono (f := π) hH'
    rwa [Subgroup.comap_top,
      ← Subgroup.comap_sup_eq (f := π) Ustar Mstar (QuotientGroup.mk'_surjective O)] at hmono
  have hmap_top : (⊤ : Subgroup ↥H).map H.subtype = H := by
    apply le_antisymm (Subgroup.map_subtype_le ⊤)
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, trivial, rfl⟩
  have hO_le : O.map H.subtype ≤ H ⊓ M := by
    refine le_inf (Subgroup.map_subtype_le O) ?_
    change (primeComplementCore (G := ↥H) p).map H.subtype ≤ M
    rw [← nineTenGen_relPPrimeCore_eq_map h.prime H]
    exact h.relPPrimeCore_le
  have hMcomap : Mstar.comap π = M.subgroupOf H ⊔ O := by
    change (starImg p H M).comap π = M.subgroupOf H ⊔ O
    unfold starImg
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hM_le : (Mstar.comap π).map H.subtype ≤ H ⊓ M := by
    rw [hMcomap, Subgroup.map_sup]
    refine sup_le ?_ hO_le
    rw [Subgroup.subgroupOf_map_subtype]
    exact le_inf inf_le_right inf_le_left
  have hHle : H ≤ U ⊔ (H ⊓ M) := by
    have hmap := Subgroup.map_mono (f := H.subtype) hcomap
    rw [hmap_top, Subgroup.map_sup] at hmap
    exact hmap.trans (sup_le_sup_left hM_le U)
  have hInf_le : H ⊓ M ≤ normalizer (kSub p M H : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact conj_mem_kSub hy.1 hy.2 ha
    · intro hconj
      have h1 : y⁻¹ * (y * a * y⁻¹) * (y⁻¹)⁻¹ ∈ kSub p M H :=
        conj_mem_kSub (H.inv_mem hy.1) (M.inv_mem hy.2) hconj
      have h2 : y⁻¹ * (y * a * y⁻¹) * (y⁻¹)⁻¹ = a := by group
      rwa [h2] at h1
  have hcompNorm : Ustar ≤ compNormalizer (StarGroup p H) :=
    sup_le layer_le_compNormalizer centralizer_layer_le_compNormalizer
  have hU_le : U ≤ normalizer (kSub p M H : Set G) := by
    have key : ∀ z : ↥H, π z ∈ Ustar → ∀ a ∈ kSub p M H,
        (z : G) * a * (z : G)⁻¹ ∈ kSub p M H := by
      intro z hz a ha
      unfold kSub at ha ⊢
      rw [if_neg hL] at ha ⊢
      refine conj_mem_sSup (S := {Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M}) ?_ ha
      intro Y hY
      have hY1 : IsPComponentIn p (Y.map (MulAut.conj (z : G)).toMonoidHom) H :=
        isPComponentIn_conj hY.1 z.2
      refine ⟨hY1, ?_⟩
      intro hle
      have hsub : (Y.map (MulAut.conj (z : G)).toMonoidHom).subgroupOf H =
          (Y.subgroupOf H).map (MulAut.conj z).toMonoidHom := by
        ext t
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        constructor
        · rintro ⟨c, hc, hcz⟩
          refine ⟨⟨c, hY.1.1 hc⟩, hc, ?_⟩
          exact Subtype.ext (by simpa using hcz)
        · rintro ⟨b, hb, hbz⟩
          refine ⟨b, hb, ?_⟩
          simpa using congrArg Subtype.val hbz
      have hcomp : π.comp (MulAut.conj z).toMonoidHom =
          (MulAut.conj (π z)).toMonoidHom.comp π := by
        ext g
        simp [MulAut.conj_apply]
      have hstar : starImg p H (Y.map (MulAut.conj (z : G)).toMonoidHom) =
          (starImg p H Y).map (MulAut.conj (π z)).toMonoidHom := by
        unfold starImg
        rw [hsub, Subgroup.map_map, hcomp, ← Subgroup.map_map]
      have hnorm : π z ∈ normalizer (starImg p H Y : Set (StarGroup p H)) :=
        mem_compNormalizer_iff.mp (hcompNorm hz) (starImg p H Y) (isComponent_starImg hY.1)
      have hfix : (starImg p H Y).map (MulAut.conj (π z)).toMonoidHom = starImg p H Y :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm
      have hEq : starImg p H (Y.map (MulAut.conj (z : G)).toMonoidHom) = starImg p H Y := by
        rw [hstar, hfix]
      have hYeq : Y.map (MulAut.conj (z : G)).toMonoidHom = Y :=
        eq_of_starImg_eq h.prime hY1 hY.1 hEq
      rw [hYeq] at hle
      exact hY.2 hle
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      exact key z hz a ha
    · intro hconj
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      let z' : ↥H := ⟨(z : G)⁻¹, H.inv_mem z.2⟩
      have hz' : π z' ∈ Ustar := by
        have hzinv : z' = z⁻¹ := Subtype.ext rfl
        rw [hzinv, map_inv]
        exact Ustar.inv_mem hz
      have h1 := key z' hz' ((z : G) * a * (z : G)⁻¹) hconj
      have h2 : (z' : G) * ((z : G) * a * (z : G)⁻¹) * (z' : G)⁻¹ = a := by
        change (z : G)⁻¹ * ((z : G) * a * (z : G)⁻¹) * ((z : G)⁻¹)⁻¹ = a
        group
      rwa [h2] at h1
  have hHnorm : H ≤ H ⊓ normalizer (kSub p M H : Set G) := by
    refine hHle.trans (sup_le ?_ ?_)
    · exact le_inf (Subgroup.map_subtype_le (Ustar.comap π)) hU_le
    · exact le_inf inf_le_left hInf_le
  rw [Subgroup.normal_subgroupOf_iff (kSub_le p M H)]
  intro a y ha hy
  have hyB : y ∈ H ⊓ normalizer (kSub p M H : Set G) := hHnorm hy
  exact (Subgroup.mem_normalizer_iff.mp hyB.2 a).mp ha

section Certified


theorem eq_kSub_sup_of_top_le (h : NineSettingGen G M p Q H E k)
    (hL : ¬ pLayerIn p H ≤ M)
    (hH : (⊤ : Subgroup (StarGroup p H)) ≤ (CFSG.layer (StarGroup p H) ⊔
      centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))) ⊔ starImg p H M)
    (hY : centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤ starImg p H M) :
    H = kSub p M H ⊔ (H ⊓ M) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  let Kstar : Subgroup (StarGroup p H) := kStar p M H
  let Mstar : Subgroup (StarGroup p H) := starImg p H M
  let A : Subgroup (StarGroup p H) :=
    sSup {C : Subgroup (StarGroup p H) | CFSG.IsComponent C ∧ C ≤ Mstar}
  have hlayer : CFSG.layer (StarGroup p H) = Kstar ⊔ A :=
    h.layer_eq_kStar_sup_of_not_le hL
  have hA_le : A ≤ Mstar := sSup_le fun C hC => hC.2
  have htop : (⊤ : Subgroup (StarGroup p H)) ≤ Kstar ⊔ Mstar := by
    refine hH.trans (sup_le ?_ le_sup_right)
    refine sup_le ?_ (hY.trans le_sup_right)
    rw [hlayer]
    exact sup_le le_sup_left (hA_le.trans le_sup_right)
  have hcomap : (⊤ : Subgroup ↥H) ≤ Kstar.comap π ⊔ Mstar.comap π := by
    have hmono := Subgroup.comap_mono (f := π) htop
    rwa [Subgroup.comap_top,
      ← Subgroup.comap_sup_eq (f := π) Kstar Mstar (QuotientGroup.mk'_surjective O)] at hmono
  have hmap_top : (⊤ : Subgroup ↥H).map H.subtype = H := by
    apply le_antisymm (Subgroup.map_subtype_le ⊤)
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, trivial, rfl⟩
  have hO_le : O.map H.subtype ≤ H ⊓ M := by
    refine le_inf (Subgroup.map_subtype_le O) ?_
    change (primeComplementCore (G := ↥H) p).map H.subtype ≤ M
    rw [← nineTenGen_relPPrimeCore_eq_map h.prime H]
    exact h.relPPrimeCore_le
  have hKcomap : Kstar.comap π = (kSub p M H).subgroupOf H ⊔ O := by
    change (starImg p H (kSub p M H)).comap π = (kSub p M H).subgroupOf H ⊔ O
    unfold starImg
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hMcomap : Mstar.comap π = M.subgroupOf H ⊔ O := by
    change (starImg p H M).comap π = M.subgroupOf H ⊔ O
    unfold starImg
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hK_le : (Kstar.comap π).map H.subtype ≤ kSub p M H ⊔ (H ⊓ M) := by
    rw [hKcomap, Subgroup.map_sup]
    refine sup_le ?_ (hO_le.trans le_sup_right)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (kSub_le p M H)]
    exact le_sup_left
  have hM_le' : (Mstar.comap π).map H.subtype ≤ H ⊓ M := by
    rw [hMcomap, Subgroup.map_sup]
    refine sup_le ?_ hO_le
    rw [Subgroup.subgroupOf_map_subtype]
    exact le_inf inf_le_right inf_le_left
  have hM_le : (Mstar.comap π).map H.subtype ≤ kSub p M H ⊔ (H ⊓ M) :=
    hM_le'.trans le_sup_right
  have hHle : H ≤ kSub p M H ⊔ (H ⊓ M) := by
    have hmap := Subgroup.map_mono (f := H.subtype) hcomap
    rw [hmap_top, Subgroup.map_sup] at hmap
    exact hmap.trans (sup_le hK_le hM_le)
  exact le_antisymm hHle (sup_le (kSub_le p M H) inf_le_left)

theorem xSub_le_of_centralizer_le (h713 : SevenOneThree) (hI : NineTenInputs)
    (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) (hNQ : normalizer (Q : Set G) ≤ M)
    (hQN : starImg p H Q ≤ compNormalizer (StarGroup p H)) (hL : ¬ pLayerIn p H ≤ M)
    (hY : centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤ starImg p H M) :
    xSub p M H ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hH := h.top_le_layer_sup_centralizer_sup h713 hI hH2 hp hQ hNQ hQN
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  let Kstar : Subgroup (StarGroup p H) := kStar p M H
  let Mstar : Subgroup (StarGroup p H) := starImg p H M
  let Xstar : Subgroup (StarGroup p H) := centralizer (Kstar : Set (StarGroup p H))
  let Qstar : Subgroup (StarGroup p H) := starImg p H Q
  let B : Subgroup (StarGroup p H) := Qstar ⊔ Xstar
  let Lstar : Subgroup (StarGroup p H) := CFSG.layer (StarGroup p H)
  let Ystar : Subgroup (StarGroup p H) :=
    centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))
  let A : Subgroup (StarGroup p H) :=
    sSup {C : Subgroup (StarGroup p H) | CFSG.IsComponent C ∧ C ≤ Mstar}
  have hKnorm : Kstar.Normal :=
    (h.kSub_normal_of_top_le hL hH).map π (QuotientGroup.mk'_surjective O)
  haveI : Kstar.Normal := hKnorm
  have hlayer : CFSG.layer (StarGroup p H) = Kstar ⊔ A :=
    h.layer_eq_kStar_sup_of_not_le hL
  have hA_le : A ≤ Mstar := sSup_le fun C hC => hC.2
  have hKleL : Kstar ≤ CFSG.layer (StarGroup p H) := by
    have h1 : Kstar ≤ Kstar ⊔ A := le_sup_left
    rwa [← hlayer] at h1
  have hA_X : A ≤ Xstar := by
    have hAc := sSup_le_centralizer_sSup (X := StarGroup p H) (A := Mstar)
    rw [← h.kStar_eq_sSup_of_not_le hL] at hAc
    exact hAc
  have hY_X : Ystar ≤ Xstar :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hKleL)
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf p Qstar B :=
    (h.isSylowOf_starImg_top hQ).of_le le_sup_left le_top
  have hNindex : ¬ p ∣ (compNormalizer (StarGroup p H)).index :=
    h.not_dvd_index_compNormalizer hQ hQN
  have hNormQ : normalizer (Qstar : Set (StarGroup p H)) ≤ Mstar :=
    h.normalizer_starImg_le h.Q_le_H hQ.isPGroup hNQ
  have hF : B ≤ (B ⊓ (Lstar ⊔ Ystar)) ⊔ Mstar :=
    h.le_inf_sup_starImg h713 hI hH2 hp hNindex hQsyl hNormQ
  have hP_le_Q : B ⊓ Kstar ≤ Qstar := by
    obtain ⟨Syl, hSyl⟩ := hQsyl
    let f : ↥(B ⊓ Kstar) →* StarGroup p H ⧸ Xstar :=
      (QuotientGroup.mk' Xstar).comp (B ⊓ Kstar).subtype
    have hker_le : f.ker ≤ (CFSG.pCore p (StarGroup p H)).subgroupOf (B ⊓ Kstar) := by
      intro z hz
      have hz1 : (QuotientGroup.mk' Xstar) (z : StarGroup p H) = 1 := hz
      have hzX : (z : StarGroup p H) ∈ Xstar :=
        (QuotientGroup.eq_one_iff (N := Xstar) _).mp hz1
      have hzK : (z : StarGroup p H) ∈ Kstar := z.2.2
      have hY : Kstar ⊓ Xstar ≤ Ystar := by
        intro w hw
        show w ∈ centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))
        rw [hlayer, Subgroup.mem_centralizer_iff]
        intro l hl
        rw [Subgroup.normal_mul Kstar A] at hl
        obtain ⟨k, hk, a, ha, rfl⟩ := hl
        have hwa : w * a = a * w :=
          (Subgroup.mem_centralizer_iff.mp (hA_X ha)) w hw.1
        have hwk : k * w = w * k :=
          (Subgroup.mem_centralizer_iff.mp hw.2) k hk
        calc (k * a) * w = k * (a * w) := by group
          _ = k * (w * a) := by rw [hwa]
          _ = (k * w) * a := by group
          _ = (w * k) * a := by rw [hwk]
          _ = w * (k * a) := by group
      have h1 : Kstar ⊓ Xstar ≤ CFSG.pCore p (StarGroup p H) :=
        (le_inf (inf_le_left.trans hKleL) hY).trans
          (layer_inf_centralizer_le_pCore h.prime H)
      exact h1 ⟨hzK, hzX⟩
    have hker_p : IsPGroup p f.ker :=
      ((CFSG.pCore_isPGroup (p := p) (G := StarGroup p H)).comap_subtype
        (K := B ⊓ Kstar)).to_le hker_le
    have hQstar_p : IsPGroup p Qstar := (h.isSylowOf_starImg_top hQ).isPGroup
    have hrange_le : f.range ≤ Qstar.map (QuotientGroup.mk' Xstar) := by
      have hfr : f.range = (B ⊓ Kstar).map (QuotientGroup.mk' Xstar) := by
        change ((QuotientGroup.mk' Xstar).comp (B ⊓ Kstar).subtype).range = _
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [hfr]
      calc (B ⊓ Kstar).map (QuotientGroup.mk' Xstar)
          ≤ B.map (QuotientGroup.mk' Xstar) := Subgroup.map_mono inf_le_left
        _ = (Qstar ⊔ Xstar).map (QuotientGroup.mk' Xstar) := rfl
        _ = Qstar.map (QuotientGroup.mk' Xstar) ⊔
            Xstar.map (QuotientGroup.mk' Xstar) := by rw [Subgroup.map_sup]
        _ = Qstar.map (QuotientGroup.mk' Xstar) := by
            rw [show Xstar.map (QuotientGroup.mk' Xstar) = ⊥ from
              (Subgroup.map_eq_bot_iff Xstar).mpr
                (le_of_eq (QuotientGroup.ker_mk' (N := Xstar)).symm), sup_bot_eq]
    have hrange_p : IsPGroup p f.range :=
      (hQstar_p.map (QuotientGroup.mk' Xstar)).to_le hrange_le
    have hPp : IsPGroup p ↥(B ⊓ Kstar) := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hker_p
      obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hrange_p
      refine IsPGroup.of_card (n := a + b) ?_
      rw [← Subgroup.card_ker_mul_card_range f, ha, hb, pow_add]
    have hKn : ((B ⊓ Kstar).subgroupOf B).Normal := by
      rw [Subgroup.inf_subgroupOf_left Kstar B]
      exact hKnorm.subgroupOf B
    have hPp' : IsPGroup p ((B ⊓ Kstar).subgroupOf B) :=
      hPp.comap_subtype (K := B)
    haveI : ((B ⊓ Kstar).subgroupOf B).Normal := hKn
    have hle := IsPGroup.le_sylow_of_normal hPp' Syl
    have hmap := Subgroup.map_mono (f := B.subtype) hle
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left, hSyl] at hmap
    exact hmap
  have hBLY_M : B ⊓ (Lstar ⊔ Ystar) ≤ Mstar := by
    have hAX_B : A ⊔ Ystar ≤ B :=
      sup_le (hA_X.trans le_sup_right) (hY_X.trans le_sup_right)
    have hded : B ⊓ (Kstar ⊔ (A ⊔ Ystar)) ≤ (B ⊓ Kstar) ⊔ (A ⊔ Ystar) :=
      inf_sup_le_of_normal_right hKnorm hAX_B
    have hstep : B ⊓ (Lstar ⊔ Ystar) ≤ Qstar ⊔ (A ⊔ Ystar) := by
      calc B ⊓ (Lstar ⊔ Ystar) = B ⊓ (Kstar ⊔ (A ⊔ Ystar)) := by
              rw [show Lstar = Kstar ⊔ A from hlayer, sup_assoc]
        _ ≤ (B ⊓ Kstar) ⊔ (A ⊔ Ystar) := hded
        _ ≤ Qstar ⊔ (A ⊔ Ystar) := sup_le_sup_right hP_le_Q _
    exact hstep.trans (sup_le (starImg_mono h.Q_le_M) (sup_le hA_le hY))
  have hB_M : B ≤ Mstar := hF.trans (sup_le hBLY_M le_rfl)
  have hstar : starImg p H (xSub p M H) ≤ Mstar := by
    rw [starImg_xSub]
    exact le_sup_right.trans hB_M
  have hx_le : xSub p M H ≤ H := by
    unfold xSub CFSG.AGLEmbedding.d1PlusCore
    exact Subgroup.map_subtype_le _
  exact (h.le_iff_starImg_le hx_le).mpr hstar

theorem nineTenOne_of_centralizer_le (h713 : SevenOneThree) (hI : NineTenInputs)
    (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) (hNQ : normalizer (Q : Set G) ≤ M)
    (hQN : starImg p H Q ≤ compNormalizer (StarGroup p H)) (hL : ¬ pLayerIn p H ≤ M)
    (hY : centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤ starImg p H M) :
    NineTenOne p M H := by
  have hH := h.top_le_layer_sup_centralizer_sup h713 hI hH2 hp hQ hNQ hQN
  exact Or.inl ⟨h.xSub_le_of_centralizer_le h713 hI hH2 hp hQ hNQ hQN hL hY,
    h.eq_kSub_sup_of_top_le hL hH hY, h.kSub_normal_of_top_le hL hH⟩

theorem not_centralizer_le_of_le (h713 : SevenOneThree) (hI : NineTenInputs)
    (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) (hNQ : normalizer (Q : Set G) ≤ M)
    (hQN : starImg p H Q ≤ compNormalizer (StarGroup p H)) (hL : pLayerIn p H ≤ M) :
    ¬ centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤ starImg p H M := by
  intro hY
  have hH := h.top_le_layer_sup_centralizer_sup h713 hI hH2 hp hQ hNQ hQN
  have hLle : CFSG.layer (StarGroup p H) ≤ starImg p H M := (h.pLayerIn_le_iff).mp hL
  have htop : (⊤ : Subgroup (StarGroup p H)) ≤ starImg p H M :=
    hH.trans (sup_le (sup_le hLle hY) le_rfl)
  have hHM : starImg p H H ≤ starImg p H M := by
    rw [starImg_self]
    exact htop
  exact h.not_le ((h.le_iff_starImg_le le_rfl).mpr hHM)

end Certified

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
