module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.O89X
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.KFact76RankThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.LThreeTwoPowCore
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K89Sp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PO
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K89SMain
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320SLRed
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3Odd
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1U3Odd
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactF2
import CFSG.GH74.Uniqueness.Section7Lemma711
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.CoreFreeTools
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools
public import Certificates.Certificate431004
public import CFSG.GH74.AS16.Defs
public import CFSG.GH74.E2.Components
public import CFSG.GH74.E2.OddRankG
public import CFSG.GH74.E2.OuterCore
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaHPara
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.TwoLocalSylow
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreLocalIntersections
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreLocality
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecBDerived35
public import CFSG.Quasithin.Vol2.Ch11SecBL2ODone
public import CFSG.Quasithin.Vol2.Ch11SecBL2UOver
public import CFSG.Quasithin.Vol2.Ch11SecBTCStar
public import CFSG.Quasithin.Vol2.Ch11SecCFacts
public import CFSG.Quasithin.Vol2.Ch11SecCFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym4
public import CFSG.Quasithin.Vol2.Ch11SecSSym5
public import CFSG.Quasithin.Vol2.Ch11StatementsE
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.N143.QEqual
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate5007

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15

private theorem isLThreeTwoPow_subgroupOf {G : Type} [Group G] {X L : Subgroup G} (hLX : L ≤ X)
    (hL : IsLThreeTwoPow (↥L ⧸ CFSG.pCore 2 ↥L)) :
    IsLThreeTwoPow (↥(L.subgroupOf X) ⧸ CFSG.pCore 2 ↥(L.subgroupOf X)) := by
  let e : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  have hcore : (CFSG.pCore 2 ↥(L.subgroupOf X)).map e.toMonoidHom = CFSG.pCore 2 ↥L :=
    CFSG.pCore_map_iso 2 e
  let qe : (↥(L.subgroupOf X) ⧸ CFSG.pCore 2 ↥(L.subgroupOf X)) ≃*
      (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.congr _ _ e hcore
  exact R1511C.isLThreeTwoPow_of_equiv qe hL

private theorem not_dvd_card_inf_map_conj {G : Type} [Group G] [Finite G]
    {X M A : Subgroup G} (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hA : A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M) (hAX : A ≤ X)
    (hcard : Nat.card A = 3) (hrank : CFSG.Open.pRank 3 X = 1) :
    ∀ g : ↥X, g ∉ (X ⊓ M).subgroupOf X →
      ¬ 3 ∣ Nat.card ↥((X ⊓ M).subgroupOf X ⊓
        ((X ⊓ M).subgroupOf X).map (MulAut.conj g).toMonoidHom) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro g hg hdvd
  let N : Subgroup ↥X := (X ⊓ M).subgroupOf X
  obtain ⟨b, hbord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(N ⊓ N.map (MulAut.conj g).toMonoidHom)) 3 hdvd
  have hbN : (b : ↥X) ∈ N := b.2.1
  have hbNg : (b : ↥X) ∈ N.map (MulAut.conj g).toMonoidHom := b.2.2
  let BX : Subgroup ↥X := Subgroup.zpowers (b : ↥X)
  have hBXcard : Nat.card BX = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hbord]
  have hBXN : BX ≤ N := Subgroup.zpowers_le.mpr hbN
  have hBXNg : BX ≤ N.map (MulAut.conj g).toMonoidHom := Subgroup.zpowers_le.mpr hbNg
  let B : Subgroup G := BX.map X.subtype
  have hBX : B ≤ X := Subgroup.map_subtype_le _
  have hBcard : Nat.card B = 3 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, hBXcard]
  have hBM : B ≤ M := by
    rintro z ⟨y, hy, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp (hBXN hy)).2
  have hBMg : B ≤ M.map (MulAut.conj (g : G)).toMonoidHom := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨n, hnN, hn_eq⟩ := Subgroup.mem_map.mp (hBXNg hy)
    refine Subgroup.mem_map.mpr ⟨((n : ↥X) : G), (Subgroup.mem_subgroupOf.mp hnN).2, ?_⟩
    have := congrArg (fun w : ↥X => ((w : ↥X) : G)) hn_eq
    simpa [MulAut.conj_apply] using this
  obtain ⟨y, hyX, hAy⟩ :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.exists_conj_of_pRank_le_one
      Nat.prime_three (le_of_eq hrank) hAX hBX hcard hBcard
  have hAyM : A.map (MulAut.conj y).toMonoidHom ≤ M := hAy ▸ hBM
  have hyM : y ∈ M :=
    CFSG.LocalAnalysis.RankThreeUC.S15.false_of_A8_L5_aux.mem_of_map_conj_le hM hA hAyM
  have hBinvM : B.map (MulAut.conj (g : G)⁻¹).toMonoidHom ≤ M := by
    rintro z ⟨bb, hbb, rfl⟩
    obtain ⟨m, hmM, hm_eq⟩ := Subgroup.mem_map.mp (hBMg hbb)
    rw [← hm_eq]
    simpa [MulAut.conj_apply, mul_assoc] using hmM
  have hAinvM : A.map (MulAut.conj ((g : G)⁻¹ * y)).toMonoidHom ≤ M := by
    rw [← CFSG.ClassicalInvolution.Balance.map_map_conj, hAy]
    exact hBinvM
  have hginv_y_M : (g : G)⁻¹ * y ∈ M :=
    CFSG.LocalAnalysis.RankThreeUC.S15.false_of_A8_L5_aux.mem_of_map_conj_le hM hA hAinvM
  have hgM : (g : G) ∈ M := by
    have h1 : y⁻¹ * (g : G) ∈ M := by
      simpa using M.inv_mem hginv_y_M
    have h2 : y * (y⁻¹ * (g : G)) ∈ M := M.mul_mem hyM h1
    simpa [mul_assoc] using h2
  exact hg (Subgroup.mem_subgroupOf.mpr ⟨g.2, hgM⟩)

private theorem isStronglyPEmbedded_subgroupOf_inf {G : Type} [Group G] [Finite G]
    {X M A : Subgroup G} (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hA : A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M) (hAX : A ≤ X)
    (hcard : Nat.card A = 3) (hrank : CFSG.Open.pRank 3 X = 1) (hXM : ¬ X ≤ M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 ((X ⊓ M).subgroupOf X) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥X := (X ⊓ M).subgroupOf X
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hXM
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥X) ∈ N := by
      change (⟨x, hx⟩ : ↥X) ∈ (X ⊓ M).subgroupOf X
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hmem).2
  · have hA3 : Nat.card (A.subgroupOf X) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv, hcard]
    have hle : A.subgroupOf X ≤ N := by
      intro a ha
      have haA : (a : G) ∈ A := ha
      exact show (a : G) ∈ X ⊓ M from ⟨a.2, hA.1 haA⟩
    exact hA3 ▸ Subgroup.card_dvd_of_le hle
  · simpa [N] using not_dvd_card_inf_map_conj hM hA hAX hcard hrank

private theorem exists_conj_eq_of_sylow {G : Type} [Group G] [Finite G]
    {X M S : Subgroup G} (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S X) (hSM : S ≤ M)
    {m : G} (hmX : m ∈ Subgroup.normalizer (X : Set G)) (hmM : m ∈ M) :
    ∃ y ∈ X ⊓ M,
      S.map (MulAut.conj m).toMonoidHom = S.map (MulAut.conj y).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXmap : X.map (MulAut.conj m).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hmX
  have hSmSylX : CFSG.ABGLocalTools.IsSylowOf 2
      (S.map (MulAut.conj m).toMonoidHom) X := by
    have hrel : (S.map (MulAut.conj m).toMonoidHom).relIndex X = S.relIndex X := by
      have h := Subgroup.relIndex_map_map_of_injective
        (f := (MulAut.conj m).toMonoidHom) S X (MulAut.conj m).injective
      rwa [hXmap] at h
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨Subgroup.map_mono hSyl.le |>.trans (le_of_eq hXmap), hSyl.isPGroup.map _, ?_⟩
    rw [hrel]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hSyl).2.2
  have hSm_le_M : S.map (MulAut.conj m).toMonoidHom ≤ M := by
    rintro z ⟨s, hs, rfl⟩
    exact M.mul_mem (M.mul_mem hmM (hSM hs)) (M.inv_mem hmM)
  have hSm_le_inf : S.map (MulAut.conj m).toMonoidHom ≤ X ⊓ M := by
    intro z hz
    exact ⟨hSmSylX.le hz, hSm_le_M hz⟩
  have hSmSylM : CFSG.ABGLocalTools.IsSylowOf 2
      (S.map (MulAut.conj m).toMonoidHom) (X ⊓ M) := hSmSylX.of_le hSm_le_inf inf_le_left
  have hS_le_inf : S ≤ X ⊓ M := by
    intro z hz
    exact ⟨hSyl.le hz, hSM hz⟩
  have hSSylM : CFSG.ABGLocalTools.IsSylowOf 2 S (X ⊓ M) := hSyl.of_le hS_le_inf inf_le_left
  obtain ⟨y, hy, hyconj⟩ := hSSylM.exists_mem_conj hSmSylM
  refine ⟨y, hy, ?_⟩
  have hle : S.map (MulAut.conj m).toMonoidHom ≤ S.map (MulAut.conj y).toMonoidHom := by
    intro z hz
    have hz' : y⁻¹ * z * y ∈ S := (hyconj z).mp hz
    refine Subgroup.mem_map.mpr ⟨y⁻¹ * z * y, hz', ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hcard : Nat.card ↥(S.map (MulAut.conj m).toMonoidHom) =
      Nat.card ↥(S.map (MulAut.conj y).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m).injective,
      Subgroup.card_map_of_injective (MulAut.conj y).injective]
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

private theorem exists_conj_eq_of_mem_normalizer {G : Type} [Group G] [Finite G]
    {H X M S : Subgroup G} (hH : H = X ⊔ (H ⊓ M))
    (hXnorm : H ≤ Subgroup.normalizer (X : Set G))
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S X) (hSM : S ≤ M)
    {h : G} (hh : h ∈ Subgroup.normalizer (S : Set G) ⊓ H) :
    ∃ x y m : G, x ∈ X ∧ y ∈ X ⊓ M ∧ m ∈ H ⊓ M ∧ h = x * m ∧
      S.map (MulAut.conj x⁻¹).toMonoidHom = S.map (MulAut.conj y).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXH : X ≤ H := le_sup_left.trans (le_of_eq hH.symm)
  have hKH : H ⊓ M ≤ H := le_sup_right.trans (le_of_eq hH.symm)
  haveI : (X.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hXnorm
  have hsup : X.subgroupOf H ⊔ (H ⊓ M).subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hXH hKH]
    have hEq : (X ⊔ (H ⊓ M)).subgroupOf H = H.subgroupOf H := by
      rw [show X ⊔ (H ⊓ M) = H from hH.symm]
    rw [hEq, Subgroup.subgroupOf_self]
  let hHelt : ↥H := ⟨h, hh.2⟩
  have hmem : hHelt ∈ X.subgroupOf H ⊔ (H ⊓ M).subgroupOf H := by
    rw [hsup]
    exact Subgroup.mem_top hHelt
  obtain ⟨x, hx, m, hm, hxm⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := X.subgroupOf H)
      (t := (H ⊓ M).subgroupOf H)).mp hmem
  have hxG : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
  have hmG : (m : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hm
  have hh_eq : h = (x : G) * (m : G) := by
    have := congrArg (fun w : ↥H => (w : G)) hxm
    exact this.symm
  have hSconj_h : S.map (MulAut.conj h).toMonoidHom = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hh.1
  have hSconj_xm : S.map (MulAut.conj ((x : G) * (m : G))).toMonoidHom = S := by
    rw [← hh_eq]; exact hSconj_h
  have hx_inv_eq : S.map (MulAut.conj (x : G)⁻¹).toMonoidHom =
      S.map (MulAut.conj (m : G)).toMonoidHom := by
    have h1 : (S.map (MulAut.conj (m : G)).toMonoidHom).map
        (MulAut.conj (x : G)).toMonoidHom = S := by
      rw [CFSG.ClassicalInvolution.Balance.map_map_conj, hSconj_xm]
    have h2 := congrArg (fun T : Subgroup G =>
      T.map (MulAut.conj (x : G)⁻¹).toMonoidHom) h1
    rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.map_conj_inv_cancel] at h2
    exact h2.symm
  obtain ⟨y, hy, hSm_eq_Sy⟩ := exists_conj_eq_of_sylow hSyl hSM (hXnorm hmG.1) hmG.2
  exact ⟨(x : G), y, (m : G), hxG, hy, hmG, hh_eq, hx_inv_eq.trans hSm_eq_Sy⟩

private theorem normalizer_inf_le_of_eq_sup {G : Type} [Group G] [Finite G]
    {H X M S : Subgroup G} (hH : H = X ⊔ (H ⊓ M))
    (hXnorm : H ≤ Subgroup.normalizer (X : Set G))
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S X) (hSM : S ≤ M)
    (hNX : Subgroup.normalizer (S : Set G) ⊓ X ≤ M) :
    Subgroup.normalizer (S : Set G) ⊓ H ≤ M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h hh
  obtain ⟨x, y, m, hxG, hy, hmG, hh_eq, hx_inv_eq⟩ :=
    exists_conj_eq_of_mem_normalizer hH hXnorm hSyl hSM hh
  have hSxy : S.map (MulAut.conj (x * y)).toMonoidHom = S := by
    rw [← CFSG.ClassicalInvolution.Balance.map_map_conj, ← hx_inv_eq]
    simpa using
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.map_conj_inv_cancel S x⁻¹
  have hxyN : x * y ∈ Subgroup.normalizer (S : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hSxy
  have hxyX : x * y ∈ X := X.mul_mem hxG hy.1
  have hxyM : x * y ∈ M := hNX ⟨hxyN, hxyX⟩
  have hxM : x ∈ M := by
    have h := M.mul_mem hxyM (M.inv_mem hy.2)
    simpa [mul_assoc] using h
  rw [hh_eq]
  exact M.mul_mem hxM hmG.2

private theorem le_normalizer_inf_of_sylow {G : Type} [Group G] [Finite G]
    {H X SX T : Subgroup G} (hXnorm : H ≤ Subgroup.normalizer (X : Set G))
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T H) (hTeq : T ⊓ X = SX) :
    T ≤ Subgroup.normalizer (SX : Set G) := by
  intro t ht
  have htH : t ∈ H := hTsyl.le ht
  have hTmap : T.map (MulAut.conj t).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ht)
  have hXmap : X.map (MulAut.conj t).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXnorm htH)
  have hmap : (T ⊓ X).map (MulAut.conj t).toMonoidHom = T ⊓ X := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hTmap, hXmap]
  rw [hTeq] at hmap
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

private theorem exists_sylow_of_normalClosure {G : Type} [Group G] [Finite G]
    {H X M SX : Subgroup G} (hXH : X ≤ H)
    (hXnorm : H ≤ Subgroup.normalizer (X : Set G))
    (hSXsyl : CFSG.ABGLocalTools.IsSylowOf 2 SX X) (hSXM : SX ≤ M)
    (hNX : Subgroup.normalizer (SX : Set G) ⊓ X ≤ M)
    (hNH : Subgroup.normalizer (SX : Set G) ⊓ H ≤ M) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ S ≤ M ∧
      Subgroup.normalizer (S : Set G) ⊓ H ≤ M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := H ⊓ Subgroup.normalizer (SX : Set G)
  obtain ⟨S, hSK⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 K
  have hSXK : SX ≤ K := by
    intro z hz
    exact ⟨hSXsyl.le.trans hXH hz, Subgroup.le_normalizer hz⟩
  have hSXleS : SX ≤ S :=
    CFSG.GH74.Uniqueness.le_of_isSylowOf_of_isPGroup_normal hSK hSXK inf_le_right
      hSXsyl.isPGroup
  have hSKH : S ≤ H := hSK.le.trans inf_le_left
  have hSp : IsPGroup 2 S := hSK.isPGroup
  have hSpH : IsPGroup 2 (S.subgroupOf H) := hSp.comap_subtype
  obtain ⟨T_H, hST_H⟩ := hSpH.exists_le_sylow
  let T : Subgroup G := (T_H : Subgroup ↥H).map H.subtype
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T H := ⟨T_H, rfl⟩
  have hST : S ≤ T := by
    intro z hz
    exact Subgroup.mem_map.mpr ⟨⟨z, hSKH hz⟩, hST_H hz, rfl⟩
  have hTp : IsPGroup 2 T := hTsyl.isPGroup
  have hinfp : IsPGroup 2 ↥(T ⊓ X) := hTp.to_inf_left (K := X)
  have hSXle : SX ≤ T ⊓ X := by
    intro z hz
    exact ⟨hSXleS.trans hST hz, hSXsyl.le hz⟩
  have hTeq : T ⊓ X = SX := hSXsyl.eq_of_le hSXle inf_le_right hinfp
  have hTX : T ≤ Subgroup.normalizer (SX : Set G) :=
    le_normalizer_inf_of_sylow hXnorm hTsyl hTeq
  have hTK : T ≤ K := by
    intro z hz
    exact ⟨hTsyl.le hz, hTX hz⟩
  have hTeqS : T = S := hSK.eq_of_le hST hTK hTp
  have hSH : CFSG.ABGLocalTools.IsSylowOf 2 S H := hTeqS ▸ hTsyl
  have hSM : S ≤ M := by
    have hle : S ≤ K := hSK.le
    change S ≤ H ⊓ Subgroup.normalizer (SX : Set G) at hle
    rw [inf_comm] at hle
    exact hle.trans hNH
  refine ⟨S, hSH, hSM, ?_⟩
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (S : Set G) := hg.1
  have hgH : g ∈ H := hg.2
  have hgX : g ∈ Subgroup.normalizer (X : Set G) := hXnorm hgH
  have hSinfX : S ⊓ X = SX := by rw [← hTeqS, hTeq]
  have hginf : g ∈ Subgroup.normalizer ((S ⊓ X : Subgroup G) : Set G) :=
    CFSG.GH74.Uniqueness.mem_normalizer_inf_of_mem_normalizer hgN hgX
  rw [hSinfX] at hginf
  exact hNH ⟨hginf, hgH⟩

private theorem exists_isSylowOf_map_subtype {G : Type} [Group G] [Finite G]
    {X M : Subgroup G} {S₀ : Subgroup ↥X}
    (hS₀syl : CFSG.ABGLocalTools.IsSylowOf 2 S₀ ⊤)
    (hS₀N : S₀ ≤ (X ⊓ M).subgroupOf X)
    (hS₀norm : Subgroup.normalizer (S₀ : Set ↥X) ≤ (X ⊓ M).subgroupOf X) :
    ∃ SX : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 SX X ∧ SX ≤ M ∧
      Subgroup.normalizer (SX : Set G) ⊓ X ≤ M := by
  classical
  let SX : Subgroup G := S₀.map X.subtype
  have hSXsyl : CFSG.ABGLocalTools.IsSylowOf 2 SX X := by
    have h := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) X).mpr hS₀syl
    simpa [SX, Subgroup.map_top, Subgroup.range_subtype] using h
  have hSXM : SX ≤ M := by
    rintro z ⟨s, hs, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp (hS₀N hs)).2
  have hSXnorm : Subgroup.normalizer (SX : Set G) ⊓ X ≤ M := by
    intro z hz
    have hzN : z ∈ Subgroup.normalizer (SX : Set G) := hz.1
    have hzX : z ∈ X := hz.2
    let zX : ↥X := ⟨z, hzX⟩
    have hzS : SX.map (MulAut.conj z).toMonoidHom = SX :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hzN
    have hS₀map : S₀.map (MulAut.conj zX).toMonoidHom = S₀ := by
      refine Subgroup.map_injective (f := X.subtype) X.subtype_injective ?_
      calc (S₀.map (MulAut.conj zX).toMonoidHom).map X.subtype
          = (S₀.map X.subtype).map (MulAut.conj z).toMonoidHom := by
            rw [Subgroup.map_map, Subgroup.map_map]
            congr 1
        _ = SX.map (MulAut.conj z).toMonoidHom := rfl
        _ = SX := hzS
        _ = S₀.map X.subtype := rfl
    have hzNX : zX ∈ (X ⊓ M).subgroupOf X :=
      hS₀norm (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hS₀map)
    exact (Subgroup.mem_subgroupOf.mp hzNX).2
  exact ⟨SX, hSXsyl, hSXM, hSXnorm⟩

private theorem exists_sylow_norm_le_of_k89Sp {G : Type} [Group G] [Finite G]
    (hK89 : K89Sp) (hC : CStarGen G) {H X M L A : Subgroup G}
    (hXH : X ≤ H) (hHne : H ≠ ⊤) (hXM : ¬ X ≤ M)
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hA : A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M) (hAX : A ≤ X)
    (hcard : Nat.card A = 3) (hrank : CFSG.Open.pRank 3 X = 1)
    (hLle : L ≤ H ⊓ M) (hLX : L ≤ X)
    (hLq : IsLThreeTwoPow (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ SX : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 SX X ∧ SX ≤ M ∧
      Subgroup.normalizer (SX : Set G) ⊓ X ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥X := (X ⊓ M).subgroupOf X
  have hNsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 N :=
    isStronglyPEmbedded_subgroupOf_inf hM hA hAX hcard hrank hXM
  have hKX : CFSG.Open.IsKGroup ↥X := by
    haveI : IsSimpleGroup G := hC.simple
    have hXtop : X ≠ ⊤ := fun htop => hHne (top_le_iff.mp (htop ▸ hXH))
    exact CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper hC.kProper hXtop
  have hNrank : CFSG.Open.pRank 3 N ≤ 1 := by
    have h1 : CFSG.Open.pRank 3 ((X ⊓ M).subgroupOf X) =
        CFSG.Open.pRank 3 (X ⊓ M) := by
      have hmap : ((X ⊓ M).subgroupOf X).map X.subtype = M ⊓ X := by
        rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left, inf_comm]
      have h2 : CFSG.Open.pRank 3 (M ⊓ X) =
          CFSG.Open.pRank 3 ((X ⊓ M).subgroupOf X) := by
        simpa [hmap] using
          (CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective
            (p := 3) (by norm_num) X.subtype X.subtype_injective
            ((X ⊓ M).subgroupOf X))
      calc CFSG.Open.pRank 3 ((X ⊓ M).subgroupOf X)
          = CFSG.Open.pRank 3 (M ⊓ X) := h2.symm
        _ = CFSG.Open.pRank 3 (X ⊓ M) := by rw [inf_comm]
    rw [h1]
    calc CFSG.Open.pRank 3 (X ⊓ M) ≤ CFSG.Open.pRank 3 X :=
          CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left
      _ = 1 := hrank
  have hLN : L.subgroupOf X ≤ N := by
    intro l hl
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    exact Subgroup.mem_subgroupOf.mpr
      ⟨hLX hlL, hLle.trans inf_le_right hlL⟩
  have hLqX : IsLThreeTwoPow
      (↥(L.subgroupOf X) ⧸ CFSG.pCore 2 ↥(L.subgroupOf X)) :=
    isLThreeTwoPow_subgroupOf hLX hLq
  obtain ⟨S₀, hS₀syl, hS₀N, hS₀norm⟩ :=
    hK89 ↥X hKX N (L.subgroupOf X) hNsp hNrank hLN hLqX
  exact exists_isSylowOf_map_subtype hS₀syl hS₀N hS₀norm


section Certificates


private theorem k89Sp_holds
    : K89Sp :=
  CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof.K89Sp_of
    (And.intro CFSG.LocalAnalysis.RankThreeUC.S15.F1Proof.f1L3Odd_proved
      CFSG.LocalAnalysis.RankThreeUC.S15.F1Proof.f1U3Odd_proved)
    CFSG.LocalAnalysis.RankThreeUC.S15.KFactL32OddFix_holds

theorem o89At_of_kFact76MaxRankThree
    (h76 : KFact76MaxRankThree)
    {G : Type} [Group G] [Finite G] (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O89At G M := by
  classical
  have hK89 : K89Sp := k89Sp_holds
  intro H hH hH3 L hLle hcomp hrk hLq A hAL hAc hAu hweak
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL3 : IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L) :=
    isLThreeTwoPow_pPrimeCore_of_pCore hLq
  have h : Hyp83 M H L A := Hyp83.mk_of_args H hH L hLle hcomp hrk A hAL hAc hAu hweak
  let X : Subgroup G := CFSG.Goldschmidt.normalClosureIn H A
  have hXH : X ≤ H := CFSG.Goldschmidt.Sec8.normalClosureIn_le_self H A
  have hXnorm : H ≤ Subgroup.normalizer (X : Set G) :=
    CFSG.Goldschmidt.Sec8.le_normalizer_normalClosureIn H A
  have hAX : A ≤ X := CFSG.Goldschmidt.Sec8.le_normalClosureIn
    (hAL.trans (hLle.trans inf_le_left))
  have hLX : L ≤ X := le_normalClosure_of_isPComponent h hL3
  have hXrank : CFSG.Open.pRank 3 X = 1 :=
    pRank_three_normalClosure_eq_one h76 hC hM h hL3 hH3
  have hHsup : H = X ⊔ (H ⊓ M) := eq_sup_inf_of_pRank_one h76 hC hM h hL3 hH3
  by_cases hXM : X ≤ M
  · have hHM : H ≤ M := by
      rw [hHsup]
      exact sup_le hXM inf_le_right
    obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 H
    exact ⟨S, hS, hS.le.trans hHM, inf_le_right.trans hHM⟩
  · haveI : IsSimpleGroup G := hC.simple
    have hHne : H ≠ ⊤ :=
      CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hC.nonab H h.twoLocal
    obtain ⟨SX, hSXsyl, hSXM, hSXnorm⟩ :=
      exists_sylow_norm_le_of_k89Sp hK89 hC hXH hHne hXM hM hAu hAX hAc hXrank hLle hLX hLq
    have hNHXM : Subgroup.normalizer (SX : Set G) ⊓ H ≤ M :=
      normalizer_inf_le_of_eq_sup hHsup hXnorm hSXsyl hSXM hSXnorm
    obtain ⟨S, hS, hSM, hSN⟩ :=
      exists_sylow_of_normalClosure hXH hXnorm hSXsyl hSXM hSXnorm hNHXM
    exact ⟨S, hS, hSM, hSN⟩

theorem o89At_of_kFact76Max
    (h76 : KFact76Max)
    {G : Type} [Group G] [Finite G] (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O89At G M :=
  o89At_of_kFact76MaxRankThree (kFact76MaxRankThree_of_kFact76Max h76) hC hM

theorem o89Gen_of_kFact76MaxRankThree
    (h76 : KFact76MaxRankThree) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O89Gen := by
  intro G _ _ hC M hM _ _
  exact o89At_of_kFact76MaxRankThree h76 hC hM

theorem o89Gen_of_kFact76Max
    (h76 : KFact76Max) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O89Gen :=
  o89Gen_of_kFact76MaxRankThree (kFact76MaxRankThree_of_kFact76Max h76)

end Certificates

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
