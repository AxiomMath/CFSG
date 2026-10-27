module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTenBranches
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenAtQuotKer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineApplyInputs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCongr
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenAtStarQuot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.LThreeParabolic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeYTransport
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeOrders
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixXStarPGroup
import CFSG.GroupTheory.SylowNormalIndex
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFive
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFour
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
import CFSG.LocalAnalysis.RankThreeUC.Notation
import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
import CFSG.LocalAnalysis.RankThreeUC.WeakModules

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.GH74.GLS.Stage2.Signalizer (IsMaxParabolicP)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem isPGroup_xStar (h : TwelveCtx G M p Q H)
    (hbot : pLayerIn p H = ⊥) :
    IsPGroup p ↥(((xSub p M H).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hL : pLayerIn p H ≤ M := hbot ▸ bot_le
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  let K := Nat.card ↥H
  have hcop : Nat.Coprime p (orderOf ((y ^ p ^ K : ↥H) : G)) := by
    have h := CFSG.Walter.Huppert.coprime_orderOf_pow_card (p := p) y
    rw [← Subgroup.orderOf_coe] at h
    exact h
  have hmem : ((y ^ p ^ K : ↥H) : G) ∈ xSub p M H :=
    Subgroup.mem_subgroupOf.mp (Subgroup.pow_mem _ hy (p ^ K))
  let W : Subgroup G := Subgroup.zpowers ((y ^ p ^ K : ↥H) : G)
  have hWX : W ≤ xSub p M H := Subgroup.zpowers_le.mpr hmem
  have hWcard : Nat.Coprime p (Nat.card W) := by
    rw [Nat.card_zpowers]
    exact hcop
  have hWrel : W ≤ relPPrimeCore p H :=
    TwelveCtx.le_relPPrimeCore_of_le_xSub h hL hWcard hWX
  have hgen : ((y ^ p ^ K : ↥H) : G) ∈ relPPrimeCore p H :=
    hWrel (Subgroup.mem_zpowers _)
  have h3 : π (y ^ p ^ K) = 1 := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      h.p_prime H] at hgen
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hgen
    have hzy' : z = y ^ p ^ K := Subtype.ext hzy
    rw [← hzy']
    exact (QuotientGroup.eq_one_iff (N := primeComplementCore (G := ↥H) p) z).mpr hz
  have h1 : (π y) ^ p ^ K = 1 := by
    rw [← map_pow]
    exact h3
  have hdvd : orderOf (π y) ∣ p ^ K := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow h.p_prime).mp hdvd
  exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk⟩

private theorem xStar_le_pCore (h : TwelveCtx G M p Q H)
    (hbot : pLayerIn p H = ⊥) :
    Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) ≤
      CFSG.pCore p (StarGroup p H) := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hL : pLayerIn p H ≤ M := hbot ▸ bot_le
  have hKstar : (kStar p M H).Normal := kStar_normal_of_le hL
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  have hXeq : ((xSub p M H).subgroupOf H).map π =
      Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) := by
    rw [xSub, CFSG.AGLEmbedding.d1PlusCore]
    change Subgroup.map π (Subgroup.comap H.subtype (Subgroup.map H.subtype
      (Subgroup.comap π (Subgroup.centralizer
        (kStar p M H : Set (StarGroup p H)))))) = _
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hCp : IsPGroup p ↥(Subgroup.centralizer (kStar p M H : Set (StarGroup p H))) :=
    hXeq ▸ isPGroup_xStar h hbot
  exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup
    Subgroup.normal_centralizer hCp

private theorem xSub_le_ker_oneMap (h : TwelveCtx G M p Q H)
    (hbot : pLayerIn p H = ⊥) :
    xSub p M H ≤ ((oneMap p H).ker).map H.subtype := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let ρ : StarGroup p H →* StarQuotP p H :=
    QuotientGroup.mk' (CFSG.pCore p (StarGroup p H))
  have hXle : Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) ≤
      CFSG.pCore p (StarGroup p H) := xStar_le_pCore h hbot
  have hker : (oneMap p H).ker = (CFSG.pCore p (StarGroup p H)).comap π := by
    rw [oneMap, ← MonoidHom.comap_ker ρ π, QuotientGroup.ker_mk']
  rw [hker, xSub, CFSG.AGLEmbedding.d1PlusCore]
  exact Subgroup.map_mono (Subgroup.comap_mono hXle)

private theorem xSub_le_M_of_branchC (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hbot : pLayerIn p H = ⊥) : xSub p M H ≤ M := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  have hker : (oneMap p H).ker = (CFSG.pCore p (StarGroup p H)).comap π := by
    rw [oneMap, ← MonoidHom.comap_ker (QuotientGroup.mk' (CFSG.pCore p (StarGroup p H))) π,
      QuotientGroup.ker_mk']
  refine (xSub_le_ker_oneMap h hbot).trans ?_
  rw [hker]
  refine (Subgroup.map_mono (comap_pCore_starGroup_le_normalCore hI h)).trans ?_
  refine (Subgroup.map_mono (Subgroup.normalCore_le _)).trans ?_
  rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  exact inf_le_left

private theorem xSub_dPrime_of_branchC (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hbot : pLayerIn p H = ⊥) : ¬ d ∣ Nat.card (xSub p M H) := by
  have hle := xSub_le_ker_oneMap h hbot
  have hcard : Nat.card (xSub p M H) ∣ Nat.card (oneMap p H).ker := by
    have h1 : Nat.card (xSub p M H) ∣ Nat.card (((oneMap p H).ker).map H.subtype) :=
      Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective H.subtype_injective] at h1
  exact fun hdvd => not_dvd_card_ker_oneMap hI h hns hd (hdvd.trans hcard)

private theorem threeTenCase_of_sixThreeOneList {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp3 : p ≠ 3) (hcard : Nat.card X ≠ 1) (hlist : SixThreeOneList p X) :
    (IsSLType 2 (ZMod p) X ∨ IsPSLType 2 (ZMod p) X ∨ IsSLType 3 (ZMod p) X) ∨
      (p = 7 ∧ IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 7)))
        (fun B _ => Nat.card B = 2) X) ∨
      (p = 5 ∧
        (IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
            (fun B _ => Nat.card B = 2) X ∨
          IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
            (fun B _ => IsQ8D8Type B) X ∨
          IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) X)) ∨
      (p = 3 ∧
        (IsSLType 2 (ZMod 5) X ∨
          IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
            (fun B _ => IsQ8D8Type B) X)) := by
  rcases hlist with h1 | h2 | h3 | h4
  · rcases h1 with h1 | h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (Or.inr h1))
    · exact Or.inl (Or.inr (Or.inl h1))
    · exact (hcard h1).elim
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact (hp3 h4.1).elim

private theorem pRank_inf_le_one_of_isCyclic_sylow {d : ℕ} (hdp : d.Prime)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M))
    (hDcyc : IsCyclic ↥D) : CFSG.Open.pRank d (H ⊓ M) ≤ 1 := by
  have hfact : Fact d.Prime := ⟨hdp⟩
  obtain ⟨S, hS⟩ := hD.exists_sylow_eq_subgroupOf
  have hScyc : IsCyclic (S : Subgroup ↥(H ⊓ M)) := by
    rw [hS]
    have hDcyc' : IsCyclic ↥D := hDcyc
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hD.le).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hD.le).symm.surjective
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H ⊓ M)]
  exact pRank_le_one_of_isCyclic_sylow hdp S hScyc

private theorem isCyclic_of_isCyclic_oneImg_of_sylow (_hI : NineNineOneInput)
    (h : TwelveCtx G M p Q H) (hns : ¬ Group.IsSolvable ↥M) {d : ℕ}
    (hd : d ∈ sigmaSet G M) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M))
    (hcyc : IsCyclic ↥(oneImg p H D)) : IsCyclic ↥D :=
  isCyclic_of_isCyclic_oneImg _hI h hns hd hD.isPGroup (hD.le.trans inf_le_left) hcyc

private theorem isSylowOf_oneImg (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    CFSG.ABGLocalTools.IsSylowOf d (oneImg p H D) ⊤ := by
  have hfact : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have hDsylH : CFSG.ABGLocalTools.IsSylowOf d D H :=
    isSylowOf_H_of_isSylowOf_inf h hns hd hD hD1
  have hDsylH' : CFSG.ABGLocalTools.IsSylowOf d (D.subgroupOf H) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := d) H
      (A := D.subgroupOf H) (B := ⊤)]
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hD.le.trans inf_le_left),
      Subgroup.map_top, Subgroup.range_subtype]
  dsimp only [oneImg]
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hDsylH' ⊢
  obtain ⟨-, hDp, hDind⟩ := hDsylH'
  rw [Subgroup.relIndex_top_right] at hDind
  refine ⟨le_top, hDp.map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact fun hdvd => hDind (hdvd.trans (Subgroup.index_map_dvd
    (f := oneMap p H) (H := D.subgroupOf H)
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))))

omit [Finite G] in
private theorem oneImg_inf_eq (p : ℕ) (M H : Subgroup G) :
    oneImg p H M = oneImg p H (M ⊓ H) := by
  rw [oneImg, oneImg]
  have h : (M ⊓ H).subgroupOf H = M.subgroupOf H := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  rw [h]

private theorem twelveThreeYQuotient_of_branchC (hI : NineNineOneInput)
    (h : TwelveCtx G M p Q H) (hns : ¬ Group.IsSolvable ↥M) {d : ℕ}
    (hd : d ∈ sigmaSet G M) (hbot : pLayerIn p H = ⊥)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥)
    {B : Subgroup (StarQuotP p H)} {I Y : Subgroup ↥B} (hB : B = oneAmb p M H D)
    (hIeq : I = (oneImg p H (kSub p M H)).subgroupOf B)
    (hYeq : Y = (oneImg p H M ⊓ B).subgroupOf B)
    (hSL3I : IsSLType 3 (ZMod p) ↥I) (hmaxpar : IsMaxParabolicP p I Y)
    (hDIB : (oneImg p H D).subgroupOf B ≤ I) (hdp1 : d ∣ p + 1) :
    TwelveThreeYQuotient G M H p d := by
  have hL : pLayerIn p H ≤ M := hbot ▸ bot_le
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hd2 : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have hfactp : Fact p.Prime := ⟨h.p_prime⟩
  have hfactd : Fact d.Prime := ⟨hdp⟩
  subst hB
  obtain ⟨eI⟩ := hSL3I
  let eI' : ↥((oneImg p H (kSub p M H)).subgroupOf
      (oneAmb p M H D)) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod p) := hIeq ▸ eI
  have hp5 : 5 ≤ p := five_le_of_odd_prime_dvd_add_one h.p_prime h.p_odd hdp hd2 hdp1
  have hIn : (oneImg p H (kSub p M H)).Normal :=
    (kSub_normal_of_le hL).map (oneMap p H)
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  let eK : ↥(oneImg p H (kSub p M H)) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod p) :=
    (Subgroup.subgroupOfEquivOfLe
      (show oneImg p H (kSub p M H) ≤ oneAmb p M H D from le_sup_left)).symm.trans eI'
  have hP : IsMaxParabolicP p (oneImg p H (kSub p M H))
      (oneImg p H M ⊓ oneImg p H (kSub p M H)) := by
    refine isMaxParabolicP_oneImg_of_oneAmb (D := D) ?_
    rwa [← hIeq, ← hYeq]
  have hPeq : (oneImg p H M ⊓ oneImg p H (kSub p M H)) =
      ((M ⊓ H).subgroupOf H).map (oneMap p H) ⊓ oneImg p H (kSub p M H) := by
    rw [oneImg_inf_eq p M H, oneImg]
  have hDsyl' := isSylowOf_oneImg h hns hd hD hD1
  have hDI' : oneImg p H D ≤ oneImg p H (kSub p M H) := by
    refine CFSG.LocalCores.le_of_subgroupOf_le
      (show oneImg p H D ≤ oneAmb p M H D from le_sup_right) ?_
    rwa [hIeq] at hDIB
  exact twelveThreeYQuotient_of_isMaxParabolicP (M := M) (H := H) (p := p) (d := d)
    hp5 hdp hd2 hdp1 (A := StarQuotP p H) (oneMap p H)
    (not_dvd_card_ker_oneMap hI h hns hd) hIn eK hP hPeq hDsyl' hDI'

private theorem twelveThreeCommon_of_branchC (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hbot : pLayerIn p H = ⊥) (hrank : CFSG.Open.pRank d (H ⊓ M) ≤ 1)
    (hY : IsSimpleGroup (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) ∧
      ¬ Group.IsSolvable (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) ∧
      3 ∣ Nat.card (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))) :
    TwelveThreeCommon M p H d := by
  have hL : pLayerIn p H ≤ M := hbot ▸ bot_le
  exact
    { xSub_le_M := xSub_le_M_of_branchC hI h hbot
      xSub_normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (xSub_le_H p M H)).mpr
        (xSub_normal_of_pLayerIn_le hL)
      xSub_dPrime := xSub_dPrime_of_branchC hI h hns hd hbot
      rank_le_one := hrank
      y_simple := hY.1
      y_nonsolvable := hY.2.1
      three_dvd := hY.2.2 }

private theorem twelveThreeCaseTwo_of_branchC (h : TwelveCtx G M p Q H)
    (hbot : pLayerIn p H = ⊥) {d : ℕ}
    (hSL3 : IsSLType 3 (ZMod p) (KStarQuot p M H)) (hdp1 : d ∣ p + 1)
    (hYq : TwelveThreeYQuotient G M H p d) : TwelveThreeCaseTwo M p H d := by
  have hL : pLayerIn p H ≤ M := hbot ▸ bot_le
  refine ⟨hbot, ⟨isPConstrained_of_pLayerIn_eq_bot h.p_prime H hbot, hSL3, hdp1, hYq⟩, ?_⟩
  intro W hWX hWp
  exact TwelveCtx.le_relPPrimeCore_of_le_xSub h hL
    ((h.p_prime.coprime_iff_not_dvd).mpr hWp) hWX

theorem twelveThreeData_of_branchC (h10 : NineTenGen) (h310 : ThreeTen) (hI : NineNineOneInput)
    (h : TwelveCtx G M p Q H) (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hdH : d ∣ Nat.card (H ⊓ M : Subgroup G)) (hbot : pLayerIn p H = ⊥) (hp3 : p ≠ 3) :
    TwelveThreeData M p H d := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hd2 : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have : Fact d.Prime := ⟨hdp⟩
  have hL : pLayerIn p H ≤ M := hbot ▸ bot_le
  obtain ⟨D, hD⟩ := CFSG.ABGLocalTools.exists_isSylowOf d (H ⊓ M)
  have hk0 : 0 < (Nat.card (H ⊓ M : Subgroup G)).factorization d :=
    hdp.factorization_pos_of_dvd Nat.card_pos.ne' hdH
  have hD1 : D ≠ ⊥ := by
    intro hbotD
    have hcardD : Nat.card D = 1 := by rw [hbotD, Subgroup.card_bot]
    rw [hD.card_eq] at hcardD
    exact (Nat.one_lt_pow hk0.ne' hdp.one_lt).ne' hcardD
  let B := oneAmb p M H D
  let I := (oneImg p H (kSub p M H)).subgroupOf B
  let Dsub := (oneImg p H D).subgroupOf B
  let Y := (oneImg p H M ⊓ B).subgroupOf B
  obtain ⟨P, hpp, hp2, hdp', hd2', hdne, hIeq, hDsyl, hDne, hPsyl, hYlt, hγ, hN⟩ :=
    exists_threeTenHyp_oneAmb hI h hns hd hL hD hD1
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  obtain ⟨hlist, hcard⟩ := nineTen_branchC_of_twelveCtx h10 h hEQ hE hEc hΓ hbot
  obtain ⟨e₁⟩ := nonempty_oneImg_kSub_mulEquiv (p := p) h hL
  let e : ↥I ≃* KStarQuot p M H :=
    (Subgroup.subgroupOfEquivOfLe (show oneImg p H (kSub p M H) ≤ B from le_sup_left)).trans e₁
  have hlistI : SixThreeOneList p ↥I := SixThreeOneList.of_mulEquiv e.symm hlist
  have hcardI : Nat.card ↥I ≠ 1 := fun h1 => hcard ((Nat.card_congr e.toEquiv).symm.trans h1)
  have hcase := threeTenCase_of_sixThreeOneList hp3 hcardI hlistI
  have hconcl := h310 (↥B) I Dsub P Y p d hpp hp2 hdp' hd2' hdne hIeq hDsyl hDne hPsyl
    hYlt hγ hN hcase
  obtain ⟨hDcycB, hDIB, hSL3I, hdp1, hmaxpar⟩ := hconcl
  have hDsuble : oneImg p H D ≤ B := le_sup_right
  have hc : IsCyclic ↥(oneImg p H D) := by
    have hDsubcyc : IsCyclic ↥Dsub := hDcycB
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hDsuble).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hDsuble).surjective
  have hDcyc : IsCyclic ↥D := isCyclic_of_isCyclic_oneImg_of_sylow hI h hns hd hD hc
  have hrank := pRank_inf_le_one_of_isCyclic_sylow hdp hD hDcyc
  let eI : ↥I ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod p) := hSL3I.some
  have hSL3 : IsSLType 3 (ZMod p) (KStarQuot p M H) := ⟨e.symm.trans eI⟩
  have hYq := twelveThreeYQuotient_of_branchC hI h hns hd hbot hD hD1
    (B := B) (I := I) (Y := Y) rfl rfl rfl hSL3I hmaxpar hDIB hdp1
  have hp5 : 5 ≤ p := five_le_of_odd_prime_dvd_add_one h.p_prime h.p_odd hdp hd2 hdp1
  have hy := simple_nonsolvable_three_dvd_of_isPSLType_two
    (X := modPrimeComplement d (oPPrimeHull d (H ⊓ M))) hp5 hYq
  have hcommon := twelveThreeCommon_of_branchC hI h hns hd hbot hrank hy
  exact ⟨hcommon, Or.inl (twelveThreeCaseTwo_of_branchC h hbot hSL3 hdp1 hYq)⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
