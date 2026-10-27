module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineSocle
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeBranchNotLe
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeCaseSporOf
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeOrders
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.RankThree.PartOne.S8.Statements
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineApply
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeYTransport
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.LThreeParabolic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenBasics
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenConstrained
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenDvdP1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveA
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

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem isCyclic_of_isCyclic_starImg (h : TwelveCtx G M p Q H) {d : ℕ} (hdp : d.Prime)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) {D : Subgroup G} (hDH : D ≤ H)
    (hDd : IsPGroup d D) (hc : IsCyclic ↥(starImg p H D)) : IsCyclic ↥D := by
  have : Fact d.Prime := ⟨hdp⟩
  have hO := not_dvd_card_primeComplementCore_of_twelveCtx h hXM
  let e : ↥(D.subgroupOf H) ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDH
  let f : ↥(D.subgroupOf H) →* ↥(starImg p H D) :=
    (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
      (G := ↥H) p)).subgroupMap (D.subgroupOf H)
  have hfker : f.ker = ⊥ := by
    apply Subgroup.card_eq_one.mp
    have hdiv1 : Nat.card f.ker ∣ Nat.card (D.subgroupOf H) :=
      Subgroup.card_subgroup_dvd_card f.ker
    have hdiv2 : Nat.card f.ker ∣
        Nat.card (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
          (G := ↥H) p) := by
      have hle : (f.ker).map (D.subgroupOf H).subtype ≤
          CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) p := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        have hy1 : f y = 1 := hy
        have hmem : (D.subgroupOf H).subtype y ∈
            (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
              (G := ↥H) p)).ker := by
          rw [MonoidHom.mem_ker]
          show ((f y : ↥(starImg p H D)) : StarGroup p H) = 1
          rw [hy1]
          rfl
        rwa [QuotientGroup.ker_mk'] at hmem
      have hcard : Nat.card (f.ker.map (D.subgroupOf H).subtype) = Nat.card f.ker :=
        Subgroup.card_map_of_injective (D.subgroupOf H).subtype_injective
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle
    have hnot : ¬ d ∣ Nat.card f.ker := fun h => hO (h.trans hdiv2)
    obtain ⟨n, hn⟩ := hDd.exists_card_eq
    have hcardD : Nat.card (D.subgroupOf H) = d ^ n := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv, hn]
    have hdvd : Nat.card f.ker ∣ d ^ n := hcardD ▸ hdiv1
    have hcop : Nat.Coprime (d ^ n) (Nat.card f.ker) :=
      (hdp.coprime_iff_not_dvd.mpr hnot).pow_left n
    exact Nat.eq_one_of_dvd_coprimes hcop hdvd (dvd_refl _)
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, hfker]
  have hcyc : IsCyclic ↥(D.subgroupOf H) := isCyclic_of_injective f hfinj
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

private theorem pRank_inf_le_one_of_isCyclic_starImg (h : TwelveCtx G M p Q H) {d : ℕ}
    (hdp : d.Prime) (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hc : IsCyclic ↥(starImg p H D)) :
    CFSG.Open.pRank d (H ⊓ M) ≤ 1 := by
  have hcycD : IsCyclic ↥D :=
    isCyclic_of_isCyclic_starImg h hdp hXM (hD.le.trans inf_le_left) hD.isPGroup hc
  obtain ⟨S, hS⟩ := hD.exists_sylow_eq_subgroupOf
  have hScyc : IsCyclic (S : Subgroup ↥(H ⊓ M)) := by
    rw [hS]
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hD.le).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hD.le).symm.surjective
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H ⊓ M)]
  exact pRank_le_one_of_isCyclic_sylow hdp S hScyc

private theorem simple_nonsolvable_three_dvd_of_isSimpleOfOrder {n : ℕ} {X : Type} [Group X]
    (h : IsSimpleOfOrder n X) (h3 : 3 ∣ n) :
    IsSimpleGroup X ∧ ¬ Group.IsSolvable X ∧ 3 ∣ Nat.card X := by
  obtain ⟨hs, hns, hc⟩ := isSimpleOfOrder_iff.mp h
  exact ⟨hs, hns, by rwa [hc]⟩

private theorem simple_nonsolvable_three_dvd_of_cases (h : TwelveCtx G M p Q H) {d : ℕ}
    (hdp : d.Prime) (hd2 : d ≠ 2)
    (hc : TwelveThreeCaseSix M p H d ∨ TwelveThreeCaseSpor M p H d) :
    IsSimpleGroup (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) ∧
      ¬ Group.IsSolvable (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) ∧
      3 ∣ Nat.card (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) := by
  rcases hc with h6 | hsp
  · obtain ⟨-, -, ⟨-, hdpvd, hPSL⟩, -⟩ := h6
    have hfact : Fact p.Prime := ⟨h.p_prime⟩
    exact simple_nonsolvable_three_dvd_of_isPSLType_two
      (five_le_of_odd_prime_dvd_add_one h.p_prime h.p_odd hdp hd2 hdpvd) hPSL
  · obtain ⟨-, -, hAlt, -⟩ := hsp
    rcases hAlt with h3 | h4 | h5
    · obtain ⟨-, -, -, hPSL⟩ := h3
      exact simple_nonsolvable_three_dvd_of_isSimpleOfOrder
        (isSimpleOfOrder_of_isPSLType_three_three hPSL) (by norm_num)
    · obtain ⟨-, h4' | h4'⟩ := h4
      · exact simple_nonsolvable_three_dvd_of_isSimpleOfOrder h4'.2.2 (by norm_num)
      · exact simple_nonsolvable_three_dvd_of_isSimpleOfOrder h4'.2.2 (by norm_num)
    · obtain ⟨-, h5' | h5'⟩ := h5
      · exact simple_nonsolvable_three_dvd_of_isSimpleOfOrder
          (isSimpleOfOrder_of_isPSLType_three_seven h5'.2.2) (by norm_num)
      · exact simple_nonsolvable_three_dvd_of_isSimpleOfOrder h5'.2.2 (by norm_num)

private theorem threeNineSocleCase_or_fi22_or_isPSLType {X : Type} [Group X] [Finite X]
    {K X₁ : Subgroup X} {p d : ℕ}
    (h : ThreeNineTuple p d ↥K (oPrimeModPrimeComplement d X₁)) :
    ThreeNineSocleCase K X₁ p d ∨
      (p = 5 ∧ d = 7 ∧ CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Fi22 ∧
        CFSG.Open.StatedClassicalModel (oPrimeModPrimeComplement d X₁) .POmegaPlus 4 2 1) ∨
      (d ∣ p + 1 ∧ IsPSLType 3 (ZMod p) ↥K ∧
        IsPSLType 2 (ZMod p) (oPrimeModPrimeComplement d X₁)) := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr (Or.inr h)

private theorem twelveThreeAltThree_or_altFour_or_altFive_of_threeNineSocleCase
    (hord : TwelveThreeOrderFacts) {d : ℕ}
    (hcase : ThreeNineSocleCase (kStar p M H) (starImg p H M ⊓ kStar p M H) p d)
    (e : oPrimeModPrimeComplement d (starImg p H M ⊓ kStar p M H) ≃*
      modPrimeComplement d (oPPrimeHull d (H ⊓ M))) :
    TwelveThreeAltThree M p H d ∨ TwelveThreeAltFour M p H d ∨
      TwelveThreeAltFive M p H d := by
  rcases hcase with ⟨hp, hd, hK, hW⟩ | ⟨hp, hd, hK, hW⟩ | ⟨hp, hd, hK, hW⟩ |
    ⟨hp, hd, hK, hW⟩ | ⟨hp, hd, hK, hW⟩
  · exact Or.inl ⟨hp, hord.1 _ hK, hd, Nonempty.map (fun f => e.symm.trans f) hW⟩
  · exact Or.inr (Or.inl ⟨hp, Or.inl ⟨hord.2.1 _ hK, hd,
      IsSimpleOfOrder.of_mulEquiv e.symm
        (isSimpleOfOrder_of_statedClassicalModel_psu_three_five hW)⟩⟩)
  · exact Or.inr (Or.inl ⟨hp, Or.inr ⟨hord.2.2.1 _ hK, hd,
      IsSimpleOfOrder.of_mulEquiv e.symm (hord.2.2.2.2.2.1 _ hW)⟩⟩)
  · exact Or.inr (Or.inr ⟨hp, Or.inl ⟨hord.2.2.2.1 _ hK, hd,
      Nonempty.map (fun f => e.symm.trans f) hW⟩⟩)
  · exact Or.inr (Or.inr ⟨hp, Or.inr ⟨hord.2.2.2.2.1 _ hK, hd,
      IsSimpleOfOrder.of_mulEquiv e.symm (hord.2.2.2.2.2.2 _ hW)⟩⟩)

section Holds


private theorem caseSix_or_caseSpor_of_branchA (h39 : ThreeNine) (hI : NineNineOneInput)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (hsoc : KFactThreeNineSocle)
    (hord : TwelveThreeOrderFacts) (hFi : KFactFi22SectionThreeRank) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) (hA : ¬ pLayerIn p H ≤ M)
    (hKn : ((kSub p M H).subgroupOf H).Normal) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    TwelveThreeCaseSix M p H d ∨ TwelveThreeCaseSpor M p H d := by
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hd2 : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have : Fact d.Prime := ⟨hdp⟩
  have hO := not_dvd_card_primeComplementCore_of_twelveCtx h hXM
  obtain ⟨-, hDK, hT⟩ := threeNine_kStar_of_twelveCtx h39 hI hbridge h hns hd hXM hA hD hD1
  have hX₁ : starImg p H M ⊓ (kStar p M H ⊔ starImg p H D) = starImg p H M ⊓ kStar p M H :=
    congrArg (starImg p H M ⊓ ·) (sup_eq_left.mpr hDK)
  obtain ⟨eW⟩ := CFSG.LocalAnalysis.AGL81I.Section3.oPrimeModPrimeComplement_congr d
    (MulEquiv.subgroupCongr hX₁)
  have hT' : ThreeNineTuple p d ↥(kStar p M H)
      (oPrimeModPrimeComplement d (starImg p H M ⊓ kStar p M H)) :=
    ThreeNineTuple.congr (MulEquiv.refl _) eW hT
  obtain ⟨e⟩ := nonempty_oPrimeModPrimeComplement_starImg_mulEquiv hdp hO hD hDK
    (starImg_le_normalizer_kStar p M H)
  have he : oPrimeModPrimeComplement d (starImg p H M ⊓ kStar p M H) ≃*
      modPrimeComplement d (oPPrimeHull d (H ⊓ M)) := eW.symm.trans e
  rcases threeNineSocleCase_or_fi22_or_isPSLType hT' with hsocCase | hFi22 | hPSL
  · exact Or.inr (twelveThreeCaseSpor_of_threeNineSocleCase hI hbridge hsoc h hns hd hXM hA
      hKn hD hD1 hDK hsocCase
      (twelveThreeAltThree_or_altFour_or_altFive_of_threeNineSocleCase hord hsocCase he))
  · obtain ⟨-, -, hK, hW⟩ := hFi22
    exact (false_of_fi22_kStar hFi h inf_le_left hK hW).elim
  · obtain ⟨hdp1, hK, hW⟩ := hPSL
    have hW' : IsPSLType 2 (ZMod p) (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) :=
      Nonempty.map (fun f => he.symm.trans f) hW
    have hDstar : IsPGroup d (starImg p H D) := by
      change IsPGroup d ((D.subgroupOf H).map
        (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) p)))
      exact (hD.isPGroup.comap_subtype (K := H)).map _
    have hDstar_ne : starImg p H D ≠ ⊥ :=
      starImg_ne_bot_of_not_dvd hdp hO (hD.le.trans inf_le_left) hD.isPGroup hD1
    have hdD : d ∣ Nat.card ↥(starImg p H D) :=
      (hDstar.card_eq_or_dvd).resolve_left fun h1 =>
        hDstar_ne (Subgroup.card_eq_one.mp h1)
    exact Or.inl ⟨hA, hKn, ⟨hK, hdp1, hW'⟩,
      isMaxParabolicP_kStar_of_isPSLType_three hI h hdp hd2 hdp1 hKn hD.le hdD hDK hK⟩

theorem twelveThreeData_of_branchA (h10 : NineTenGen) (h39 : ThreeNine)
    (hI : NineNineOneInput) (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hsoc : KFactThreeNineSocle) (hord : TwelveThreeOrderFacts)
    (hFi : KFactFi22SectionThreeRank) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G))
    (hdH : d ∣ Nat.card (H ⊓ M : Subgroup G)) (hA : ¬ pLayerIn p H ≤ M) :
    TwelveThreeData M p H d := by
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hd2 : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have : Fact d.Prime := ⟨hdp⟩
  obtain ⟨hXle, hKn⟩ :=
    xSub_le_M_and_kSub_normal_of_branchA h10 h39 hI hbridge hord h hns hd hXM hdH hA
  obtain ⟨D, hD⟩ := CFSG.ABGLocalTools.exists_isSylowOf d (H ⊓ M)
  have hD1 : D ≠ ⊥ := by
    have hk0 : 0 < (Nat.card (H ⊓ M : Subgroup G)).factorization d :=
      hdp.factorization_pos_of_dvd Nat.card_pos.ne' hdH
    intro hbot
    have hcard : Nat.card D = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hD.card_eq] at hcard
    exact (Nat.one_lt_pow hk0.ne' hdp.one_lt).ne' hcard
  obtain ⟨hcyc, -, -⟩ := threeNine_kStar_of_twelveCtx h39 hI hbridge h hns hd hXM hA hD hD1
  have hc := caseSix_or_caseSpor_of_branchA h39 hI hbridge hsoc hord hFi h hns hd hXM hA hKn hD hD1
  obtain ⟨hs, hnsol, h3⟩ := simple_nonsolvable_three_dvd_of_cases h hdp hd2 hc
  refine ⟨⟨hXle, xSub_subgroupOf_normal_of_kSub_normal hKn, ?_,
    pRank_inf_le_one_of_isCyclic_starImg h hdp hXM hD hcyc, hs, hnsol, h3⟩, Or.inr hc⟩
  rwa [inf_eq_left.mpr hXle] at hXM

end Holds

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
