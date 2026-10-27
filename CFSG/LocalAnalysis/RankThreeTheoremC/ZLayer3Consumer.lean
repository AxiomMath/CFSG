module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Statement
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListE2
import CFSG.RankThree.PartTwo.Setup
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedCentral
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.RankThreeTheoremC.Signalizers
import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSL
import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaExp3
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaFive3
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.RankThree.PartOne.S10.Defs
import CFSG.StronglyEmbedded
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem sectionFourHyp_of_ne_top (hS : Setting G) (h3 : 3 ∈ rankThreeSigmaA G)
    {H : Subgroup G} (hH : H ≠ ⊤) : CFSG.RankThree.PartTwo.SectionFourHyp H := by
  refine ⟨cfsgIsKGroup_of_catalogSimpleSections
    (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper _ hH), ?_,
    fun q hq hq3 => ?_⟩
  · exact (CFSG.RankThree.PartTwo.evenRank_subgroup_le H).trans (le_of_eq hS.rank)
  · exact (CFSG.RankThree.PartTwo.localRank_subgroup_le hq _).trans_lt
      (rankThreeLocalRank_lt_three_of_three_mem_sigmaA hS.rank h3 hq hq3)

theorem twoLocalOddRank_reduced_le_three (hS : Setting G) (h3 : 3 ∈ rankThreeSigmaA G)
    {H : Subgroup G} (hH : H ≠ ⊤) :
    CFSG.twoLocalOddRank (H ⧸ primeComplementCore (G := H) 3) ≤ 3 := by
  have hC := sectionFourHyp_of_ne_top hS h3 hH
  set O := primeComplementCore (G := H) 3
  let f : (⊤ : Subgroup H) →* H ⧸ O :=
    (QuotientGroup.mk' O).comp (⊤ : Subgroup H).subtype
  have hf : Function.Surjective f := fun y => by
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨c, Subgroup.mem_top c⟩, rfl⟩
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    let g : f.ker →* O :=
      ((⊤ : Subgroup H).subtype.comp f.ker.subtype).codRestrict
        O fun x => (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)
    have hg : Function.Injective g := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    have hdvd : Nat.card f.ker ∣ Nat.card O := Subgroup.card_dvd_of_injective g hg
    intro h3'
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (primeComplementCore_coprime 3)
      (h3'.trans hdvd)
  have hev : CFSG.Assembly.evenRank (H ⧸ O) ≤ 3 :=
    CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 =>
      CFSG.RankThree.PartTwo.Sec4.Item434Spor.localRank_le_three_of_section hC ⊤ f hf hker hr hr2
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact hev

theorem ExtremalObstruction.not_isPConstrained_cases3 (hS : Setting G)
    (hKF1 : KF1At G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (hHtop : H ≠ ⊤) {z : G} (hzH : z ∈ H) (hzD : z ∈ D)
    (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hzp : z ^ p = 1)
    (hzn : (zpowers (⟨z, hzH⟩ : H)).Normal)
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained p H) :
    (5 ≤ p → False) ∧ (ZLayerWeakCoreFact3 →
      IsCyclic (((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype) → H ≤ M) := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hM := hext.obstruction.1
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨A, hAP, hA, hAc⟩ := pRank_attained p (P : Subgroup G) (by rw [hP3]; norm_num)
  rw [hP3] at hAc
  have hKM : (CFSG.pPrimeCore p H).map H.subtype ≤ M := by
    have hcop : ¬ p ∣ Nat.card ((CFSG.pPrimeCore p H).map H.subtype) := by
      rw [card_map_of_injective H.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd hprime).1 CFSG.pPrimeCore_coprime_card
    exact le_of_elemAbelian_normalizes hS hp hM hAP hA hAc hcop
      ((hAP.trans hPH).trans (CFSG.ABGTheoremB.le_normalizer_map_subtype H _))
  have hO : p.Coprime (Nat.card (primeComplementCore (G := H) p)) := primeComplementCore_coprime p
  have hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H := fun o ho =>
    mem_subgroupOf.2 ⟨o.2, hKM ⟨o, ho, rfl⟩⟩
  have hcon' : ¬ HasPrimeConstraint (G := H) p := fun h =>
    hcon (isPConstrained_of_hasPrimeConstraint h)
  obtain ⟨K, hKc, -, -, hKp, -, -⟩ :=
    CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component hS.kProper H hHtop p
      hprime hcon'
  set O : Subgroup H := primeComplementCore (G := H) p with hOdef
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπ
  have hEbn : (rankThreeLayer (⊤ : Subgroup (H ⧸ O))).Normal :=
    CFSG.ComponentClassification.Layer.normal _
  have hdvd : p ∣ Nat.card (rankThreeLayer (⊤ : Subgroup (H ⧸ O))) :=
    hKp.trans (Subgroup.card_dvd_of_le (le_sSup hKc))
  have hinf := inf_comap_ne_bot_of_dvd_card O (P.subtype hPH) hdvd
  set E : Subgroup G := ((rankThreeLayer (⊤ : Subgroup (H ⧸ O))).comap π).map H.subtype with hE
  have hEH : E ≤ H := map_subtype_le _
  have hHE : H ≤ normalizer (E : Set G) := CFSG.ABGTheoremB.le_normalizer_map_subtype H _
  have hSE : (P : Subgroup G) ⊓ E ≠ ⊥ := by
    intro hbot
    apply hinf
    rw [eq_bot_iff]
    rintro t ⟨htP, htE⟩
    have htP' : (t : G) ∈ (P : Subgroup G) := by
      rw [Sylow.coe_subtype] at htP
      exact htP
    have : (t : G) ∈ (P : Subgroup G) ⊓ E := ⟨htP', t, htE, rfl⟩
    rw [hbot, mem_bot] at this
    exact mem_bot.2 (Subtype.ext this)
  have hzE : z ∈ E := hext.mem_of_inf_ne_bot hprime hodd hPD (hPH.trans hHE) hSE hzD hz1 hzc hzp
  set zH : H := ⟨z, hzH⟩ with hzHdef
  have hzbE : π zH ∈ rankThreeLayer (⊤ : Subgroup (H ⧸ O)) := by
    obtain ⟨h, hh, hhz⟩ := hzE
    have : h = zH := Subtype.ext hhz
    rw [this] at hh
    exact hh
  have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hzHord : orderOf zH = p := by rw [← Subgroup.orderOf_coe]; exact hzord
  have hzbord : orderOf (π zH) = p :=
    CFSG.AGLEmbedding.orderOf_mk_of_coprime hprime O hO hzHord
  have hzb1 : π zH ≠ 1 := fun h => by
    rw [h, orderOf_one] at hzbord
    exact hprime.one_lt.ne hzbord
  have hzbp : (π zH) ^ p = 1 := by
    have := pow_orderOf_eq_one (π zH)
    rwa [hzbord] at this
  have hzbn : (zpowers (π zH)).Normal := by
    rw [← MonoidHom.map_zpowers]
    exact hzn.map π (QuotientGroup.mk'_surjective O)
  set Pbar : Sylow p (H ⧸ O) :=
    (P.subtype hPH).mapSurjective (QuotientGroup.mk'_surjective O) with hPbardef
  have hPbar : (Pbar : Subgroup (H ⧸ O)) = ((P : Subgroup G).subgroupOf H).map π := by
    rw [hPbardef, Sylow.coe_mapSurjective, Sylow.coe_subtype]
  have hrankPbar : CFSG.Open.pRank p (Pbar : Subgroup (H ⧸ O)) = 3 := by
    rw [hPbar, CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hprime O hO,
      map_subgroupOf_eq_of_le hPH]
    exact hP3
  have hzbc : π zH ∈ centralizer ((Pbar : Subgroup (H ⧸ O)) : Set (H ⧸ O)) := by
    rw [hPbar, mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have : t * zH = zH * t := Subtype.ext (mem_centralizer_iff.1 hzc (t : G) ht)
    show π t * π zH = π zH * π t
    rw [← map_mul, ← map_mul, this]
  have hcat : CFSG.AGLEmbedding.CatalogSimpleSections (H ⧸ O) :=
    (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient O
  have hcore : primeComplementCore (G := H ⧸ O) p = ⊥ := primeComplementCore_quotient_eq_bot p
  have hrankTop : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) = 3 :=
    (CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p hprime Pbar).symm.trans
      hrankPbar
  have h5 : 5 ≤ p → False := fun hp5 =>
    hzb1 (hKF1.eq_one_of_mem_layer hprime hp5 hHtop hcat hcore hrankTop.le hzbE hzbn)
  refine ⟨h5, fun hKF3 hRc => ?_⟩
  by_cases hp3 : p = 3
  · subst hp3
    have hcyc : IsCyclic (CFSG.pCore 3 (H ⧸ O)) := isCyclic_pCore_quotient (P.subtype hPH) hRc
    obtain ⟨hD, hDn⟩ := hext.exists_plane_map hprime hodd hPD hPH O hO
    rw [← hPbar] at hD hDn
    have hKF := hKF3 (H ⧸ O) hcat (twoLocalOddRank_reduced_le_three hS hp hHtop) hcore Pbar
      (π zH) hrankPbar hzbord hzbn hzbc hzbE hcyc
      ⟨_, hD, mem_map_of_mem π (show zH ∈ D.subgroupOf H from hzD), hDn⟩
    have hW := CFSG.AGLEmbedding.weakCore_map_le_map_inf_of_coprime hprime P hM.2 le_rfl hPH O
      hO hOM
    rw [← hPbar] at hW
    have hEbX : rankThreeLayer (⊤ : Subgroup (H ⧸ O)) ≤ ((H ⊓ M).subgroupOf H).map π :=
      hKF.trans hW
    have hEM : E ≤ M := by
      rintro _ ⟨h, hh, rfl⟩
      have h1 : h ∈ (((H ⊓ M).subgroupOf H).map π).comap π := hEbX hh
      rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk', sup_eq_left.2 hOM] at h1
      exact (mem_subgroupOf.1 h1).2
    have hrankY : 2 ≤ CFSG.Open.pRank 3 ((P : Subgroup G) ⊓ E) := by
      have h1 := two_le_pRank_inf_layer hodd Pbar hzbE hzbn hzb1 hzbp
      have h2 : (Pbar : Subgroup (H ⧸ O)) ⊓ rankThreeLayer (⊤ : Subgroup (H ⧸ O)) =
          (((P : Subgroup G).subgroupOf H) ⊓
            (rankThreeLayer (⊤ : Subgroup (H ⧸ O))).comap π).map π := by
        rw [hPbar]
        ext x
        constructor
        · rintro ⟨⟨t, htP, rfl⟩, hxL⟩
          exact ⟨t, ⟨htP, hxL⟩, rfl⟩
        · rintro ⟨t, ⟨htP, htL⟩, rfl⟩
          exact ⟨⟨t, htP, rfl⟩, htL⟩
      rw [h2, CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hprime O hO,
        Subgroup.map_inf _ _ H.subtype H.subtype_injective, map_subgroupOf_eq_of_le hPH] at h1
      exact h1
    exact hext.le_of_normal_of_two_le_pRank hprime hPD hPH hEH hHE hEM hrankY
  · have hp5 : 5 ≤ p := by
      have h2 := hprime.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hprime (by decide)
      omega
    exact (h5 hp5).elim

theorem transitivityComponentCase_of_kfacts3 (hS : Setting G) (hKF1 : KF1At G)
    (hKF3 : ZLayerWeakCoreFact3) : TransitivityComponentCase G := by
  intro p hp P M D hext hPD z hzD hz1 hzc hzp hPN hRc hcon
  have hzH : z ∈ normalizer ((zpowers z : Subgroup G) : Set G) := le_normalizer (mem_zpowers z)
  exact ((hext.not_isPConstrained_cases3 hS hKF1 hp hPD hPN (hS.normalizer_zpowers_ne_top hz1)
    hzH hzD hz1 hzc hzp (normal_zpowers_subtype_mk z hzH) hcon).2) hKF3 hRc

end CFSG.LocalAnalysis.RankThreeTheoremC
