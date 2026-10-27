module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRankMain
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inputs
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Cat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.GH74.GLS.IVK.Proofs2.NoOuter
public import CFSG.GH74.GLS.IVK.Proofs2.TwoTori
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvEngLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvU4Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryScalarQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Orbit
public import CFSG.Milestones.ASVolI.F431.Final4
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Comp2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LieData
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Trans
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.CTP.SeitzSpOuter
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.K159.AutCore
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.S11d.OddOutPSL2
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.RankThree.PartOne.S11d.PSLDescent
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.Sporadic.Schreier.J4SCommGenBase1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem kFactCenterRankTwo_holds
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    KFactCenterRankTwo := by
  intro X _ _ hK L hL p hp hp2 h2
  have hq : CFSG.Open.IsQuasisimple ↥L := ⟨hL.1.1.commutator_eq_top, hL.1.2.1⟩
  have hcat : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.isCatalogGroup_quotient_center_of_component hK hL
  obtain ⟨E, hE, hEa, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center ↥L)
  have hpZ : p ∣ Nat.card (Subgroup.center ↥L) := by
    have hp2dvd : p ^ 2 ∣ Nat.card E := by
      rw [hEcard]
      exact Nat.pow_dvd_pow p h2
    exact (dvd_pow_self p (by norm_num)).trans (hp2dvd.trans (Subgroup.card_dvd_of_le hE))
  by_cases hp3 : p = 3
  · subst hp3
    by_contra hcon
    have hle3 : CFSG.Open.pRank 3 L ≤ 3 := by omega
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hNcop : Nat.Coprime 3 (Nat.card (GL83.I243.Cover.primeCentre 3 ↥L)) :=
      GL83.I243.Cover.coprime_card_primeCentre
    have hN3 : ¬ 3 ∣ Nat.card (GL83.I243.Cover.primeCentre 3 ↥L) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hNcop
    have hdisj : Disjoint E (GL83.I243.Cover.primeCentre 3 ↥L) := by
      refine Subgroup.disjoint_of_coprime_natCard ?_
      rw [hEcard]
      exact Nat.Coprime.pow_left _ hNcop
    let f : ↥L →* (↥L ⧸ GL83.I243.Cover.primeCentre 3 ↥L) :=
      QuotientGroup.mk' (GL83.I243.Cover.primeCentre 3 ↥L)
    have hφinj : Function.Injective
        (fun x : E => (⟨f (x : ↥L), Subgroup.mem_map_of_mem f x.2⟩ : ↥(E.map f))) := by
      intro x y hxy
      have h1 : f (x : ↥L) = f (y : ↥L) := congrArg Subtype.val hxy
      have h2 : f ((x : ↥L)⁻¹ * (y : ↥L)) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h3 : (x : ↥L)⁻¹ * (y : ↥L) ∈ GL83.I243.Cover.primeCentre 3 ↥L := by
        rw [← QuotientGroup.ker_mk' (GL83.I243.Cover.primeCentre 3 ↥L)]
        exact MonoidHom.mem_ker.2 h2
      have h4 : (x : ↥L)⁻¹ * (y : ↥L) ∈ E := E.mul_mem (E.inv_mem x.2) y.2
      have h5 : (x : ↥L)⁻¹ * (y : ↥L) = 1 := by
        have hbot : (x : ↥L)⁻¹ * (y : ↥L) ∈ (⊥ : Subgroup ↥L) := by
          rw [← hdisj.eq_bot]
          exact ⟨h4, h3⟩
        exact Subgroup.mem_bot.1 hbot
      apply Subtype.ext
      calc (x : ↥L) = (x : ↥L) * ((x : ↥L)⁻¹ * (y : ↥L)) := by rw [h5, mul_one]
        _ = (y : ↥L) := by group
    have h9 : 9 ≤ Nat.card E := by
      rw [hEcard]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ CFSG.Open.pRank 3 (Subgroup.center ↥L) :=
            Nat.pow_le_pow_right (by norm_num) h2
    have hmaple : E.map f ≤
        Subgroup.center (↥L ⧸ GL83.I243.Cover.primeCentre 3 ↥L) := by
      rw [GL83.I243.Cover.center_quotient_eq_map (p := 3) hq]
      exact Subgroup.map_mono hE
    have hcard9 : 9 ≤ Nat.card
        ↥(Subgroup.center (↥L ⧸ GL83.I243.Cover.primeCentre 3 ↥L)) :=
      h9.trans ((Nat.card_le_card_of_injective _ hφinj).trans (Subgroup.card_le_of_le hmaple))
    have hZne : Subgroup.center (↥L ⧸ GL83.I243.Cover.primeCentre 3 ↥L) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hcard9
      omega
    have hKcat : CFSG.Open.IsCatalogGroup
        ((↥L ⧸ GL83.I243.Cover.primeCentre 3 ↥L) ⧸
          Subgroup.center (↥L ⧸ GL83.I243.Cover.primeCentre 3 ↥L)) := by
      obtain ⟨e⟩ := GL83.I243.Cover.nonempty_equiv_center_quotient (p := 3) hq
      exact CFSG.AGLEmbedding.IsCatalogGroup.of_mulEquiv e hcat
    have hKq : CFSG.Open.IsQuasisimple (↥L ⧸ GL83.I243.Cover.primeCentre 3 ↥L) :=
      GL83.I243.Cover.isQuasisimple_quotient (p := 3) hq
    have hZp : IsPGroup 3
        ↥(Subgroup.center (↥L ⧸ GL83.I243.Cover.primeCentre 3 ↥L)) :=
      GL83.I243.Cover.isPGroup_center_quotient (p := 3) hq
    have hrk : CFSG.Open.pRank 3
        (⊤ : Subgroup (↥L ⧸ GL83.I243.Cover.primeCentre 3 ↥L)) ≤ 3 := by
      rw [CFSG.SectionRank.pRank_quotient_eq (p := 3)
          (GL83.I243.Cover.primeCentre 3 ↥L) hN3,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
      exact hle3
    obtain ⟨-, hcardZ⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.bal3ThreeCenter_of_tables
        hGA hAlt hSpor (↥L ⧸ GL83.I243.Cover.primeCentre 3 ↥L) hKq hKcat hZne hZp hrk
    have h93 : 9 ≤ 3 := hcardZ ▸ hcard9
    omega
  · have hp5 : 5 ≤ p := by
      have hp2le : 2 ≤ p := hp.two_le
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      omega
    have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRank.schurMultiplierRankFact_of_tables hGA hAlt hSpor p hp hp5 ↥L hq hcat hpZ
    rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
