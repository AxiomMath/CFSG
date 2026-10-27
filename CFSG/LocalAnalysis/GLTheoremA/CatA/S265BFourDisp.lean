module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BFour
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoInn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM2Marking
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2A
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141c
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E7
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E8
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.L2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.LayerTransport
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutLin
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import Certificates.Certificate41501

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.StandardType (markChar markDeg)

theorem qsFamB_of_high (hH : QSFamBHigh) : QSFamB := by
  intro p Ω _ _ S B T x D K hN hp hK
  obtain ⟨i, hi, e⟩ := hK
  rcases tyUn_four_or_high hi with h4 | hh
  · subst hp
    exact Or.inr ⟨rfl, Or.inl ⟨i, h4, e⟩⟩
  · exact hH p Ω S B T x D K hN hp ⟨i, hh, e⟩

private theorem quFour_n_one {lab : CFSG.Assembly.LargeEvenLabel} (hc : markChar lab = 2)
    (hd : markDeg lab = 1) : lab.n = 1 := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [markChar, markDeg] at hc hd ⊢ <;> (try split_ifs at hd) <;> omega

private theorem quFour_not_td4 {R : Type} [Group R] [Finite R] (hs : IsSimpleGroup R)
    (hnab : ∃ a c : R, a * c ≠ c * a) {α : MulAut R} (hP : I1431C2.U42Pumpup R α)
    (hO : I1431C2.U42Outer) (hI : I1431C2.U42InnField) {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid} (hq2 : q.p = 2)
    (e : R ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩)
    (hcard : Nat.card R = ordTrialityD4 (2 ^ q.exponent)) : False := by
  have hc : (⟨.trialityD4 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic = 2 :=
    (TauCeti.LieTypeIndex.characteristic_trialityD4 q).trans hq2
  by_cases hin : α ∈ innAutDerived R
  · have hf : q.card = 2 := hI R hs hnab ⟨.trialityD4 q, hv⟩ hc ⟨e⟩ α hin hP
    obtain ⟨-, he⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1
      (by simpa only [TauCeti.PrimePower.card_def] using hf)
    have h25 := hP.card_dvd
    rw [hcard, he] at h25
    exact absurd h25 (by decide +kernel)
  · exact hO R hs hnab ⟨.trialityD4 q, hv⟩ hc ⟨e⟩ α hin hP

section Four


theorem quFamB_four {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (h : QUNL 3 S B T x b) (hJT : catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU4two) :
    QUConcl 3 S B x b := by
  obtain ⟨hbN, hP⟩ := quFour_pumpup h hJT
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three h.cfg.comp
  have hs : IsSimpleGroup (PSimple 3 S) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  rcases h.cfg.prop with hF | ⟨-, hTD, -⟩
  · rcases h.cfg.chev with ⟨i, hi, ⟨eS⟩⟩ | ⟨i, hi, ⟨eS⟩⟩
    · cases i with
      | lie d =>
        have hchar : d.1.characteristic = 2 := hi
        by_cases hin : chevAut 3 S ⟨b, hbN⟩ ∈ innAutDerived (PSimple 3 S)
        · have hf := I1431C2.u42InnField_holds _ hs hnab d hchar ⟨eS⟩ _ hin hP
          obtain ⟨t, n, f, hLM, hf2⟩ := CanonSubcomp.exists_lieModel_two_fieldSize d hchar eS
          obtain ⟨-, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 (hf2.symm.trans hf)
          exact (I2015.not_fieldOn_of_marking_n_one Nat.prime_three (by norm_num) hF
            (CFSG.StandardType.Canonical.largeEvenMarking_mono
              (fun _ _ _ _ _ _ hl => quFour_n_one hl.2.2.1 hl.2.2.2)
              (CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1
                hLM))).elim
        · exact Or.inr ⟨rfl, ⟨_, I1431C2.u42Outer_holds _ hs hnab d hchar ⟨eS⟩ _ hin hP, ⟨eS⟩⟩,
            hF⟩
      | _ => exact hi.elim
    · have h1 := Nat.le_of_dvd Nat.card_pos hP.card_dvd
      have h2 := MovingAround.Inputs141c.card_le_of_ambiguousChev_two hi eS
      omega
  · obtain ⟨d, hv, hd, ⟨eT⟩⟩ := CatB.exists_lieIndex hTD
    cases d with
    | trialityD4 q =>
      have hq2 := td4g2_p_two hv eT h.cfg.chev
      exact (quFour_not_td4 hs hnab hP I1431C2.u42Outer_holds I1431C2.u42InnField_holds hq2 eT
        ((Nat.card_congr eT.toEquiv).trans (CFSG.AGLEmbedding.card_catGroup_trialityD4_even
          (d := ⟨.trialityD4 q, hv⟩) hq2 rfl))).elim
    | _ => exact hd.elim

theorem quFamB_of_high (hH : QUFamBHigh) : QUFamB := by
  intro p Ω _ _ S B T x b hN hp hJ
  obtain ⟨i, hi, e⟩ := hJ
  rcases tyUn_four_or_high hi with h4 | hh
  · subst hp
    exact quFamB_four hN ⟨i, h4, e⟩
  · exact hH p Ω S B T x b hN hp ⟨i, hh, e⟩

end Four

end CFSG.LocalAnalysis.GLTheoremA.S265

end
