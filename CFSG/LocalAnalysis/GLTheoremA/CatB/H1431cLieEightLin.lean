module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzEvenCentreD4F4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieInn
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDetOrders
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinU64
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.ChevIndep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.GenPeriodic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OuterTwist
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadCover
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvB
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvM
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic
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
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Local
public import Certificates.Data.U62Rank.Check

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

local notation "fixSub" => CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup

theorem lieSEight_card_quot_center (hLO : LieOrderBridge) {G : Type} [Group G] [Finite G]
    {X J : Subgroup G} (hJ : GLAPComponent 3 X J) (hq : CFSG.Open.IsQuasisimple ↥J)
    (hT : catalogIs (PSimple 3 J) S8.L84.isSp48) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) = 1056706560 := by
  rw [Nat.card_congr (CFSG.LocalAnalysis.GLTheoremA.S171.chevIso' Nat.prime_three hJ hq).toEquiv]
  exact lieSInn_card_sp48 hLO hT

theorem lieSEight_slIndex {E : Type} [Field E] [Fintype E] {m g : ℕ} (hm : 2 ≤ m) (hg : 3 ≤ g)
    (hE : Fintype.card E = 2 ^ g) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A (m - 1) q).Valid),
      q.card = 2 ^ g ∧
        Nonempty (Matrix.SpecialLinearGroup (Fin m) E ⧸
            Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) ≃*
          (TauCeti.CFSGIndex.lie ⟨.A (m - 1) q, hv⟩).Group) := by
  classical
  let q : TauCeti.PrimePower := ⟨2, g, Nat.prime_two, by omega⟩
  have hqc : q.card = 2 ^ g := by simp only [q, TauCeti.PrimePower.card_def]
  have h8 : 8 ≤ 2 ^ g := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have h2 : 2 ∣ 2 ^ g := dvd_pow_self 2 (by omega)
  have hnk : Nat.card E = q.card := by rw [Nat.card_eq_fintype_card, hE, hqc]
  have hrange : (TauCeti.LieTypeIndex.A (m - 1) q).InStandardRange := by
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    exact ⟨by omega, fun _ => by rw [hqc]; omega⟩
  have hdup : ¬ (TauCeti.LieTypeIndex.A (m - 1) q).IsDuplicateRepresentative := by
    rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    rintro (⟨-, hc | hc | hc⟩ | ⟨-, hc⟩ | ⟨-, hc⟩) <;> rw [hqc] at hc <;> omega
  have hv : (TauCeti.LieTypeIndex.A (m - 1) q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    exact ⟨hrange, hdup⟩
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
    (n := m - 1) q hv hnk
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at e
  exact ⟨q, hv, hqc, ⟨(LinearCover.projectiveSpecialLinearEquivProjectiveSL m E).trans e⟩⟩

theorem lieSEight_slQuot_card_ne (hLO : LieOrderBridge) {X : Type} [Group X] [Finite X]
    {E : Type} [Field E] [Fintype E] {m g : ℕ} (hm : 2 ≤ m) (hg : 3 ≤ g)
    (hE : Fintype.card E = 2 ^ g) (f : Matrix.SpecialLinearGroup (Fin m) E →* X)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) :
    Nat.card (X ⧸ Subgroup.center X) ≠ 1056706560 := by
  intro hc
  obtain ⟨q, hv, hqc, ⟨eA⟩⟩ := lieSEight_slIndex (E := E) hm hg hE
  have h8 : 8 ≤ 2 ^ g := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hperf := (slFactorFacts_holds E m hm (fun _ => by omega)).perfect
  obtain ⟨eJ⟩ := nonempty_centralQuotient_mulEquiv hperf f hf hker
  have h1 := hLO ⟨.A (m - 1) q, hv⟩ (X ⧸ Subgroup.center X) ⟨eJ.symm.trans eA⟩
  change Nat.card _ = orderA (m - 1) q.card at h1
  rw [hc, hqc] at h1
  refine CFSG.SeitzReduction.SymplecticPilot.ordA_ne_ordBC (r := m - 1) (g := g) (m := 2)
    (f := 3) (by omega) (by omega) le_rfl (by norm_num) ?_
  rw [show ordBC 2 (2 ^ 3) = 1056706560 by decide +kernel]
  exact h1.symm

theorem lieSEightNoAt_linear (hLO : LieOrderBridge) :
    LieSEightNoAt fun d => ∃ n q, d = .A n q := by
  rintro Y _ _ hY - - ⟨d, hv⟩ ⟨n, q, rfl⟩ hc hf ⟨e⟩ α hα hα3 - ⟨J, hJ, hT⟩
  have hq8 : q.card = 8 := hf
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let k := GaloisField q.p q.exponent
  have hcard : Nat.card k = q.card := by
    dsimp only [k]
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne']
    exact (TauCeti.PrimePower.card_def q).symm
  have hk8 : Nat.card k = 8 := hcard.trans hq8
  have h2 : (2 : k) = 0 := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.two_eq_zero_of_natCard_pow
    (m := 3) (by rw [hk8]; norm_num)
  have eModel : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hv⟩).Group ≃*
      projectiveSL (n + 1) k :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) k)
  let θ : Y ⧸ Subgroup.center Y ≃* projectiveSL (n + 1) k := e.trans eModel
  have hβmem : MulAut.congr θ α ∈ innAutDerived (projectiveSL (n + 1) k) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ).2 hα
  obtain ⟨A, hAβ⟩ := mem_linearAutGroup_iff.1
    (CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived_projectiveSL_le_linearAutGroup
      (m := n + 1) (by omega) hβmem)
  have hAp : conjAut (n + 1) k (A ^ 3) = 1 := by
    rw [map_pow, hAβ, ← map_pow, hα3, map_one]
  obtain ⟨c, hcs⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_eq_scalar_of_conjAut_eq_one
    (by omega) hAp
  have hpk : ((3 : ℕ) : k) ≠ 0 := by
    have h3 : ((3 : ℕ) : k) = 1 := by
      have : ((3 : ℕ) : k) = 2 + 1 := by norm_num
      rw [this, h2, zero_add]
    rw [h3]
    exact one_ne_zero
  have hJ' : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (conjAut (n + 1) k A)) (J.map θ.toMonoidHom) := by
    rw [hAβ]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_transport θ α hJ
  have hpil := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conjAut hpk hcs
  have hJle := hpil _ hJ'.1 (glaPComponent_perfect hJ')
  have hcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJ' hJle).1
  obtain ⟨E, hEf, hEfin, m, j, hm, hj, hchar, hcardE, -, g, hg, hker⟩ :=
    linear_inner_component_type_card hpk hcs _ hcomp
  have hT' : catalogIs (PSimple 3 (J.map θ.toMonoidHom)) S8.L84.isSp48 :=
    (CFSG.LocalAnalysis.GLTheoremA.T123C.catalogIs_pSimple_map_iff (f := θ.toMonoidHom)
      θ.injective 3 J _).2 hT
  have hcardJ := lieSEight_card_quot_center hLO hJ' hcomp.2.2 hT'
  have hEcard : Fintype.card E = 2 ^ (3 * j) := by
    rw [Fintype.card_eq_nat_card, hcardE, hk8, pow_mul]
    norm_num
  exact lieSEight_slQuot_card_ne hLO hm (by omega) hEcard g hg hker hcardJ

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
