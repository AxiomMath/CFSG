module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClWit
public import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerShape
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFam
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaPlus
import CFSG.RankThree.PartTwo.Census.Spin.WitnessTDFive
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Omega
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6OmegaInner
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Split
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerOmega
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthAll
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLForm
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralReps
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.DiagonalLink
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainBasic
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerDefs
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FiStep
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma39
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob
import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Residual
import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open Module QuadraticMap CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.HardMathSupport.Dickson.Bal207 (OrthCompIdx)
open CFSG.HardMathSupport.Dickson.Bal207.OrthFix (OrthIdxRankLt orthInnerShape)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalAut
open CFSG.GroupTheory.WeirSylow (IsPlusType)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (autCenterQuot)
open CFSG.ComponentClassification.CatFC (omegaPlus_isPlusType)

local notation "fixSub" => CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup

theorem lieSEight_orthComp_rankFour_ne {d : TauCeti.LieTypeIndex}
    (hd : OrthCompIdx d) (hr : OrthIdxRankLt 4 d) : lieOrderFormula d ≠ 1056706560 := by
  intro h
  cases d with
  | D s q =>
    have h1 : 4 ≤ s := hd.2.2
    have h2 : s < 4 := hr
    omega
  | twistedD s q =>
    have h1 : 5 ≤ s := hd.2.2
    have h2 : s < 4 := hr
    omega
  | twistedA r q =>
    change orderTwistedA r q.card = 1056706560 at h
    have h4 : r < 4 := hr
    rcases hd with ⟨hq, hr2, hne⟩ | ⟨rfl, hp3, he⟩
    · rcases hq with hq1 | hq3
      · have hc : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hq1.1, hq1.2]; rfl
        rcases (show r = 2 ∨ r = 3 by omega) with rfl | rfl
        · exact hne ⟨rfl, hq1⟩
        · rw [hc] at h
          exact absurd h (by decide +kernel)
      · have hc : q.card = 8 := by
          rw [TauCeti.PrimePower.card_def, hq3.1, hq3.2]
          norm_num
        rcases (show r = 2 ∨ r = 3 by omega) with rfl | rfl <;> rw [hc] at h <;>
          exact absurd h (by decide +kernel)
    · have hqcard : q.card = 3 := by
        rw [TauCeti.PrimePower.card_def, hp3, he]
        norm_num
      rw [hqcard] at h
      exact absurd h (by decide +kernel)
  | A r q =>
    obtain ⟨rfl, hq⟩ := hd
    have hqcard : q.card = 8 := by
      rw [TauCeti.PrimePower.card_def, hq.1, hq.2]
      norm_num
    change orderA 1 q.card = 1056706560 at h
    rw [hqcard] at h
    exact absurd h (by decide +kernel)
  | _ => exact hd.elim

open CFSG.RankThree.PartTwo.Census.Spin in
theorem lieSEight_hasWitness_tdfive (d : TauCeti.TypeTwistedDLieIndex)
    (h2 : d.1.characteristic = 2) (h3 : d.1.fieldExponent = 3) (h5 : d.1.rank = 5) :
    HasWitness d.Group 3 4 := by
  have hchar : (2 : d.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → d.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero d.1.Closure d.1.characteristic)
    exact_mod_cast h
  obtain ⟨c, hc⟩ := CarrierD.exists_unit_order_seven d.1 h2
  have hq : d.1.fieldOrder = 8 := by
    rw [TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, h2, h3]
    norm_num
  have hcard : Nat.card (CarrierTD.fixedField2 d) = 64 := by
    rw [CarrierTD.card_fixedField2, h2, h3]
    norm_num
  haveI : Finite (CarrierTD.fixedField2 d) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨μ, hμL, hμo⟩ := exists_unit_orderOf (CarrierTD.fixedField2 d) (s := 3)
    (by rw [hcard]; norm_num)
  have hμσ : CarrierTD.frob d (CarrierTD.frob d μ) = μ := hμL
  have hσ : ∀ u : d.1.Closure, CarrierTD.frob d u = u ^ 8 := fun u => by
    rw [CarrierTD.frob_apply, hq]
  have hμ3 : μ ^ 3 = 1 := hμo ▸ pow_orderOf_eq_one μ
  have hμ3' : (μ : d.1.Closure) ^ 3 = 1 := by
    have := congrArg (fun u : d.1.Closureˣ => (u : d.1.Closure)) hμ3
    simpa using this
  have hμ2 : (μ : d.1.Closure) ^ 2 ≠ 1 := by
    intro h
    have h' : μ ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hμo] at this
    omega
  have hμN : μ * Units.map (CarrierTD.frob d : d.1.Closure →* d.1.Closure) μ = 1 :=
    Units.ext (by
      simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, Units.val_one]
      rw [hσ]
      linear_combination ((μ : d.1.Closure) ^ 6 + (μ : d.1.Closure) ^ 3 + 1) * hμ3')
  exact CarrierTD.hasWitness_tdfive_gen (CarrierTD.isTwistedFrobenius d)
    (fun i hi => CarrierTD.perm_of_lt d hi) (CarrierTD.perm_forkA d) (CarrierTD.perm_forkB d)
    hc hμσ hμ2 hμ3 hμN hchar h5

theorem lieSEight_local81_twistedD_five (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD 5 q).Valid) (hp : q.p = 2) (hf : q.exponent = 3) :
    I1431C2.Local81 (TauCeti.CFSGIndex.lie ⟨.twistedD 5 q, hv⟩).Group := by
  obtain ⟨hchar, -, hexp, hrank⟩ := CFSG.RankThree.PartTwo.Census.Spin.typeTwistedD_mk_data 5 q hv
  exact I1431C2.Local81.of_hasWitness
    (lieSEight_hasWitness_tdfive _ (hchar.trans hp) (hexp.trans hf) hrank)

theorem lieSEight_local81_twistedD_six (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hp : q.p = 2) (h6 : 6 ≤ r) :
    I1431C2.Local81 (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group := by
  obtain ⟨hchar, -, -, hrank⟩ := CFSG.RankThree.PartTwo.Census.Spin.typeTwistedD_mk_data r q hv
  exact I1431C2.Local81.of_hasWitness
    (CFSG.RankThree.PartTwo.Census.Spin.CarrierTD.hasWitness_twShort _ (hchar.trans hp)
      (by rw [hrank]; exact h6))

theorem lieSEight_d4_coords {S : Type} [Group S]
    (hM : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .POmegaPlus 4 2 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (Q : QuadraticForm F (Fin (2 * 4) → F)) (_ : S ≃* ProjOrthDerived Q),
      Nat.card F = 2 ^ 3 ∧ (polarBilin Q).Nondegenerate ∧
      (∃ U : Submodule F (Fin (2 * 4) → F), finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
      (IsPlusType Q ↔ Even 4) := by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hM.2
  haveI : CharP F 2 := by
    haveI := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 3) (by rw [Fintype.card_eq_nat_card, hF])
  have hreg := regular_coordinateQuadPlus 4 F (by norm_num)
  exact ⟨F, inferInstance, inferInstance, inferInstance, coordinateQuadPlus 4 F,
    (coordinatePlusWitnessEquiv F e₀).trans (coordBridge (coordinateQuadPlus 4 F) (by norm_num)),
    hF, hreg.1, hreg.2, iff_of_true (omegaPlus_isPlusType 4 F) (by decide)⟩

theorem lieSEight_d4_inner_noSp (hLO : LieOrderBridge) {S : Type} [Group S] [Finite S]
    (hM : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .POmegaPlus 4 2 3) {s : S}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ¬ CompOfType S (MulAut.conj s) S8.L84.isSp48 := by
  rintro ⟨J, hJ, hT⟩
  obtain ⟨F, hFf, hFfin, hFchar, Q, eQ, hF, hQ, hT3, hV⟩ := lieSEight_d4_coords hM
  have ht3 : orderOf (eQ s) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hs3, map_one])
      (fun h => hs1 (eQ.injective (h.trans (map_one eQ).symm)))
  obtain ⟨hlayer, htypes, -, -⟩ := orthInnerShape (Or.inr (by rw [hF]; norm_num))
    (by norm_num : 0 < 2 * 4) hQ hT3 rfl (le_refl 4) hV ht3
  haveI : Finite (ProjOrthDerived Q) := Finite.of_equiv S eQ.toEquiv
  have hJ' : GLAPComponent 3 (fixSub (MulAut.conj (eQ s))) (J.map eQ.toMonoidHom) := by
    rw [← CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj eQ s]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_transport eQ (MulAut.conj s) hJ
  have hle := hlayer _ hJ'.1 (glaPComponent_perfect hJ')
  have hcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJ' hle).1
  obtain ⟨i, hi, hrk, ⟨eZ⟩⟩ := htypes _ hcomp
  have hT' : catalogIs (PSimple 3 (J.map eQ.toMonoidHom)) S8.L84.isSp48 :=
    (CFSG.LocalAnalysis.GLTheoremA.T123C.catalogIs_pSimple_map_iff (f := eQ.toMonoidHom)
      eQ.injective 3 J _).2 hT
  have hc := lieSEight_card_quot_center hLO hJ' hcomp.2.2 hT'
  have h2 := hLO i _ ⟨eZ⟩
  exact lieSEight_orthComp_rankFour_ne hi hrk (h2.symm.trans hc)

@[expose] def LieSEightD4Tri : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    CFSG.Assembly.LowTwoRank.StatedClassicalModel S .POmegaPlus 4 2 3 →
      ∀ β : MulAut S, β ∈ innAutDerived S → β ^ 3 = 1 → (∀ s : S, MulAut.conj s ≠ β) →
        ¬ CompOfType S β S8.L84.isSp48

theorem lieSEightAt_D (hGA : CFSG.Open.GriessAllModelsStatement) (hLO : LieOrderBridge)
    (hTri : LieSEightD4Tri) : LieSEightAt fun d => ∃ n q, d = .D n q := by
  rintro Y _ _ hY - hRk ⟨d, hv⟩ ⟨n, q, rfl⟩ hc hf ⟨e⟩ ξ hξ3 hξ1 hin J hJ hT -
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hq8 : q.card = 8 := hf
  have hp2 : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_D n q).symm.trans hc
  have hexp : q.exponent = 3 := by
    have h := q.card_def
    rw [hq8, hp2] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num : 8 = 2 ^ 3))
  show False
  rcases (show n = 4 ∨ 5 ≤ n by simp only [] at hr; omega) with rfl | h5
  · have hM := CFSG.Models.lieModel_D 4 q hv e
    have hM' := hM.2.resolve_right (fun h0 => absurd h0.1 (by norm_num))
    rw [hp2, hexp] at hM'
    haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
    have hZ : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := I1431C2.cl_center_eq_bot_of_simple
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY)
    have hβ3 : inducedAut ξ ^ 3 = 1 := by
      rw [show inducedAut ξ = autCenterQuot Y ξ from rfl, ← map_pow, hξ3, map_one]
    have hβ1 : inducedAut ξ ≠ 1 := fun h' => hξ1 (eq_one_of_inducedAut_eq_one hY.1 h')
    have hcomp := lieSEight_image_component hY hJ hT
    by_cases hinn : ∃ s : Y ⧸ Subgroup.center Y, MulAut.conj s = inducedAut ξ
    · obtain ⟨s, hs⟩ := hinn
      rw [← hs] at hcomp hβ3 hβ1
      have hs3 : s ^ 3 = 1 := by
        apply CFSG.mulAutConj_injective_of_center_eq_bot hZ
        rw [map_pow, hβ3, map_one]
      have hs1 : s ≠ 1 := fun h => hβ1 (by rw [h, map_one])
      exact lieSEight_d4_inner_noSp hLO hM' hs3 hs1 hcomp
    · exact hTri _ hM' _ hin hβ3 (fun s hs => hinn ⟨s, hs⟩) hcomp
  · exact (I1431C2.false_of_local81_group hGA hY hRk (d := ⟨.D n q, hv⟩) (fun h => h) e
      (I1431C2.local81_D n q hv hp2 h5)).elim

theorem lieSEightAt_twistedD (hGA : CFSG.Open.GriessAllModelsStatement)
    (h4 : LieSEightNoAt fun d => ∃ q, d = .twistedD 4 q) :
    LieSEightAt fun d => ∃ n q, d = .twistedD n q := by
  rintro Y _ _ hY hcore hRk ⟨d, hv⟩ ⟨n, q, rfl⟩ hc hf he ξ hξ3 hξ1 hin J hJ hT hτ
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hq8 : q.card = 8 := hf
  have hp2 : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_twistedD n q).symm.trans hc
  have hexp : q.exponent = 3 := by
    have h := q.card_def
    rw [hq8, hp2] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num : 8 = 2 ^ 3))
  rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by simp only [] at hr; omega) with rfl | rfl | h6
  · exact lieSEightAt_of_noAt h4 Y hY hcore hRk ⟨_, hv⟩ ⟨q, rfl⟩ hc hf he ξ hξ3 hξ1 hin J hJ hT hτ
  · obtain ⟨e⟩ := he
    exact (I1431C2.false_of_local81_group hGA hY hRk (d := ⟨.twistedD 5 q, hv⟩) (fun h => h) e
      (lieSEight_local81_twistedD_five q hv hp2 hexp)).elim
  · obtain ⟨e⟩ := he
    exact (I1431C2.false_of_local81_group hGA hY hRk (d := ⟨.twistedD n q, hv⟩) (fun h => h) e
      (lieSEight_local81_twistedD_six n q hv hp2 h6)).elim

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
