module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzPinCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RankE8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzFacts
public import Certificates.Certificate26990
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockOddPairOrbitInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockProperSupportOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CommutingFamilyCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Step
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSONFacts
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.ThSchreier.AutCore
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open scoped commutatorElement

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.EvenSporadicStandard.Solomon78


theorem rep_suzCommArr {u v : Array Nat} {g h : Equiv.Perm (Fin 1782)} (hu : Rep 1782 u g)
    (hv : Rep 1782 v h) (hiu : isInvA 1782 u (invCand 1782 u) = true)
    (hiv : isInvA 1782 v (invCand 1782 v) = true) :
    Rep 1782 (suzCommArr u v) (g * h * g⁻¹ * h⁻¹) :=
  rep_compA (rep_compA (rep_compA hu hv) (rep_inv_of_isInvA hu hiu))
    (rep_inv_of_isInvA hv hiv)

theorem ne_of_eqA_false {n : ℕ} {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hu : Rep n u h) (he : eqA n t u = false) : g ≠ h := fun hgh => by
  rw [(eqA_iff ht hu).2 hgh] at he
  exact Bool.noConfusion he

theorem suz_pinned_data : ∃ K : Subgroup (Equiv.Perm (Fin 1782)), K ≤ suzM ∧
    (∀ k ∈ K, k * suzInv 0 = suzInv 0 * k) ∧ ⁅K, K⁆ = K ∧ Nat.card K = 20160 ∧
      3 ≤ CFSG.pRank 2 K := by
  have h := Certificates.certificate26680
  simp only [suzRowCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hlet, hinv⟩, hrel⟩, hfix⟩, hgen⟩, hcls⟩, hzc⟩ := h
  simp only [suzLettersOK, Bool.and_eq_true] at hlet
  obtain ⟨⟨⟨⟨⟨hlA, hlB⟩, hlL⟩, hlZ⟩, hlG0⟩, hlG1⟩ := hlet
  simp only [suzInvOK, Bool.and_eq_true] at hinv
  obtain ⟨⟨⟨⟨hiA, hiB⟩, hiL⟩, hiAl⟩, hiBl⟩ := hinv
  simp only [suzRelOK, Bool.and_eq_true] at hrel
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpA, hpB⟩, ht0⟩, hcA⟩, hcB⟩, hlz⟩, hg0⟩, hg1⟩, hzz⟩ := hrel
  set A : Equiv.Perm (Fin 1782) := suzWord suzWordA with hAdef
  set B : Equiv.Perm (Fin 1782) := suzWord suzWordB with hBdef
  have hRA : Rep 1782 suzArrA A := by
    unfold suzArrA
    exact rep_suzArr (lettersOK_mono (by norm_num) hlA)
  have hRB : Rep 1782 suzArrB B := by
    unfold suzArrB
    exact rep_suzArr (lettersOK_mono (by norm_num) hlB)
  have hRAi : Rep 1782 suzArrAi A⁻¹ := rep_inv_of_isInvA hRA hiA
  have hRBi : Rep 1782 suzArrBi B⁻¹ := rep_inv_of_isInvA hRB hiB
  have hR0 : Rep 1782 (tArr 0) (suzInv 0) := rep_suzInv (by norm_num)
  have hAc : A * suzInv 0 = suzInv 0 * A :=
    (eqA_iff (rep_compA hRA hR0) (rep_compA hR0 hRA)).1 hcA
  have hBc : B * suzInv 0 = suzInv 0 * B :=
    (eqA_iff (rep_compA hRB hR0) (rep_compA hR0 hRB)).1 hcB
  have hAM : A ∈ suzM := suzWord_mem hlA
  have hBM : B ∈ suzM := suzWord_mem hlB
  let gs2 : ℕ → Equiv.Perm (Fin 1782) := fun h => if h = 0 then A else B
  have hS2 : ∀ h < 2, Rep 1782 suzArrAB[h]! (gs2 h) := Solomon78.rep_two_getElem! (f := gs2) hRA hRB
  have hS2i : ∀ h < 2, Rep 1782 suzArrABi[h]! (gs2 h)⁻¹ :=
    Solomon78.rep_two_getElem! (f := fun h => (gs2 h)⁻¹) hRAi hRBi
  obtain ⟨ev, hev, hevK⟩ : ∃ ev : List ℤ → Equiv.Perm (Fin 1782),
      (∀ w, lettersOK 2 w = true → Rep 1782 (suzArrWord w) (ev w)) ∧
        ∀ w, ev w ∈ Subgroup.closure {A, B} := by
    refine ⟨fun w => Quiver.SchreierGraph.evalWord (fun h : Fin 2 => gs2 h) (toLetters 2 w),
      fun w hw => rep_wordA hS2 hS2i w hw, fun w => ?_⟩
    have := evalWord_mem_closure (fun h : Fin 2 => gs2 h) (toLetters 2 w)
    have e : Set.range (fun h : Fin 2 => gs2 h) = {A, B} := range_fun_two A B
    rwa [e] at this
  have h2 := Certificates.certificate26990
  simp only [suzPinCheck, Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨hpl, hE8⟩, hperf⟩, hcomm⟩, hK⟩ := h2
  simp only [suzPinLetters, Bool.and_eq_true, beq_iff_eq] at hpl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlE1, hlE2⟩, hlE3⟩, hlU1⟩, hlV1⟩, hlU2⟩, hlV2⟩, hlC⟩, hlD⟩, hsA⟩, hsB⟩ := hpl
  have hKcl : ⁅Subgroup.closure {A, B}, Subgroup.closure {A, B}⁆ = Subgroup.closure {A, B} := by
    refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy => ?_) ?_
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
        (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    ·
      simp only [suzPerfCheck, suzCommOK, Bool.and_eq_true] at hperf
      obtain ⟨⟨⟨hiU1, hiV1⟩, hcA'⟩, ⟨⟨hiU2, hiV2⟩, hcB'⟩⟩ := hperf
      have h1 := (eqA_iff (rep_suzCommArr (hev _ hlU1) (hev _ hlV1) hiU1 hiV1) hRA).1 hcA'
      have h2 := (eqA_iff (rep_suzCommArr (hev _ hlU2) (hev _ hlV2) hiU2 hiV2) hRB).1 hcB'
      have hAK : A ∈ ⁅Subgroup.closure {A, B}, Subgroup.closure {A, B}⁆ := by
        have := Subgroup.commutator_mem_commutator (hevK suzWordU1) (hevK suzWordV1)
        rwa [commutatorElement_def, h1] at this
      have hBK : B ∈ ⁅Subgroup.closure {A, B}, Subgroup.closure {A, B}⁆ := by
        have := Subgroup.commutator_mem_commutator (hevK suzWordU2) (hevK suzWordV2)
        rwa [commutatorElement_def, h2] at this
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hAK
      · exact hBK
  refine ⟨Subgroup.closure {A, B}, ?_, ?_, hKcl, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hAM
    · exact hBM
  · have hle : Subgroup.closure {A, B} ≤
        centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782))) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact mem_centralizer_singleton_iff.2 hAc
      · exact mem_centralizer_singleton_iff.2 hBc
    intro k hk
    exact mem_centralizer_singleton_iff.1 (hle hk)
  · simp only [suzKCheck, Bool.and_eq_true, beq_iff_eq] at hK
    obtain ⟨hgenK, hsize⟩ := hK
    have hTA : TabRep suzArrA A := ⟨hsA, hRA⟩
    have hTB : TabRep suzArrB B := ⟨hsB, hRB⟩
    have hE : Enumerates (Subgroup.closure {A, B}) (enumOf 1782 suzArrAB 20160).tabs.toList := by
      refine enumerates_closure ?_ ?_ hgenK
      · rintro a (rfl | rfl)
        · exact ⟨0, by simp [suzArrAB], hTA⟩
        · exact ⟨1, by simp [suzArrAB], hTB⟩
      · intro j hj
        have hj2 : j < 2 := by simpa [suzArrAB] using hj
        interval_cases j
        · exact ⟨A, Or.inl rfl, hTA⟩
        · exact ⟨B, Or.inr rfl, hTB⟩
    rw [hE.card, Array.length_toList, hsize]
  ·
    simp only [suzE8Check, Bool.and_eq_true, Bool.not_eq_true'] at hE8
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, n7⟩ := hE8
    have ra := hev suzWordE1 hlE1
    have rb := hev suzWordE2 hlE2
    have rc := hev suzWordE3 hlE3
    have ha2 := (eqA_iff (rep_compA ra ra) rep_idA).1 e1
    have hb2 := (eqA_iff (rep_compA rb rb) rep_idA).1 e2
    have hc2 := (eqA_iff (rep_compA rc rc) rep_idA).1 e3
    have hab := (eqA_iff (rep_compA ra rb) (rep_compA rb ra)).1 e4
    have hac := (eqA_iff (rep_compA ra rc) (rep_compA rc ra)).1 e5
    have hbc := (eqA_iff (rep_compA rb rc) (rep_compA rc rb)).1 e6
    have m1 := ne_of_eqA_false ra rep_idA n1
    have m2 := ne_of_eqA_false rb rep_idA n2
    have m3 := ne_of_eqA_false rb ra n3
    have m4 := ne_of_eqA_false rc rep_idA n4
    have m5 := ne_of_eqA_false rc ra n5
    have m6 := ne_of_eqA_false rc rb n6
    have m7 := ne_of_eqA_false rc (rep_compA ra rb) n7
    exact three_le_pRank_of_three_involutions
      (a := (⟨ev suzWordE1, hevK _⟩ : ↥(Subgroup.closure {A, B})))
      (b := (⟨ev suzWordE2, hevK _⟩ : ↥(Subgroup.closure {A, B})))
      (c := (⟨ev suzWordE3, hevK _⟩ : ↥(Subgroup.closure {A, B})))
      (Subtype.ext ha2) (Subtype.ext hb2) (Subtype.ext hc2) (Subtype.ext hab) (Subtype.ext hac)
      (Subtype.ext hbc) (fun h => m1 (congrArg Subtype.val h))
      (fun h => m2 (congrArg Subtype.val h))
      (fun h => m3 (congrArg Subtype.val h)) (fun h => m4 (congrArg Subtype.val h))
      (fun h => m5 (congrArg Subtype.val h)) (fun h => m6 (congrArg Subtype.val h))
      (fun h => m7 (congrArg Subtype.val h))

theorem suz_commutator_data : ∃ e x : Equiv.Perm (Fin 1782), e ∈ suzM ∧ x ∈ suzM ∧
    e * suzInv 0 = suzInv 0 * e ∧ x * suzInv 0 = suzInv 0 * x ∧
      e * x * e⁻¹ * x⁻¹ = suzInv 0 := by
  have h2 := Certificates.certificate26990
  simp only [suzPinCheck, Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨hpl, hE8⟩, hperf⟩, hcomm⟩, hK⟩ := h2
  simp only [suzPinLetters, Bool.and_eq_true, beq_iff_eq] at hpl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlE1, hlE2⟩, hlE3⟩, hlU1⟩, hlV1⟩, hlU2⟩, hlV2⟩, hlC⟩, hlD⟩, hsA⟩, hsB⟩ := hpl
  simp only [suzCommCheck, suzCommOK, Bool.and_eq_true] at hcomm
  obtain ⟨⟨hcC, hcD⟩, ⟨hiC, hiD⟩, hE⟩ := hcomm
  have rC : Rep 1782 (suzArr suzWordC) (suzWord suzWordC) :=
    rep_suzArr (lettersOK_mono (by norm_num) hlC)
  have rD : Rep 1782 (suzArr suzWordD) (suzWord suzWordD) :=
    rep_suzArr (lettersOK_mono (by norm_num) hlD)
  have r0 : Rep 1782 (tArr 0) (suzInv 0) := rep_suzInv (by norm_num)
  refine ⟨suzWord suzWordC, suzWord suzWordD, suzWord_mem hlC, suzWord_mem hlD, ?_, ?_, ?_⟩
  · exact (eqA_iff (rep_compA rC r0) (rep_compA r0 rC)).1 hcC
  · exact (eqA_iff (rep_compA rD r0) (rep_compA r0 rD)).1 hcD
  · exact (eqA_iff (rep_suzCommArr rC rD hiC hiD) r0).1 hE

theorem suz_pinned_pair : ∃ (ut : ↥suzM) (Kt : Subgroup ↥suzM), ut * ut = 1 ∧ ut ≠ 1 ∧
    (∀ k ∈ Kt, k * ut = ut * k) ∧ ⁅Kt, Kt⁆ = Kt ∧ Nat.card Kt = 20160 ∧
      3 ≤ CFSG.pRank 2 Kt := by
  obtain ⟨K, hKM, hKc, hKp, hKcard, hKrank⟩ := suz_pinned_data
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ht0M, -⟩ := suz_row_facts
  refine ⟨⟨suzInv 0, ht0M⟩, K.subgroupOf suzM, Subtype.ext (suzInv_sq (by norm_num)),
    fun h => suzInv_ne_one (i := 0) (by norm_num) (congrArg Subtype.val h), ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact Subtype.ext (hKc k (Subgroup.mem_subgroupOf.1 hk))
  · have hperf : Group.IsPerfect ↥K := isPerfect_iff.mpr hKp
    exact isPerfect_iff.mp (isPerfect_subgroupOf_of_le hKM hperf)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hKcard]
  · rw [pRank_two_eq_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKM)]
    exact hKrank

end CFSG.EvenSporadicStandard.Induction
