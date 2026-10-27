module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSkel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFinalFour
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Setup
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.SeitzReduction (SeitzSetting seitzSetting_of quotientCenterMulEquiv lieModel_of_mulEquiv)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

theorem card_of_lieModel_l44 {W : Type} [Group W] (h : LieModel W .PSL 4 2 2) :
    Nat.card W = 987033600 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_four (h.statedClassicalModel (by decide))

theorem not_evenStandardException_of_card_eq_l44
    {Q : Type} [Group Q] (hQ : Nat.card Q = 987033600) :
    ¬ Recognition.Exact.EvenStandardException Q := by
  classical
  rintro (h1 | h1 | h1 | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | h1 | h1 | h1)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · have hle : Nat.card Q ≤ Fintype.card K ^ 16 := by
      rw [Nat.card_congr e.toEquiv]
      calc Nat.card (commutator (Matrix.symplecticGroup (Fin 2) K))
          ≤ Nat.card (Matrix.symplecticGroup (Fin 2) K) := Subgroup.card_le_card_group _
        _ ≤ Nat.card (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
            Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = Fintype.card K ^ 16 := by
            rw [Matrix, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]
            simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
            ring
    rw [hQ, hK] at hle
    exact absurd hle (by norm_num)
  · have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
    have hH : Nat.card (Chevalley.adjointGroup .G2 K) = 12096 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK2]
      rfl
    have : Finite (Chevalley.adjointGroup .G2 K) :=
      Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
    have hle : Nat.card Q ≤ 12096 := by
      rw [Nat.card_congr e.toEquiv, ← hH]
      refine Subgroup.card_le_of_le (Subgroup.commutator_le.2 fun a ha c hc => ?_)
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hc) (inv_mem ha)) (inv_mem hc)
    rw [hQ] at hle
    exact absurd hle (by norm_num)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · obtain ⟨e⟩ := h1
    rw [Nat.card_congr e.toEquiv] at hQ
    change Nat.card CFSG.Blueprint.NativeSporadic.He = _ at hQ
    rw [CFSG.Sporadic.He.card_He] at hQ
    exact absurd hQ (by norm_num)

theorem center_eq_bot_of_l44
    {K W : Type} [Group K]
    [Finite K] [Group W] [Finite W] (hK : Group.IsPerfect K) (e : K ⧸ center K ≃* W)
    (h : LieModel W .PSL 4 2 2) : center K = ⊥ := by
  have hsc : Assembly.LowTwoRank.StatedClassicalModel W .PSL 4 2 2 :=
    ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl h
  obtain ⟨hcomm, ⟨eM⟩⟩ := LieType.Steinberg.CentralExt.GriessClassical.psl_row hsc
  have hWperf : Group.IsPerfect W := ⟨hcomm⟩
  let p : K →* W := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hpker : p.ker = center K := by
    ext k
    simp only [p, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hdvd := RankThree.PartOne.card_ker_dvd_card_hopfMultiplier hWperf hK p hp hpker.le
  rw [hpker, Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess W).symm.toEquiv,
    Nat.card_congr eM.toEquiv] at hdvd
  have h1 : Nat.card (Multiplier.generic .PSL 4 2 2 × Multiplier.exceptional .PSL 4 2 2) = 1 := by
    have hg : Multiplier.genericOrders .PSL 4 2 2 = (1, 1) := by decide
    have hx : Multiplier.exceptionalOrders .PSL 4 2 2 = (1, 1) := rfl
    unfold Multiplier.generic Multiplier.exceptional
    rw [hg, hx, Nat.card_prod, Nat.card_prod]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [h1, Nat.dvd_one] at hdvd
  exact Subgroup.card_eq_one.1 hdvd

section Main


theorem linearFourInput_holds : CFSG.SeitzReduction.LinearPilot.LinearFourInput :=
  CFSG.SeitzReduction.LinearPilot.linearFourInput_of_factorNormal
    CFSG.SeitzReduction.gls3OddLieAutComponentsInput
    (CFSG.SeitzReduction.CrossChar.sLmNotOddLieInputAt (by norm_num))
    CFSG.SeitzReduction.LinearPilot.catSLmSporadicAt_three
    (CFSG.SeitzReduction.LinearPilot.linearSwapFactorNormalFourInput_of_factorNormal
      CFSG.SeitzReduction.LinearPilot.linearSwapFactorNormalInput_holds)

theorem shapeTwoTenL44Excl_holds : ShapeTwoTenL44Excl := by
  intro G _ _ L Q z u h d T e x hx hτ hfus hzx hL
  obtain ⟨hx2, -, hx1⟩ := swap_elt_facts h d T e hx hτ
  have hxord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  obtain ⟨W, hWN, hCW, -, hLie⟩ := hL
  have hWs : IsSimpleGroup W := CFSG.SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_PSL hLie
  have hWc := card_of_lieModel_l44 hLie
  have hWp : ¬ (Nat.card W).Prime := by
    rw [hWc]
    intro hp
    have := hp.eq_one_or_self_of_dvd 2 (by norm_num)
    omega
  obtain ⟨K, hK, ⟨eK⟩, -, hCK⟩ := exists_stdHyp_of_twoSec_cent h hxord hCW hWs hWp
  have hKperf : Group.IsPerfect K := ⟨hK.standard.1.1⟩
  have hZ : center K = ⊥ := center_eq_bot_of_l44 hKperf eK hLie
  have eKW : K ≃* W := (quotientCenterMulEquiv hZ).symm.trans eK
  obtain ⟨F, _, _, hF4, ⟨eW⟩⟩ := exists_projectiveSL_of_lieModel_four hLie
  have : CharP F 2 := charP_two_of_card_four hF4
  have hLMq : LieModel (K ⧸ center K) .PSL 4 2 2 := lieModel_of_mulEquiv eK.symm hLie
  have hcardq : Nat.card (K ⧸ center K) = 987033600 := (Nat.card_congr eK.toEquiv).trans hWc
  have hadm : Assembly.LowTwoRank.StatedLieAdmissible .PSL 4 2 2 :=
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl hLie).1
  obtain ⟨S, hS⟩ := hK.cyclicSylow
  have : IsSimpleGroup G := h.std.simple
  have hset : SeitzSetting G K := seitzSetting_of h.std.nonab h.std.kProper hK.standard hK.oddCore
    S hS (Or.inl ⟨.PSL, 4, 2, hadm, hLMq⟩) (not_evenStandardException_of_card_eq_l44 hcardq) hZ
  exact linearFourInput_holds G K hset 2 F (by rw [hF4]; norm_num) le_rfl (eKW.trans eW) x hxord
    hCK

end Main

end CFSG.OddStandard.AltStdSec
