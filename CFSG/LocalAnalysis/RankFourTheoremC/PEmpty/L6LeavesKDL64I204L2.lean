module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmDefs
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Final
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieL2

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Dickson.I271
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Subgroup
open scoped commutatorElement MatrixGroups

theorem kdL64I204L2_pPrimeCore_bot {p : ℕ} (hp : p.Prime) {Z : Type} [Group Z] [Finite Z]
    {L : Subgroup Z} [IsSimpleGroup ↥L] (hLn : L.Normal) (hpL : p ∣ Nat.card ↥L)
    (hC : Subgroup.centralizer (L : Set Z) = ⊥) : CFSG.pPrimeCore p Z = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  haveI : (N.subgroupOf L).Normal := hN.subgroupOf L
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf L) with h | h
  · have hdisj : N ⊓ L = ⊥ := disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h)
    have hNc : N ≤ Subgroup.centralizer (L : Set Z) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hmem : ⁅k, l⁆ ∈ N ⊓ L :=
        Subgroup.commutator_le_inf N L (Subgroup.commutator_mem_commutator hk hl)
      rw [hdisj, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem.symm
    rw [hC] at hNc
    exact le_bot_iff.1 hNc
  · exfalso
    have hLN : L ≤ N := Subgroup.subgroupOf_eq_top.1 h
    have hd : p ∣ Nat.card N := hpL.trans (Subgroup.card_dvd_of_le hLN)
    exact hp.one_lt.ne' (hcop.eq_one_of_dvd hd)

theorem kdL64I204L2_holds
    : KDL64I204L2 := by
  intro p hp hp5 Z _ _ L hLn hL2 hC B hB _ hBsc W hBW hcop
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eL⟩⟩ := hL2
  have hp2 : p ≠ 2 := by omega
  have h5 : 5 ≤ p ^ p := le_trans hp5 (le_self_pow (by omega) (by omega))
  have h4 : 4 ≤ Nat.card K := by rw [hKcard]; omega
  have h3 : p ^ p ≠ 3 := by omega
  obtain ⟨hsimpP, hnabP⟩ :=
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.simple_nonabelian_projectiveSL_two h4
  let eLP : ↥L ≃* projectiveSL 2 K :=
    eL.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K)
  haveI : IsSimpleGroup ↥L := eLP.isSimpleGroup
  have hZP : Subgroup.center (projectiveSL 2 K) = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnabP
  have hZL : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxP : eLP x ∈ Subgroup.center (projectiveSL 2 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := eLP.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
    rw [hZP, Subgroup.mem_bot] at hxP
    rw [Subgroup.mem_bot]
    exact eLP.injective (hxP.trans (map_one eLP).symm)
  have hqL : CFSG.Open.IsQuasisimple ↥L := by
    have hPSL : CFSG.IsQuasisimple (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
      (CFSG.Foundations.SteinbergCA.quasisimple_iff
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).2.2.1.mpr
        (CFSG.ComponentClassification.RankTwoOddLie.isQuasisimple_psl2 h4)
    exact (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥L).2.2.1.mp
      (CFSG.IsQuasisimple.of_mulEquiv eL hPSL)
  have hpL : p ∣ Nat.card ↥L := by
    rw [Nat.card_congr eLP.toEquiv]
    exact CFSG.SignalizerFunctorTheorem.CatalogBridge.dvd_card_projectiveSL_of_dvd le_rfl hp
      (by rw [hKcard]; exact dvd_pow_self p (by omega))
  have hcore : GLAPPrimeCore p Z = ⊥ := kdL64I204L2_pPrimeCore_bot hp hLn hpL hC
  have hcomp : GLAPComponent p ⊤ L :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hqL hpL le_top
      (hLn.subgroupOf ⊤)
  have hscp : IsSCp p ⊤ B :=
    ⟨le_top, hB, fun E _ hE hBE => le_antisymm (fun y hy => hBsc y
      (Subgroup.mem_centralizer_iff.2 fun b hb =>
        congrArg Subtype.val (hE.1.is_comm.comm (⟨b, hBE hb⟩ : ↥E) ⟨y, hy⟩)) (hE.2 y hy)) hBE⟩
  have hLtop : Subgroup.normalizer (L : Set Z) = ⊤ := Subgroup.normalizer_eq_top L
  have hnorm : B ≤ Subgroup.normalizer (L : Set Z) := by rw [hLtop]; exact le_top
  have hchevP : IsChevSimple p (projectiveSL 2 K) :=
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.isChevSimple_projectiveSL_two hp hp2
      (by omega) hKcard h3
  have hchev : IsChevSimple p (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZL).trans
        (QuotientGroup.quotientBot.trans eLP)).symm hchevP
  have hH : Chev204Hyp p L B := ⟨hp, hp2, hcore, hcomp, hscp, hnorm, hchev⟩
  have hne : ¬ ChevExc p L B := by
    rintro ⟨h3', -⟩
    omega
  have hDC : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree :=
    CFSG.HardMathSupport.Solomon.Coordinator.defCharInnerCoreFree_holds
  have hOut : CFSG.HardMathSupport.Dickson.I271.DefCharOuterCoreFree :=
    CFSG.HardMathSupport.Dickson.I271.defCharOuterCoreFree_of_kdata
      CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutCoreFree_holds
      CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutCentInner_holds
  have hamb : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.LocalAnalysis.GLTheoremA.KDAmbSolv q :=
    fun q hq hq2 => CFSG.LocalAnalysis.GLTheoremA.kdAmbSolv_holds hq hq2
      CFSG.LocalAnalysis.GLTheoremA.u42_fixSubgroup_solvable
  have hU := fun (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) =>
    CFSG.LocalAnalysis.GLTheoremA.kdChevUnique_of hq hq2
      (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds hq hq2)
      (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutChevUnique_holds hq hq2)
      (hamb q hq hq2)
  have hT := fun (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) =>
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutChev_holds hq hq2
  have hE := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutExc_of_outerCent
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.outerCentAll_holds
    (hamb 3 Nat.prime_three (by norm_num))
  have hCent : ChevCentralizerStep :=
    CFSG.HardMathSupport.Dickson.I271.chevCentralizerStep_of_kdata hU hT hE
  have hCyc : ChevCyclicCase :=
    CFSG.HardMathSupport.Dickson.I271.chevCyclicCase_of_nineFold
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      (fun q hq hq2 => CFSG.LocalAnalysis.GLTheoremA.kd65_holds hq hq2)
      CFSG.HardMathSupport.Dickson.I271.kdU43NineFold_holds
  have hAmb : ChevAmbCase := CFSG.HardMathSupport.Dickson.I271.chevAmbCase_holds
  have hbal := CFSG.HardMathSupport.Dickson.I271.chev204_induction hDC hOut
    (CFSG.LocalAnalysis.GLTheoremA.kd65_holds hp hp2)
    (CFSG.LocalAnalysis.GLTheoremA.kdChevInner_of hp hp2
      (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds hp hp2) (hamb p hp hp2))
    hCent hCyc hAmb (Nat.card Z) Z rfl L B hH hne
  have hWN : W ≤ Subgroup.normalizer (L : Set Z) := by rw [hLtop]; exact le_top
  have hcop' : Nat.Coprime p (Nat.card W) :=
    (Nat.Coprime.coprime_dvd_right (dvd_mul_left p 2) hcop).symm
  have hBW' : B ⊓ Subgroup.normalizer (L : Set Z) ≤ Subgroup.normalizer (W : Set Z) :=
    inf_le_left.trans hBW
  have hWC : W ≤ Subgroup.centralizer (L : Set Z) := hbal W hWN hcop' hBW'
  rw [hC] at hWC
  exact le_bot_iff.1 hWC

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
