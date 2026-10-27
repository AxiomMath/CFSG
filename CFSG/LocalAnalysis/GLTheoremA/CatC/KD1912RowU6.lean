module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowU6Special
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowU6Blk
public import CFSG.GroupTheory.TwoNilpotentOfCardTwoMulPrime
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6
public import CFSG.Goldschmidt75.B1Comp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank23
public import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open
open CFSG.Fischer
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem card_outer_six : Nat.card (Outer S6) = 6 := by
  have hv : (TauCeti.LieTypeIndex.twistedA 5 ppTwo).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [ppTwo]
  obtain ⟨eM⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.nonempty_equiv_timmesfeldPSU 5 ppTwo hv
    (by simp [ppTwo]) (MulEquiv.refl _)
  obtain ⟨eS⟩ := CFSG.LocalAnalysis.GLTheoremA.LevelLieU6.bridge_u6two_stated hv
    (by simp [ppTwo]) (MulEquiv.refl _)
  have h := Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (eS.symm.trans eM)).toEquiv
  rw [h, CFSG.LargeExtraspecial.S14.card_outer_timmesfeldPSU_six]

theorem twoNilpotent_outer_six : TwoNilpotent (Outer S6) :=
  CFSG.twoNilpotent_of_card_eq_two_mul_prime Nat.prime_three (by norm_num)
    (by rw [card_outer_six])

theorem outTwoNilpConcl_six : CFSG.LieType.ChevTwo.OutTwoNilpConcl S6 :=
  CFSG.Quasithin.H13.OutTwoNilp.outTwoNilpotent_of_twoNilpotent_outer twoNilpotent_outer_six

theorem center_six : Subgroup.center S6 = ⊥ := by
  haveI := isSimple_S6
  haveI : Group.IsPerfect M6 :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := 1) (K := F4) hF4card
      (n := 6) (by norm_num) (by decide)
  exact CFSG.Goldschmidt75.center_eq_bot_of_simple

theorem oddCoreFact_three_six : OddCoreFact 3 S6 := by
  refine ⟨outTwoNilpConcl_six, fun α hα => ?_⟩
  have hα3 : α ^ 3 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  rw [odd_card_gLAPPrimeCoreOf_innerAut_inf_centralizer_iff center_six 3 α]
  change Odd (Nat.card (GLAPPrimeCoreOf 3 (fixSubgroup α)))
  rw [show GLAPPrimeCoreOf 3 (fixSubgroup α) = ⊥ from
    gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr
      (u6TwoOddCoreThree_of_cases u6TwoBlockCore_holds
        u6TwoNineCore_holds α hα3), Subgroup.card_bot]
  exact odd_one

theorem oddCoreFact_three_of_twistedA5_two {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hq : q.card = 2)
    {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 5 q, hv⟩).Group) :
    OddCoreFact 3 S := by
  obtain ⟨eS⟩ := CFSG.LocalAnalysis.GLTheoremA.LevelLieU6.bridge_u6two_stated hv hq e
  exact (oddCoreFact_congr (p := 3) eS).mpr oddCoreFact_three_six

end CFSG.LocalAnalysis.GLTheoremA.KD1912
