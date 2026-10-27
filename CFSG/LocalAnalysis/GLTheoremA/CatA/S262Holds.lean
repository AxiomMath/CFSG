module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262List
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262Alt8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262GF2Uni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262OmM8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262E6Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262E78
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262E78Data
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest11
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE7
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE8
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LiePL
public import CFSG.HardMathSupport.Solomon.Coordinator.I713

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem good3On_gf2Uni (hPL : KD264PL 3) : Good3On gf2Uni :=
  good3On_of_fixed_perfect hPL (fun e he => by
    cases e <;> simp only [gf2Uni] at he
    · exact three_ne_characteristic_of_card_two
        (TauCeti.LieTypeIndex.characteristic_twistedA _ _) he.2
    all_goals exact he.elim) fixed_perfect_gf2Uni

theorem i262GF2_holds
    : I262GF2 := by
  have hPL : KD264PL 3 := kd264PL_holds 3 Nat.prime_three (by norm_num)
  exact i262GF2_of_families (good3On_gf2Lin hPL) (good3On_gf2Uni hPL) (good3On_gf2Symp hPL)
    (good3On_gf2OrthPlus hPL) (good3On_gf2OrthMinus hPL) (good3On_gf2E7 hPL e7_reps_good)
    (good3On_gf2E8 hPL e8_reps_good) (e9GoodOn_gf2OmMinus8 hPL) (e9GoodOn_gf2E6 hPL)

theorem i262_holds
    : I262 :=
  i262_of_parts (fun p hp hp2 => kd264ExcNoGood_of_inputs kd264OutCyc_holds
      (kd264OuterIdx_of_families lieOuterIdx_linear lieOuterIdx_unitary lieOuterIdx_classicalBCD
          lieOuterIdx_triality lieOuterIdx_excUntwisted lieOuterIdx_excTwisted)
      (kd264InnGood_of_exc lieInnGood_E6 lieInnGood_E7 lieInnGood_E8 lieInnGood_twistedE6)
      kd264TriInnGood_holds hp hp2 (kd264PL_holds p hp hp2))
    i262GF2_holds i262Alt8_holds

theorem qUList_holds
    : S265.QUList :=
  qUList_of_i262 i262_holds

theorem qSList_holds
    : S265.QSList :=
  qSList_of_i262 i262_holds
    (fun Ω _ _ _ hp hp2 => chevClosureQAt_of_lieComp_lieComps (G := Ω) lieComp_holds
      (fun _ hq hq5 => lieCompsOn_holds hq hq5) hp hp2 hp hp2)
    CFSG.HardMathSupport.Solomon.Coordinator.i_7_13_1_pPrime_holds

end CFSG.LocalAnalysis.GLTheoremA.S262

end
