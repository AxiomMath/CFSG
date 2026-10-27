module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ONThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.McLThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.McL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Z

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.I271 (CentShape CentShapeRk)

theorem row_on (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : I1431SporRow .ONan := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = 460815505920 :=
    CFSG.Sporadic.ON.card_ON
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    Finite.of_equiv _ CFSG.ONSchreier.onEquivPv.symm.toEquiv
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  refine row_of_centShapeRk (s := .ONan) hOut (hbr .ONan).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    CFSG.HardMathSupport.Dickson.I271.onThree_centShapeRk ?_
  intro T _ hT hc
  obtain ⟨-, ⟨e⟩⟩ := hT
  rw [Nat.card_congr e.toEquiv, card_alt_six_eq] at hc
  norm_num at hc

theorem row_mcl (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : I1431SporRow .McL := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .McL) = 898128000 :=
    CFSG.Sporadic.McL.card_McL
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    CFSG.Sporadic.McL.isSimpleGroup_McL
  have hsh := CFSG.HardMathSupport.Dickson.I271.mcl_constrainedShape_three
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL
  refine row_of_model (s := .McL) hOut (hbr .McL).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    fun k hk => ?_
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; norm_num at hk
  intro I hI
  exact (KDSpor.false_of_glaPComponent_of_pConstrained Nat.prime_three
    (hsh k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k)) hI).elim

end CFSG.LocalAnalysis.GLTheoremA.I1431Z

end
