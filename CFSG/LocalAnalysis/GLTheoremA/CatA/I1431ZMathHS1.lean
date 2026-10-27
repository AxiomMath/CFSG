module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24Five
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711c2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Z

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c


theorem row_fi22 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : I1431SporRow .Fi22 := by
  have hc : Nat.card (NativeSporadic.Carrier .Fi22) = 64561751654400 := CFSG.Sporadic.Fi22.card_Fi22
  haveI : Finite (NativeSporadic.Carrier .Fi22) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (NativeSporadic.Carrier .Fi22) := CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
  refine row_of_centShapeRk (s := .Fi22) hOut (hbr .Fi22).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    fi22CentShapeRk_native ?_
  intro T _ hT hcT
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Multipliers.U43.card_X₀] at hcT
  norm_num at hcT

theorem row_ly (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : I1431SporRow .Ly := by
  have hc : Nat.card (NativeSporadic.Carrier .Ly) = 51765179004000000 := CFSG.Sporadic.Ly.card_Ly'
  haveI : Finite (NativeSporadic.Carrier .Ly) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (NativeSporadic.Carrier .Ly) := CFSG.Sporadic.Ly.isSimpleGroup_Ly
  refine row_of_centShapeRk (s := .Ly) hOut (hbr .Ly).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    lyShape_three ?_
  intro T _ hT hcT
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL] at hcT
  norm_num at hcT

theorem row_th (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : I1431SporRow .Th := by
  have hc : Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 :=
    CFSG.RankThree.PartOne.CTP.card_Th
  haveI : Finite (NativeSporadic.Carrier .Th) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (NativeSporadic.Carrier .Th) :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th
      CFSG.Sporadic.Th.th_kernel_facts
  refine row_of_centShapeRk (s := .Th) hOut (hbr .Th).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    thCentShapeRk_native ?_
  intro T _ hT hcT
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, CFSG.GH74.QTGen4.Recog.G23.ghat_card] at hcT
  norm_num at hcT

theorem row_fi23 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : I1431SporRow .Fi23 := by
  have hc : Nat.card (NativeSporadic.Carrier .Fi23) = 4089470473293004800 :=
    CFSG.Sporadic.Fi23.card_Fi23
  haveI : Finite (NativeSporadic.Carrier .Fi23) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (NativeSporadic.Carrier .Fi23) := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  refine row_of_centShapeRk (s := .Fi23) hOut (hbr .Fi23).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    fi23CentShapeRk_native ?_
  intro T _ hT hcT
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, CFSG.HardMathSupport.Dickson.I271.tabFi23_card_om] at hcT
  norm_num at hcT

theorem row_fi24 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1431SporRow .Fi24Prime := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.Fi24FiveRows.fi24_model hbr
  have hC := CFSG.HardMathSupport.Dickson.I271.TabFi24.centShapeRk_J_good
    (Good := fun T _ => Nat.card T ≠ 25920)
    (fun T T' _ _ e h hc => h ((Nat.card_congr e.toEquiv).trans hc))
    (fun _ _ _ _ hT => by rw [hT]; norm_num) (fun _ _ _ _ hT => by rw [hT]; norm_num)
  exact @row_of_centShapeRk .Fi24Prime _ _ hfin hs hOut b hnc _ _ hC (fun _ _ h => h)

end CFSG.LocalAnalysis.GLTheoremA.I1431Z
