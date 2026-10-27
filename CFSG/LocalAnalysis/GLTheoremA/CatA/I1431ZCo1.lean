module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Z

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.I271 (CentShape CentShapeRk)



section Co1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier

theorem row_co1 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : I1431SporRow .Co1 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := CFSG.HardMathSupport.Dickson.I271.TabCo1.co1_model_five hbr
  have hC := CFSG.HardMathSupport.Dickson.I271.TabCo1.tabCo1_centShapeRk_three_good
    (Good := fun T _ => Nat.card T ≠ 25920)
    (fun T T' _ _ e h hc => h ((Nat.card_congr e.toEquiv).trans hc))
    (fun T _ e hc => by
      have h1 : Nat.card T = 3265920 := (Nat.card_congr e.toEquiv).trans
        CFSG.LieType.Multipliers.U43.card_X₀
      rw [h1] at hc
      norm_num at hc)
    (by
      show Nat.card ↥(alternatingGroup (Fin 9)) ≠ 25920
      rw [CFSG.HardMathSupport.Dickson.I271.TabCo1.card_alt_nine]
      norm_num)
    (fun _ _ hc _ => by
      show _ ≠ 25920
      rw [hc]
      norm_num)
    (hbr .Suz)
  exact @row_of_centShapeRk .Co1 ↥GA _ hfin hs hOut b hnc _ _ hC (fun _ _ h => h)

end Co1

end CFSG.LocalAnalysis.GLTheoremA.I1431Z

end
