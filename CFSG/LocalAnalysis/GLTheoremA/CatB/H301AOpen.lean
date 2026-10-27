module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.Sporadic.LyI301.Row
public import CFSG.Sporadic.ThI301.Row
public import CFSG.Sporadic.Co1I301.Row
public import CFSG.Sporadic.Co2I301.Row
public import CFSG.Sporadic.SuzI301.Row

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8

section Open


theorem i301AAt_of_open (hfi24 : I301ARow .fi24) (hm3 : I301ARow .m3) (hm5 : I301ARow .m5)
    (hcov : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), I301ACoverAt G p) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ), I301AAt G p := by
  intro G _ _ p
  refine i301AAt_of_rows CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds (fun row => ?_) (hcov G p)
  cases row with
  | ly => exact CFSG.Sporadic.LyI301.i301ARow_ly
  | co2 => exact CFSG.Sporadic.Co2I301.i301ARow_co2
  | co1 => exact CFSG.Sporadic.Co1I301.i301ARow_co1
  | fi24 => exact hfi24
  | fi24h => intro hc; exact absurd hc (by decide)
  | suz => exact CFSG.Sporadic.SuzI301.i301ARow_suz
  | suzh => intro hc; exact absurd hc (by decide)
  | th => exact CFSG.Sporadic.ThI301.i301ARow_th
  | m3 => exact hm3
  | m5 => exact hm5

end Open

end CFSG.LocalAnalysis.GLTheoremA.H301

end
