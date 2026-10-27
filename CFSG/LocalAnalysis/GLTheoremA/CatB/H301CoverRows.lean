module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301CoverLift3
public import CFSG.Sporadic.Fi24I301Cover.Row
public import CFSG.Sporadic.SuzI301Cover.Row
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.LocalAnalysis.GLTheoremA.S8


theorem i301ARowCover_all : ∀ row : Row, I301ARowCover row := by
  intro row
  cases row with
  | fi24h => exact CFSG.Sporadic.Fi24I301Cover.i301ARowCover_fi24h
  | suzh => exact CFSG.Sporadic.SuzI301Cover.i301ARowCover_suzh
  | ly => intro hc; exact absurd hc (by decide)
  | co2 => intro hc; exact absurd hc (by decide)
  | co1 => intro hc; exact absurd hc (by decide)
  | fi24 => intro hc; exact absurd hc (by decide)
  | suz => intro hc; exact absurd hc (by decide)
  | th => intro hc; exact absurd hc (by decide)
  | m3 => intro hc; exact absurd hc (by decide)
  | m5 => intro hc; exact absurd hc (by decide)

theorem i301ACoverAt_holds : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), I301ACoverAt G p :=
  fun _ _ _ _ => i301ACoverAt_of_rows
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds i301ARowCover_all

end CFSG.LocalAnalysis.GLTheoremA.H301
