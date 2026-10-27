module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T11
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T6
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T13
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T15

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly
open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open scoped commutatorElement


theorem exc_of_residuals
    (G : Type) [Group G] [Finite G] (hcls : ExcChev2Class) (hA6 : A6NoChar2Lambda)
    (hTD4 : TD4C1NotExc) :
    ∀ (X L : Subgroup G) (b : G), GLAPComponent 3 X L → IsChevSimple 2 (PSimple 3 L) → b ^ 3 = 1 →
      R2Prop 3 b L → (IsTD4 3 L → centCard2 3 L b = Nat.sqrt (card2 3 L)) →
      GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) → Ipart 3 L b ≠ ⊥ →
      catalogIs (PSimple 3 (Ipart 3 L b)) excIndex →
      catalogIs (PSimple 3 L) (fun i => S9.isSp4eight i ∨ S9.isL3char2 i ∨ S9.isU3char2 i) := by
  intro X L b hL hchev hbp hR hcent hI hIne hexc
  rcases hR with hF | ⟨-, hTDL, hNI⟩
  · exact exc_fieldOn G hcls hA6 X L b hL hchev hbp hF hI hIne hexc
  · exact (hTD4 G X L b hL hchev hTDL hbp hNI (hcent hTDL) (Ipart 3 L b) hI hIne hexc).elim

theorem i91TypeAt_of_residuals
    (G : Type) [Group G] [Finite G] (hcls : ExcChev2Class)
    (hA6 : A6NoChar2Lambda) (hTD4 : TD4C1NotExc) : I91TypeAt G :=
  { exc := exc_of_residuals G hcls hA6 hTD4
    l3 := l3_of_td4 td4NotL3_holds G }

theorem i91TypeAt_of_TD4C1NotExc
    (G : Type) [Group G] [Finite G] (hTD4 : TD4C1NotExc) : I91TypeAt G :=
  i91TypeAt_of_residuals G (excChev2_class catDistinctCtx_holds) a6NoChar2Lambda_holds hTD4

end I91T

end CFSG.LocalAnalysis.GLTheoremA
