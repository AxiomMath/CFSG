module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

noncomputable abbrev excRatComp {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)) :
    Subgroup (ModGL τ L) :=
  rationalComponent S.ρ S.Γ (rootCharHom a) i

@[expose] def ExcShape (r nc : ℕ) : Prop :=
  (1 ≤ r ∧ r ≤ 8 ∧ nc = r * (r + 1)) ∨ (2 ≤ r ∧ r ≤ 8 ∧ nc = 2 * (r * r)) ∨
    (4 ≤ r ∧ r ≤ 8 ∧ nc = 2 * (r * (r - 1))) ∨ (r = 6 ∧ nc = 72) ∨ (r = 7 ∧ nc = 126) ∨
    (r = 8 ∧ nc = 240) ∨ (r = 4 ∧ nc = 48)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
