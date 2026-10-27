module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.StandardType (GGTorusLift)

structure U3CoreHyp (S : Type) [Group S] (labL : GLALabel) (β : MulAut S) (n : ℕ)
    (J : Subgroup S) : Prop where
  center_eq_bot : Subgroup.center S = ⊥
  innDiagKind : InnDiagKind S labL β
  split : GLASplit 3 labL
  pow_three : β ^ 3 = 1
  ne_one : β ≠ 1
  odd : Odd n
  three_le : 3 ≤ n
  dvd : labL.n ∣ n
  isComponentOf : IsComponentOf J (fixSubgroup β)
  hasLabel : HasLabel ↥J (· = ⟨.twA, 2, n⟩)
  rank_le : ∀ r : ℕ, GGTorusLift 3 r S → r ≤ 3

@[expose] def U3CoreOn (Fam : GLALabel → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (labL : GLALabel) (β : MulAut S) (n : ℕ) (J : Subgroup S),
    Fam labL → U3CoreHyp S labL β n J → 3 ∣ Nat.card ↥(Subgroup.center ↥J)

@[expose] def U3CoreS : Prop := U3CoreOn fun _ => True

theorem u3CoreS_of_families (hL : U3CoreOn FamLin) (hU : U3CoreOn FamUni)
    (hSp : U3CoreOn FamSymp) (hO : U3CoreOn FamOrth) (hE : U3CoreOn FamExc) : U3CoreS := by
  intro S _ _ labL β n J _ h
  rcases fam_cover labL with hF | hF | hF | hF | hF
  · exact hL S labL β n J hF h
  · exact hU S labL β n J hF h
  · exact hSp S labL β n J hF h
  · exact hO S labL β n J hF h
  · exact hE S labL β n J hF h

end CFSG.LocalAnalysis.GLTheoremA.CanonU3
