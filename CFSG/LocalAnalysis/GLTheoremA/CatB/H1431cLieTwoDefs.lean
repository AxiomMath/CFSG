module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

@[expose] def LieSTwoAt (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ → RkY Y →
    ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → d.1.characteristic = 2 →
      KD264Lie.fieldSize d.1 = 2 →
      Nonempty (Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut (Y ⧸ Subgroup.center Y), α ∈ innAutDerived (Y ⧸ Subgroup.center Y) →
        α ^ 3 = 1 → α ≠ 1 →
        (CompOfType (Y ⧸ Subgroup.center Y) α S9.isSp6two →
          S8.L84.isSp82 (.lie d) ∨ isF4two (.lie d)) ∧
        ¬ CompOfType (Y ⧸ Subgroup.center Y) α S8.L84.isSp48

theorem lieSTwo_of_at (h : LieSTwoAt fun _ => True) : LieSTwo :=
  fun Y _ _ hY hcore hRk d hc hf he α hα h3 h1 =>
    h Y hY hcore hRk d trivial hc hf he α hα h3 h1

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
