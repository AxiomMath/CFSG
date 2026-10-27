module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

@[expose] def U42Pumpup (S : Type) [Group S] (α : MulAut S) : Prop :=
  α ^ 3 = 1 ∧ α ≠ 1 ∧ ∃ J : Subgroup S, GLAPComponent 3 (fixSubgroup α) J ∧
    catalogIs (PSimple 3 J) S9.isU4two

@[expose] def U42InnField : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∈ innAutDerived S → U42Pumpup S α → KD264Lie.fieldSize d.1 = 2

@[expose] def U42Outer : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∉ innAutDerived S → U42Pumpup S α → S9.isU4eight (.lie d)

@[expose] def U42FieldTwoAt (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ → RkY Y →
    ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → d.1.characteristic = 2 →
      KD264Lie.fieldSize d.1 = 2 →
      Nonempty (Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut (Y ⧸ Subgroup.center Y), α ∈ innAutDerived (Y ⧸ Subgroup.center Y) →
        U42Pumpup (Y ⧸ Subgroup.center Y) α → I1431LieList (.lie d)

@[expose] def U42FieldTwo : Prop :=
  U42FieldTwoAt fun _ => True

@[expose] def U42Classical : TauCeti.LieTypeIndex → Prop
  | .A _ _ | .twistedA _ _ | .B _ _ | .C _ _ | .D _ _ | .twistedD _ _ => True
  | _ => False

@[expose] def U42NonClassical (d : TauCeti.LieTypeIndex) : Prop :=
  ¬ U42Classical d

theorem u42FieldTwo_of_parts (hC : U42FieldTwoAt U42Classical)
    (hN : U42FieldTwoAt U42NonClassical) : U42FieldTwo := by
  intro Y _ _ hY hcore hRk d _ hc hf he α hα hP
  by_cases hd : U42Classical d.1
  · exact hC Y hY hcore hRk d hd hc hf he α hα hP
  · exact hN Y hY hcore hRk d hd hc hf he α hα hP

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
