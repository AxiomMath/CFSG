module

public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)

@[expose] def I1431LieList (i : TauCeti.CFSGIndex) : Prop :=
  S9.isSp8two i ∨ S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i ∨ S9.isU4eight i

@[expose] def I1431SporS : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (fixSubgroup β) J → catalogIs (PSimple 3 J) S9.isU4two → s = TauCeti.SporadicName.Co2

@[expose] def I1431ChevTwoS : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ → RkY Y →
    catalogIs (Y ⧸ Subgroup.center Y) (onLie fun d => d.characteristic = 2) →
    ∀ ξ : MulAut Y, ξ ^ 3 = 1 → ξ ≠ 1 → ∀ J : Subgroup Y,
      GLAPComponent 3 (fixSubgroup ξ) J → catalogIs (PSimple 3 J) S9.isU4two →
      catalogIs (Y ⧸ Subgroup.center Y) I1431LieList

theorem i1431List_iff (i : TauCeti.CFSGIndex) :
    S9.i1431List i ↔ i = .sporadic .Co2 ∨ I1431LieList i :=
  Iff.rfl

end CFSG.LocalAnalysis.GLTheoremA

end
