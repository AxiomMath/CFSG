module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def K14SporU : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (fixSubgroup β) J →
      (catalogIs (PSimple 3 J) S9.isU5two ∨ catalogIs (PSimple 3 J) S9.isSp6two) →
      s = TauCeti.SporadicName.Co2

@[expose] def K14NotChevOdd : Prop :=
  ∀ (S : Type) [Group S], (catalogIs S S9.isU5two ∨ catalogIs S S9.isSp6two) →
    ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ IsChevSimple r S

@[expose] def K14NotAlt : Prop :=
  ∀ (S : Type) [Group S] (m : ℕ), 5 ≤ m →
    (catalogIs S S9.isU5two ∨ catalogIs S S9.isSp6two) → ¬ Nonempty (S ≃* alternatingGroup (Fin m))

end CFSG.LocalAnalysis.GLTheoremA

end
