module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Facts2
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def I1432LieOut : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), d.1.characteristic = 3 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ α : MulAut S, α ^ 3 = 1 → α ∉ inner S →
    ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup α) J →
      (catalogIs (PSimple 3 J) (S8.isD4of 3) → catalogIs S (S8.isD4of 27)) ∧
      (catalogIs (PSimple 3 J) (S8.isG2of 3) →
        catalogIs S (S8.isG2of 27) ∨ catalogIs S (S8.isD4of 3) ∨ catalogIs S (isTD4of 3) ∨
          catalogIs S (S8.isD4of 27))

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
