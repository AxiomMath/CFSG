module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def I137ChevClosureComp : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → CFSG.Open.IsKGroup S → (IsChevSimple p S ∨ catalogIs S (k2 p)) →
    ∀ α : MulAut S, α ^ p = 1 → ∀ I : Subgroup S,
      GLAPComponent p (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I →
      catalogIs (PSimple p I) (S9.isList93 p) → IsChevSimple 2 S

end CFSG.LocalAnalysis.GLTheoremA
