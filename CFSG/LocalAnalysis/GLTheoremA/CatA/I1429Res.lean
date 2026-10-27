module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def isSp4_27 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .B 2 q => q.card = 27 | _ => False

@[expose] def I1429SubfieldOut : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q → IsChevSimple 3 (Q ⧸ Subgroup.center Q) →
    ∀ β : MulAut Q, β ^ 3 = 1 → β ∉ (MulAut.conj : Q →* MulAut Q).range →
      ∀ I : Subgroup Q, GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) I →
        catalogIs (PSimple 3 I) S9.isU4two → catalogIs (Q ⧸ Subgroup.center Q) isSp4_27

@[expose] def I1429InnerRest : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q → IsChevSimple 3 (Q ⧸ Subgroup.center Q) →
    ¬ (Subgroup.center Q = ⊥ ∧ catalogIs Q (onLie fun d => d.characteristic = 3)) →
    ∀ q : Q, (MulAut.conj q) ^ 3 = 1 → MulAut.conj q ≠ 1 →
      ∀ I : Subgroup Q,
        ¬ GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj q)) I

@[expose] def I1429TwoRankSp4 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    catalogIs (Q ⧸ Subgroup.center Q) isSp4_27 → 6 ≤ GLATwoLocalRank 3 Q

@[expose] def I1429Residual : Prop :=
  I1429SubfieldOut ∧ I1429InnerRest ∧ I1429TwoRankSp4

end CFSG.LocalAnalysis.GLTheoremA

end
