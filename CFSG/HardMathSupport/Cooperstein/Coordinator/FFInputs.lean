module

public import CFSG.Quasithin.Background.Module
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding

@[expose] def FFHyp {V : Type} [CommGroup V] [Finite V] (H L : Subgroup (MulAut V)) : Prop :=
  L = quasithinGenFitting H ∧ CFSG.IsQuasisimple ↥L ∧ CFSG.pCore 2 ↥H = ⊥ ∧
    IsCatalogGroup (↥L ⧸ Subgroup.center ↥L)

@[expose] def FFConclusion (Y : Type) [Group Y] : Prop :=
  IsClassicalTwoOrG2 Y ∨ ∃ m : ℕ, 5 ≤ m ∧ Nonempty (Y ≃* alternatingGroup (Fin m))

@[expose] def FFModuleTheorem : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H L : Subgroup (MulAut V), FFHyp H L → IsFFModule H →
      FFConclusion (↥L ⧸ Subgroup.center ↥L)

end CFSG.HardMathSupport.Cooperstein.Coordinator
