module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldCore

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

@[expose] def L34FieldSignalizerVanishingMirror : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (P : Subgroup G),
    L34FieldNormalSetting G t P → FooteLit.GSMirrorMaximal P →
    ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) →
      Open.IsElemAbelian 2 E → 8 ≤ Nat.card E → GrSLit.wGroup E = ⊥

end CFSG.ComponentClassification.GrSLit.L34Sec5S
