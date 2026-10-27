module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockLiftQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.EngineOver
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def QuasisimpleModTwoNonab (A : Type*) [Group A] : Prop :=
  commutator (A ⧸ CFSG.pCore 2 A) = ⊤ ∧
    IsSimpleGroup ((A ⧸ CFSG.pCore 2 A) ⧸ Subgroup.center (A ⧸ CFSG.pCore 2 A)) ∧
    120 < Nat.card ((A ⧸ CFSG.pCore 2 A) ⧸ Subgroup.center (A ⧸ CFSG.pCore 2 A)) ∧
    (∀ z ∈ Subgroup.center (A ⧸ CFSG.pCore 2 A), Odd (orderOf z)) ∧
    ∃ Q : Subgroup (A ⧸ CFSG.pCore 2 A), IsPGroup 2 Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a

@[expose] def KFactChevGraphOrbit : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L R P : Subgroup Y), Open.IsQuasisimple ↥L →
    IsChevTwo (↥L ⧸ Subgroup.center ↥L) → R ≤ Subgroup.normalizer (L : Set Y) →
    IsPGroup 2 R → IsSylowTwoOf (R ⊓ L) L → IsMinOverBorel L (R ⊓ L) P →
    ¬ R ≤ Subgroup.normalizer (P : Set Y) →
      Group.IsSolvable ↥(pElementSubgroup 2 (conjClosure P R)) ∨
      (∃ C : Subgroup Y, C ≤ pElementSubgroup 2 (conjClosure P R) ∧
        pElementSubgroup 2 (conjClosure P R) ≤ Subgroup.normalizer (C : Set Y) ∧
        pElementSubgroup 2 (conjClosure P R) ≤ conjClosure C R ∧
        ∀ r ∈ R, r ∉ Subgroup.normalizer (P : Set Y) →
          ⁅C, B6.conjSub r C⁆ ≤ pCoreOf 2 (pElementSubgroup 2 (conjClosure P R))) ∨
      QuasisimpleModTwoNonab ↥(twoResidual (pElementSubgroup 2 (conjClosure P R)))

end CFSG.AGLEmbeddingD2.Tits.GN516
