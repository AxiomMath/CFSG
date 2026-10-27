module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataTrans
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataWords

public section

namespace CFSG.EvenSporadicStandard.M24Std

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

@[expose] def qdGens : List S24 := [m24Cj wordQdG1, m24Cj wordQdG2]

@[expose] def qdA1 : S24 := m24E1l.getD 1 1

@[expose] def qdA2 : S24 := m24E1l.getD 22 1

@[expose] def qdStab1 : List S24 := [m24Cj wordQdS11, m24Cj wordQdS12, m24Cj wordQdS13]

@[expose] def qdStab2 : List S24 := [m24Cj wordQdS21, m24Cj wordQdS22, m24Cj wordQdS23]

@[expose] def qdDepth : ℕ := 12

@[expose] def QdBase (a : S24) (st : List S24) : Prop :=
  a ∈ m24E1l ∧ (∀ g ∈ st, QdNormChk g ∧ g * a * g⁻¹ = a) ∧
    ∀ t ∈ m24E1l, (∀ g ∈ st, g * t * g⁻¹ = t) → t = 1 ∨ t = a

instance (a : S24) (st : List S24) : Decidable (QdBase a st) := by
  unfold QdBase
  infer_instance

@[expose] def QdFixData : Prop :=
  (∀ g ∈ qdGens, QdNormChk g) ∧
    (∀ s ∈ m24E1l, s ≠ 1 →
      s ∈ qdReach qdGens qdA1 qdDepth ∨ s ∈ qdReach qdGens qdA2 qdDepth) ∧
    QdBase qdA1 qdStab1 ∧ QdBase qdA2 qdStab2

instance : Decidable QdFixData := by
  unfold QdFixData
  infer_instance

@[expose] def qdX45 : List S24 := [21, 14, 6, 16, 44, 7].map fun k => m24E1l.getD k 1

@[expose] def QdGen45Data : Prop :=
  (∀ g ∈ qdGens, QdNormChk g) ∧ qdA1 ≠ 1 ∧ qdA1 ∈ m24E1l ∧
    (∀ x ∈ qdX45, x ∈ m24E1l ∧ x ∈ qdReach qdGens qdA1 qdDepth ∧
      qdA1 * x ∈ qdReach qdGens qdA1 qdDepth) ∧
    ∀ s ∈ m24E1l, s ∈ m24Lst qdX45

instance : Decidable QdGen45Data := by
  unfold QdGen45Data
  infer_instance

end CFSG.EvenSporadicStandard.M24Std
