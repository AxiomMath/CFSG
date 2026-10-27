module

public import CFSG.LieType.SeitzGeneration.RegimesExc

public section

open CFSG.Open CFSG.LieType.SeitzGeneration

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

@[expose] def SeitzExcAnisotropicG2ThreePlus : Prop :=
  SeitzPlanes fun d p E =>
    (InnerPlane d p E ∧ ¬ IsClassicalIndex d.1 ∧ RankLE2 p (Cat d) ∧
      ¬ NormalizesRSubgroup d E) ∧
    p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .G2 q ∧ 3 ∣ q.card + 1

@[expose] def G2ThreeCatBasic : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), 3 ∣ q.card + 1 →
    Finite (Cat ⟨TauCeti.LieTypeIndex.G2 q, hv⟩) ∧
      Subgroup.center (Cat ⟨TauCeti.LieTypeIndex.G2 q, hv⟩) = ⊥

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
