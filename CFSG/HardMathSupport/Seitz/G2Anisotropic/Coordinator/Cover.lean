module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyReduction
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.PlaneFromCentralizers

public section

open CFSG.Open CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

@[expose] def SeitzExcAnisotropicNotG2ThreePlus : Prop :=
  SeitzPlanes fun d p E =>
    (InnerPlane d p E ∧ ¬ IsClassicalIndex d.1 ∧ RankLE2 p (Cat d) ∧
      ¬ NormalizesRSubgroup d E) ∧
    ¬ (p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .G2 q ∧ 3 ∣ q.card + 1)

theorem seitzExcAnisotropic_of_cover (hF : SeitzExcAnisotropicG2ThreePlus)
    (hN : SeitzExcAnisotropicNotG2ThreePlus) : SeitzExcAnisotropic :=
  SeitzPlanes.of_cover (fun d p _ _ E hs => by
    by_cases h : p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .G2 q ∧ 3 ∣ q.card + 1
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr ⟨hs, h⟩) hF hN

end CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
