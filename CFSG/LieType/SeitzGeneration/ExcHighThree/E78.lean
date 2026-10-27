module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Pilot
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Native
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThreeProved

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

section E78

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.TauCetiBridge
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley TauCeti


theorem allParabolic_of_lang {τ : Tag} (htor : LangToralOrParabolic τ) (hNR : LangPlaneKillsRoot τ)
    (hK : LangPlaneKilled τ) (K : Type) [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K)
    (A : Subgroup (adjointGroup τ K)) (hA : ∀ x ∈ A, x ^ 3 = 1) (hcard : Nat.card A = 3 ^ 2) :
    NormalizesRNative τ K A := by
  rcases htor K hK3 A hA hcard with ⟨⟨D⟩⟩ | h
  · obtain ⟨α, hα, hk⟩ := hK K hK3 A hA hcard D
    exact normalizesRNative_of_unip (hNR K A D α hα hk)
  · exact h

theorem seitzExcHighThreeE7_of_pieces
    (hNR : LangPlaneKillsRoot .E7) (hK : LangPlaneKilled .E7) :
    SeitzExcHighForAt IsE7Index PrimeRange.three :=
  seitzExcHighThree_of_allParabolic Even.chevalleyBridgesAll.e7 (fun _ ⟨q, hq⟩ => ⟨q, hq⟩)
    LieTypeIndex.characteristic_E7
    (fun K _ _ hK3 A hA hcard => allParabolic_of_lang
      (langToralOrParabolic_of_langToralPlane langToralPlane_E7_three) hNR hK K hK3 A hA hcard)

theorem seitzExcHighThreeE8_of_pieces
    (hNR : LangPlaneKillsRoot .E8) (hK : LangPlaneKilled .E8) :
    SeitzExcHighForAt IsE8Index PrimeRange.three :=
  seitzExcHighThree_of_allParabolic Even.chevalleyBridgesAll.e8 (fun _ ⟨q, hq⟩ => ⟨q, hq⟩)
    LieTypeIndex.characteristic_E8
    (fun K _ _ hK3 A hA hcard => allParabolic_of_lang
      (langToralOrParabolic_of_langToralPlane langToralPlane_E8_three) hNR hK K hK3 A hA hcard)

end E78

end CFSG.LieType.SeitzGeneration.ExcHighThree
