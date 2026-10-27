module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneSporPlaneSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneSporPlaneHeJ4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open

@[expose] def SporPlaneAt (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ A : Subgroup K, IsElemAbelian p A → Nat.card A = p ^ 2 → GLBCore p 1 A = ⊤

theorem kFactThreeOneSporPlane_of_pairs
    (hM24 : SporPlaneAt .M24 3) (hJ4 : SporPlaneAt .J4 3) (hHe : SporPlaneAt .He 3)
    (hRu : SporPlaneAt .Ru 3) (hTh : SporPlaneAt .Th 5) (hM : SporPlaneAt .M 13) :
    KFactThreeOneSporPlane := by
  rintro s p (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact hM24
  · exact fun K _ _ hK A hA hc => glbCore_one_eq_top_J2 K hK A hA hc
  · exact hJ4
  · exact hHe
  · exact hRu
  · exact fun K _ _ hK A hA hc => glbCore_one_eq_top_Co2 K hK A hA hc
  · exact fun K _ _ hK A hA hc => glbCore_one_eq_top_Co3 K hK A hA hc
  · exact hTh
  · exact hM

theorem sporPlaneAt_M24 :
    SporPlaneAt .M24 3 :=
  fun K _ _ hK A hA hc => glbCore_one_eq_top_M24 K hK A hA hc

theorem sporPlaneAt_Ru :
    SporPlaneAt .Ru 3 :=
  fun K _ _ hK A hA hc => glbCore_one_eq_top_Ru K hK A hA hc

theorem sporPlaneAt_He :
    SporPlaneAt .He 3 :=
  fun K _ _ hK A hA hc => glbCore_one_eq_top_He K hK A hA hc

theorem sporPlaneAt_J4 :
    SporPlaneAt .J4 3 :=
  fun K _ _ hK A hA hc => glbCore_one_eq_top_J4 K hK A hA hc

theorem kFactThreeOneSporPlane_of_two
    (hTh : SporPlaneAt .Th 5) (hM : SporPlaneAt .M 13) : KFactThreeOneSporPlane :=
  kFactThreeOneSporPlane_of_pairs sporPlaneAt_M24 sporPlaneAt_J4 sporPlaneAt_He sporPlaneAt_Ru
    hTh hM

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
