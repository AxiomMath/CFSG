module

public import CFSG.HardMathSupport.Solomon.Coordinator.SporCoverRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowSuz
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowFi24
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowJ3
public import CFSG.Sporadic.Presentation.McLExact
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.Sporadic.Bridge.Fi22Surj
public import CFSG.Sporadic.Bridge.Fi24Surj
public import CFSG.Sporadic.Bridge.J3Surj

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.AGLEmbedding

theorem sporCover_McL_pRank_ge_four
    (L : Type) [Group L] [Finite L] (_hperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (he : Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have b : NativeSporadic.Carrier .McL ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group := b0
  obtain ⟨e⟩ := he
  exact four_le_pRank_of_moduleDatum hZ (e.trans b.symm) (moduleDatum_McL_three)

theorem sporCover_Suz_pRank_ge_four
    (L : Type) [Group L] [Finite L] (_hperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (he : Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Suz).Group)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have b : NativeSporadic.Carrier .Suz ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Suz).Group := b0
  obtain ⟨e⟩ := he
  exact four_le_pRank_of_moduleDatum hZ (e.trans b.symm) (moduleDatum_Suz_three)

theorem sporCover_Fi22_pRank_ge_four
    (L : Type) [Group L] [Finite L] (_hperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (he : Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have b : NativeSporadic.Carrier .Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := b0
  obtain ⟨e⟩ := he
  exact four_le_pRank_of_moduleDatum hZ (e.trans b.symm) (moduleDatum_Fi22_three)

theorem sporCover_Fi24Prime_pRank_ge_four
    (L : Type) [Group L] [Finite L] (_hperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (he : Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi24Prime).Group)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have b : NativeSporadic.Carrier .Fi24Prime ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi24Prime).Group := b0
  obtain ⟨e⟩ := he
  exact four_le_pRank_of_moduleDatum hZ (e.trans b.symm) (moduleDatum_Fi24_three)

theorem sporCover_J3_pRank_ge_four
    (L : Type) [Group L] [Finite L] (_hperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (he : Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have b : NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group := b0
  obtain ⟨e⟩ := he
  exact four_le_pRank_of_moduleDatum hZ (e.trans b.symm) (moduleDatum_J3_three)

end CFSG.HardMathSupport.Solomon.Coordinator
