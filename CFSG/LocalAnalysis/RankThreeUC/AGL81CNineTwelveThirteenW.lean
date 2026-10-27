module

import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

namespace NineSetting

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

private theorem relPPrimeCore_eq_map' {p : ℕ} (hp : p.Prime) (C : Subgroup G) :
    CFSG.Open.relPPrimeCore p C =
      (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥C) p).map C.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNC, hNn, hNc⟩ := hN
    have h1 : N.subgroupOf C ≤
        CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥C) p := by
      refine le_sSup ⟨hNn, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
      exact hNc
    calc N = (N.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hNC).symm
      _ ≤ _ := Subgroup.map_mono h1
  · refine le_sSup ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · show (Subgroup.comap C.subtype
          ((CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥C) p).map
            C.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      infer_instance
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card

end NineSetting

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
