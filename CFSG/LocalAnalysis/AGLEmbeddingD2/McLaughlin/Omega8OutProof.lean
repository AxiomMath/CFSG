module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8Cited
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8Sylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Multiplier
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO8pCent
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIII
public import CFSG.RankThree.PartOne.KP.SporadicDefs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem nonempty_mulEquiv_omegaT_of_isOmegaEightPlus {Y : Type}
    [Group Y] (h : IsOmegaEightPlus Y) : Nonempty (Y ≃* CFSG.EvenSmallLie.OmegaEight.omegaT) := by
  obtain ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩ := h
  obtain ⟨f⟩ := CFSG.AGLEmbedding.O8pCent.nonempty_mulEquiv_omegaT_catalog d q hq hd
  exact ⟨e.trans f⟩

theorem kFactOmega8Out_proved :
    KFactOmega8Out := by
  refine ⟨fun X _ _ Lb hΩ hLn => ?_, fun X _ _ hq hΩ => ?_⟩
  · obtain ⟨e⟩ := nonempty_mulEquiv_omegaT_of_isOmegaEightPlus hΩ
    have h := CFSG.AGLEmbedding.relIndex_sup_centralizer_dvd_card_outer (L := Lb) (U := ⊤)
      (le_normalizer_of_normal (hLn := hLn) ⊤)
    rwa [CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv e,
      CFSG.EvenSmallLie.OmegaEight.card_outer_omegaT, top_inf_eq,
      Subgroup.relIndex_top_right] at h
  · obtain ⟨e⟩ := nonempty_mulEquiv_omegaT_of_isOmegaEightPlus hΩ
    have h := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier ⟨hq.1⟩ e
    obtain ⟨eM⟩ := CFSG.EvenSmallLie.OmegaEight.Cover.nonempty_griessHopfMultiplier_mulEquiv
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]
    rw [Nat.card_congr eM.toEquiv, Nat.card_prod, h2] at h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card (Subgroup.center X) ∣ 2 ^ 2 by simpa using h)
    exact IsPGroup.of_card hk

end CFSG.AGLEmbeddingD2.McLaughlin
