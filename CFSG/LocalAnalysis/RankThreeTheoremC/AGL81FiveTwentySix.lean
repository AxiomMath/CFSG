module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySixType
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.GNSettingM
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36H
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC.S15
  CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

namespace FiveTwentySix

theorem ne_top_of_charTwo (hS : Setting G) {X : Subgroup G} (hc : CharTwo X) : X ≠ ⊤ := by
  intro hX
  subst hX
  haveI : IsSimpleGroup G := hS.simple
  have hO : CFSG.Open.pCoreOf 2 (⊤ : Subgroup G) = ⊥ := by
    rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore,
      CFSG.CGT.PushingUp.pCore_eq_bot_of_isSimpleGroup hS.nonab]
  unfold CharTwo at hc
  rw [hO] at hc
  have hcent : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
    rw [hx]
    exact Subgroup.one_mem _
  have hle : (⊤ : Subgroup G) ≤ ⊥ := by
    have h1 : (⊤ : Subgroup G) ≤
        ⊤ ⊓ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
      rw [hcent, inf_top_eq]
    exact h1.trans hc
  have htop : (⊤ : Subgroup G) = ⊥ := le_antisymm hle bot_le
  obtain ⟨a, b, hab⟩ := hS.nonab
  have ha : a = 1 := by
    have : a ∈ (⊥ : Subgroup G) := htop ▸ Subgroup.mem_top a
    simpa using this
  have hb : b = 1 := by
    have : b ∈ (⊥ : Subgroup G) := htop ▸ Subgroup.mem_top b
    simpa using this
  exact hab (by simp [ha, hb])

theorem isC2_subgroupOf {X L : Subgroup G} (hL : IsTwoPrimeComponent X L) :
    IsC2 (L.subgroupOf X) := by
  have hperf : ⁅L.subgroupOf X, L.subgroupOf X⁆ = L.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hL.le, hL.perfect]
  refine ⟨?_, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.of_mathlib (CFSG.Open.IsSubnormal.subgroupOf hL.subnormal)
  · change CFSG.ComponentClassification.SolMax.oddGen (L.subgroupOf X) = L.subgroupOf X
    exact CFSG.ComponentClassification.SolMax.oddGen_eq_of_perfect hperf
  · exact hL.component

theorem map_threeNormalizerJoin_le {X T L : Subgroup G} (hTX : T ≤ X) (hLX : L ≤ X) :
    (threeNormalizerJoin (T.subgroupOf X) (L.subgroupOf X)).map X.subtype ≤
      threeNormalizerJoin T L := by
  simp only [threeNormalizerJoin, Subgroup.map_iSup]
  refine iSup_le fun B' => iSup_le fun hB'T => iSup_le fun hB' => iSup_le fun hB'c =>
    iSup_le fun h3 => ?_
  obtain ⟨hBT, hBchar⟩ := map_subtype_characteristic hTX hB'T hB'c
  have hBne : B'.map X.subtype ≠ ⊥ := fun h =>
    hB' ((Subgroup.map_eq_bot_iff_of_injective B' X.subtype_injective).mp h)
  have hnorm : (Subgroup.normalizer (B' : Set ↥X)).map X.subtype ≤
      Subgroup.normalizer (B'.map X.subtype : Set G) :=
    Subgroup.le_normalizer_map (H := B') X.subtype
  have hleImage : (L.subgroupOf X ⊓ Subgroup.normalizer (B' : Set ↥X)).map X.subtype ≤
      L ⊓ Subgroup.normalizer (B'.map X.subtype : Set G) := by
    rw [Subgroup.map_inf_eq _ _ _ X.subtype_injective]
    refine le_inf ?_ ?_
    · exact inf_le_left.trans (le_of_eq (Subgroup.map_subgroupOf_eq_of_le hLX))
    · exact inf_le_right.trans hnorm
  have hcard : Nat.card ↥(L.subgroupOf X ⊓ Subgroup.normalizer (B' : Set ↥X)) ∣
      Nat.card ↥(L ⊓ Subgroup.normalizer (B'.map X.subtype : Set G)) := by
    rw [← Subgroup.card_map_of_injective (K := L.subgroupOf X ⊓
      Subgroup.normalizer (B' : Set ↥X)) (f := X.subtype) X.subtype_injective]
    exact Subgroup.card_dvd_of_le hleImage
  exact hleImage.trans (inf_normalizer_le_threeNormalizerJoin (T := T) (L := L)
    (B := B'.map X.subtype) hBT hBne hBchar (h3.trans hcard))

end FiveTwentySix

theorem agl81FiveTwentySix_of
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem) (h516 : AGL81I516)
    (hG : KFactChevGenThree) (hAF : GNAltFacts) (hAlt : AGL81FiveTwentySixAlt) :
    AGL81FiveTwentySix G := by
  intro hS X T L hT hc hnoX hL h3
  have hXtop : X ≠ ⊤ := FiveTwentySix.ne_top_of_charTwo hS hc
  have hGN : GNSetting ↥X (T.subgroupOf X) :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.gnSetting_of_subgroup hS.kProper hXtop hc hT hnoX
  have h3' : 3 ∣ Nat.card (L.subgroupOf X) := by
    have hcard : Nat.card (L.subgroupOf X) = Nat.card L := by
      rw [← Subgroup.card_subtype X (L.subgroupOf X),
        Subgroup.map_subgroupOf_eq_of_le hL.le]
    rw [hcard]
    exact h3
  have hjoin : L.subgroupOf X ≤ threeNormalizerJoin (T.subgroupOf X) (L.subgroupOf X) :=
    FiveTwentySix.le_threeNormalizerJoin hFF h516 hG hAF hAlt hGN
      (FiveTwentySix.isC2_subgroupOf hL) h3'
  have hmap : L ≤ (threeNormalizerJoin (T.subgroupOf X) (L.subgroupOf X)).map X.subtype :=
    calc L = (L.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hL.le).symm
      _ ≤ (threeNormalizerJoin (T.subgroupOf X) (L.subgroupOf X)).map X.subtype :=
          Subgroup.map_mono hjoin
  show L ≤ threeNormalizerJoin T L
  exact hmap.trans (FiveTwentySix.map_threeNormalizerJoin_le hT.1 hL.le)

end CFSG.LocalAnalysis.RankThreeTheoremC
