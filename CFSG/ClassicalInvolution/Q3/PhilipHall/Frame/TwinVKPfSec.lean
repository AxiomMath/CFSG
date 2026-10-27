module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section Section

variable {H : Type} [Group H] [Finite H]

theorem datumTwinSet_quotient {n : ℕ} (hT : Thm1RTwinLiftSetBelow n)
    (hlt : Nat.card H < n) (N₀ : Subgroup H) [N₀.Normal] (hNodd : Odd (Nat.card N₀))
    (hO : classicalInvolutionOddCore (H ⧸ N₀) = ⊥) {J₀ : Subgroup H}
    (hΩ : HypOmegaGen (CoreAssembly.conjClass J₀)) (h2 : IsPGroup 2 J₀)
    (hA : AEmpty (CoreAssembly.conjClass J₀) J₀)
    (hq8 : Nonempty (↥J₀ ≃* QuaternionGroup 2)) (hgen : (⨆ g : H, conjSub g J₀) = ⊤) {t : H}
    (ht : IsUniqueInvolution J₀ t) (S : Sylow 2 ↥(J₀.map (QuotientGroup.mk' N₀)))
    (htw : HasTwin (J₀.map (QuotientGroup.mk' N₀))) :
    TightInO2 (QuotientGroup.mk' N₀ t) ∨ TwinE4 (H ⧸ N₀) ∨
      LongFundSet3 (J₀.map (QuotientGroup.mk' N₀)) (QuotientGroup.mk' N₀ t) := by
  have hmem : ∀ K ∈ CoreAssembly.conjClass J₀, IsPGroup 2 K := by
    rintro _ ⟨g, rfl⟩
    exact isPGroup_conjSub g h2
  have hJN : J₀ ⊓ N₀ = ⊥ :=
    OddQuot.inf_eq_bot_of_mem hmem hNodd (CoreAssembly.mem_conjClass_self J₀)
  have hfam : quotFamily (CoreAssembly.conjClass J₀) N₀ =
      CoreAssembly.conjClass (J₀.map (QuotientGroup.mk' N₀)) :=
    image_conjClass (N := N₀) J₀
  have hR2 : IsPGroup 2 (J₀.map (QuotientGroup.mk' N₀)) := h2.map _
  have htc : tightCore (J₀.map (QuotientGroup.mk' N₀)) = J₀.map (QuotientGroup.mk' N₀) :=
    tightCore_eq_self_of_isPGroup hR2
  have hq := OddQuot.hypOmegaGen_quotFamily hΩ hmem hNodd
  have hAall := aEmpty_forall_of_transitive hΩ.conjInvariant (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) hA
  have hAq := OddQuot.aEmpty_quotFamily hΩ hmem hNodd hAall (J₀.map (QuotientGroup.mk' N₀))
    (map_mem_quotFamily (CoreAssembly.mem_conjClass_self J₀))
  rw [hfam] at hq hAq
  have hut : IsUniqueInvolution (J₀.map (QuotientGroup.mk' N₀)) (QuotientGroup.mk' N₀ t) :=
    AscQuot.isUniqueInvolution_map_mk hJN ht
  obtain ⟨hd, hSq⟩ := q8TwinDatum_of_isPGroup hR2 S hut
    ⟨(AscQuot.quotRestrictEquiv hJN).symm.trans hq8.some⟩
  have hgen' : TightSelfGen (J₀.map (QuotientGroup.mk' N₀)) := by
    show (⨆ g : H ⧸ N₀, conjSub g (tightCore (J₀.map (QuotientGroup.mk' N₀)))) = ⊤
    rw [htc, eq_top_iff, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N₀),
      ← hgen, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [TwistQ.conjSub_map]
    exact le_iSup (fun g : H ⧸ N₀ => conjSub g (J₀.map (QuotientGroup.mk' N₀)))
      (QuotientGroup.mk' N₀ g)
  have hcard : Nat.card (H ⧸ N₀) < n :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)) hlt
  refine hT (H ⧸ N₀) hcard _ S _ hd hSq hgen' hO ?_ ?_ htw
  · rw [htc]; exact hq
  · rw [htc]; exact hAq

end Section

section Main

variable {G : Type} [Group G] [Finite G]

theorem sectionOutcomeSet_twin {n : ℕ} (hT : Thm1RTwinLiftSetBelow n)
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (h2 : ∀ K ∈ Ω, IsPGroup 2 K)
    {J : Subgroup G} (hJ : J ∈ Ω) (hq8 : Nonempty (↥J ≃* QuaternionGroup 2))
    (hA : AEmpty Ω J) {X : Subgroup G} (hJX : J ≤ X) (hXn : Nat.card X < n)
    (hgen : (⨆ x : X, conjSub (x : G) J) = X) {t : G} (ht : IsUniqueInvolution J t)
    (htw : ∃ K ∈ twinSet {L | ∃ x : X, conjSub (x : G) J = L} J, K ≠ J) :
    TightInO2 (secInv X ⟨t, hJX ht.mem⟩) ∨ TwinE4 (SecQuot X) ∨
      LongFundSet3 (secImage X J) (secInv X ⟨t, hJX ht.mem⟩) := by
  have hconj : ∀ g : ↥X, (conjSub g (J.subgroupOf X)).map X.subtype = conjSub (g : G) J := by
    intro g
    have hle : conjSub (g : G) J ≤ X := by
      have := conjSub_mono (n := (g : G)) hJX
      rwa [conjSub_eq_self_of_mem g.2] at this
    rw [conjSub_subgroupOf]
    exact Subgroup.map_subgroupOf_eq_of_le hle
  have hgenX : (⨆ g : ↥X, conjSub g (J.subgroupOf X)) = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [hconj]
    exact hgen
  have hJ2 : IsPGroup 2 (J.subgroupOf X) := (h2 J hJ).comap_subtype
  have hq8X : Nonempty (↥(J.subgroupOf X) ≃* QuaternionGroup 2) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hJX).trans hq8.some⟩
  have htX : IsUniqueInvolution (J.subgroupOf X) (⟨t, hJX ht.mem⟩ : X) :=
    isUniqueInvolution_subgroupOf ht hJX
  exact datumTwinSet_quotient hT hXn (classicalInvolutionOddCore ↥X)
    (CFSG.ComponentClassification.OddCore.odd_card ↥X)
    (CFSG.ComponentClassification.OddCore.quotient_corefree ↥X)
    (hypOmegaGen_conjClass_section hΩ hJ hJX) hJ2 (aEmpty_conjClass_section hΩ h2 hJ hA hJX)
    hq8X hgenX htX (Classical.choice inferInstance)
    ((hasTwin_secImage_iff hΩ h2 hJ hJX).mpr htw)

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
