module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointOddCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthInvolutions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem generatedPairGrowth_normalizer_le_characteristic_image
    (E : Subgroup G) (D : Subgroup E) (hD : D.Characteristic) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (D.map E.subtype : Set G) := by
  have hconj : ∀ {g : G}, g ∈ Subgroup.normalizer (E : Set G) →
      ∀ {x : G}, x ∈ D.map E.subtype → g * x * g⁻¹ ∈ D.map E.subtype := by
    intro g hg x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    let n : Subgroup.normalizer (E : Set G) := ⟨g, hg⟩
    let f := Subgroup.normalizerMonoidHom E n
    have hmem : f a ∈ D := by
      change a ∈ D.comap f.toMonoidHom
      rw [hD.fixed f]
      exact ha
    exact Subgroup.mem_map.mpr ⟨f a, hmem,
      Subgroup.normalizerMonoidHom_apply_apply_coe E n a⟩
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  refine ⟨hconj hg, fun hx => ?_⟩
  have hi := hconj ((Subgroup.normalizer (E : Set G)).inv_mem hg) hx
  simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hi

theorem generatedPairGrowth_triple_odd_core_eq_intersection [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    (CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype =
      pairOddCore H beta ⊓ triplePointStabilizer H z beta := by
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let J := pairOddCore H beta
  have hEB : E ≤ B := inf_le_left
  have hBN : B ≤ Subgroup.normalizer (J : Set G) := by
    change B ≤ Subgroup.normalizer ((CFSG.oddCore B).map B.subtype : Set G)
    exact Subgroup.le_normalizer.trans
      (generatedPairGrowth_normalizer_le_characteristic_image B (CFSG.oddCore B)
        (CFSG.ComponentClassification.OddCore.characteristic B))
  have hnormal : (J.subgroupOf E).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hEB.trans hBN)
  have hodd : Odd (Nat.card (J.subgroupOf E)) := by
    have hc : Nat.card (J.subgroupOf E) = Nat.card (J ⊓ E : Subgroup G) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype]
    rw [hc]
    exact (pairOddCore_odd H beta).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  apply le_antisymm
  · exact le_inf (triple_odd_core_le_pair_odd_core h S hzS hzcenter hbeta ht)
      (Subgroup.map_subtype_le _)
  · rw [← Subgroup.subgroupOf_map_subtype]
    exact Subgroup.map_mono (CFSG.ComponentClassification.OddCore.maximal E _ hnormal hodd)

theorem generatedPairGrowth_flip_normalizes_pair_odd_core [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    t ∈ Subgroup.normalizer (pairOddCore H beta : Set G) := by
  have hcore := pair_group_oddCore_eq h.distinguished_order hbeta ht
  have htK : t ∈ pairFlipGroup H beta t := by
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hnorm := (generatedPairGrowth_normalizer_le_characteristic_image
    (pairFlipGroup H beta t) (CFSG.oddCore (pairFlipGroup H beta t))
    (CFSG.ComponentClassification.OddCore.characteristic _))
      (Subgroup.le_normalizer htK)
  rwa [hcore] at hnorm

theorem generatedPairGrowth_normalizer_generation [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hgen : (Subgroup.zpowers z ⊔ Subgroup.zpowers t) ⊔ pairOddCore H beta = ⊤) :
    Subgroup.normalizer (pairOddCore H beta : Set G) ⊔ Subgroup.zpowers z = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact sup_le
    (sup_le le_sup_right ((Subgroup.zpowers_le.mpr
      (generatedPairGrowth_flip_normalizes_pair_odd_core h hbeta ht)).trans le_sup_left))
    (Subgroup.le_normalizer.trans le_sup_left)

theorem generatedPairGrowth_pair_odd_core_ne_bot [Finite G] [IsSimpleGroup G]
    (hnonabelian : ∃ a b : G, a * b ≠ b * a)
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hgen : (Subgroup.zpowers z ⊔ Subgroup.zpowers t) ⊔ pairOddCore H beta = ⊤) :
    pairOddCore H beta ≠ ⊥ := by
  intro hJ
  have hzt : Subgroup.zpowers z ⊔ Subgroup.zpowers t = ⊤ := by
    simpa only [hJ, sup_bot_eq] using hgen
  exact generatedPairGrowth_not_two_involutions_generate h.distinguished_order
    (order_two_of_mem_pointClass h.distinguished_order ht.1) hnonabelian hzt

theorem generatedPairGrowth_pair_odd_core_lt_top [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) : pairOddCore H beta < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro heq
  have hodd : Odd (Nat.card G) := by
    simpa only [heq, Subgroup.card_top] using pairOddCore_odd H beta
  have hd : 2 ∣ Nat.card G := h.distinguished_order ▸ orderOf_dvd_natCard z
  have hzero := Nat.mod_eq_zero_of_dvd hd
  have hone := Nat.odd_iff.mp hodd
  omega

theorem generatedPairGrowth_normal_subgroup_in_pair_odd_core_eq_bot
    [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) (N : Subgroup G) [N.Normal]
    (hNJ : N ≤ pairOddCore H beta) : N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
  · exact hN
  · exact False.elim ((generatedPairGrowth_pair_odd_core_lt_top h beta).ne_top
      (top_le_iff.mp (hN ▸ hNJ)))

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
