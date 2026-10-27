module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.GzCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma image_invSet_eq {G : Type} [Group G] {z : G} (hz2 : orderOf z = 2)
    {Q : Subgroup ↥(Gx z)} [Q.Normal] (hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) Q)
    (hQz : Qz z = Q.map (Gx z).subtype) :
    (Gx z).subtype '' {q : ↥(Gx z) | q ∈ Q ∧ q ^ 2 = 1 ∧ q ∉ centerOf Q} =
      {q : G | q ∈ Qz z ∧ q ^ 2 = 1 ∧ q ∉ Subgroup.zpowers z} := by
  have hf : Function.Injective (Gx z).subtype := Subgroup.subtype_injective (Gx z)
  have hcent := centerOf_eq_zpowers hz2 hQ
  rw [hQz]
  ext g
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨hqQ, hq2, hqcent⟩
    rw [hcent] at hqcent
    refine ⟨Subgroup.mem_map_of_mem (Gx z).subtype hqQ, ?_, ?_⟩
    · rw [← map_pow, hq2, map_one]
    · intro hmem
      exact hqcent ((Subgroup.mem_map_iff_mem hf).mp (by
        rw [MonoidHom.map_zpowers]
        rwa [show (Gx z).subtype (GxSelf z) = z from rfl]))
  · rintro ⟨hgQ, hg2, hgz⟩
    obtain ⟨q, hqQ, rfl⟩ := Subgroup.mem_map.mp hgQ
    refine ⟨q, ⟨hqQ, ?_, ?_⟩, rfl⟩
    · apply hf
      rw [map_pow, map_one]
      exact hg2
    · rw [hcent]
      intro hqmem
      exact hgz (by
        change (Gx z).subtype q ∈ Subgroup.zpowers ((Gx z).subtype (GxSelf z))
        rw [← MonoidHom.map_zpowers]
        exact Subgroup.mem_map_of_mem (Gx z).subtype hqmem)

theorem inv_classes_G (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hirr : ∀ W : Subgroup G, Subgroup.zpowers z ≤ W → W ≤ Qz z →
      (∀ g ∈ derivedOf (Gx z), ∀ w ∈ W, g * w * g⁻¹ ∈ W) → W = Subgroup.zpowers z ∨ W = Qz z) :
    ∃ S : Fin 2 → Set G,
      IsOrbitPartition (Gx z) {q | q ∈ Qz z ∧ q ^ 2 = 1 ∧ q ∉ Subgroup.zpowers z} S ∧
        Nat.card ↥(S 0) = 150 ∧ Nat.card ↥(S 1) = 120 := by
  obtain ⟨Q, hQnorm, hQW, hQz⟩ := exists_Qz_eq h.cent_z
  haveI : Q.Normal := hQnorm
  have hirrC : CIrreducible ↥(Gx z) Q := (cIrreducible_iff h.orderOf_z hQW hQz).mpr hirr
  obtain ⟨S', hpart', hcard0', hcard1'⟩ := hC.inv_classes ↥(Gx z) Q hQW hirrC
  let f : ↥(Gx z) →* G := (Gx z).subtype
  have hf : Function.Injective f := Subgroup.subtype_injective (Gx z)
  have htop : (⊤ : Subgroup ↥(Gx z)).map f = Gx z := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hN : f '' {q : ↥(Gx z) | q ∈ Q ∧ q ^ 2 = 1 ∧ q ∉ centerOf Q} =
      {q : G | q ∈ Qz z ∧ q ^ 2 = 1 ∧ q ∉ Subgroup.zpowers z} :=
    image_invSet_eq h.orderOf_z hQW hQz
  have hpart := (isOrbitPartition_map_iff hf (⊤ : Subgroup ↥(Gx z))
    {q : ↥(Gx z) | q ∈ Q ∧ q ^ 2 = 1 ∧ q ∉ centerOf Q} S').mpr hpart'
  rw [htop, hN] at hpart
  exact ⟨fun i => f '' S' i, hpart,
    by rw [Nat.card_image_of_injective hf, hcard0'],
    by rw [Nat.card_image_of_injective hf, hcard1']⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
