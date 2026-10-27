module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSFacts
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSModel

public section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert

namespace GHSylow

variable {G : Type} [Group G] (D : GHSylow G)

theorem mem_map_toG {K : Subgroup SE} {s : SE} : D.toG s ∈ K.map D.toG ↔ s ∈ K :=
  mem_map_iff_mem D.toG_injective

theorem toG_eq_iff {s s' : SE} : D.toG s = D.toG s' ↔ s = s' := D.toG_injective.eq_iff

theorem toG_eq_one_iff {s : SE} : D.toG s = 1 ↔ s = 1 := by
  rw [← map_one D.toG, D.toG_eq_iff]

theorem inf_centralizer_toG (s : SE) :
    (D.S : Subgroup G) ⊓ centralizer ({D.toG s} : Set G) =
      (centralizer ({s} : Set SE)).map D.toG := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgS, hgc⟩ := mem_inf.mp hg
    obtain ⟨c, rfl⟩ := D.exists_toG hgS
    refine mem_map.mpr ⟨c, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    have h := mem_centralizer_singleton_iff.mp hgc
    rw [← map_mul, ← map_mul] at h
    exact D.toG_injective h
  · intro hg
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hg
    refine mem_inf.mpr ⟨D.toG_mem c, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hc]

theorem card_inf_centralizer_toG (s : SE) :
    Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({D.toG s} : Set G)) =
      Nat.card (centralizer ({s} : Set SE)) := by
  rw [inf_centralizer_toG, card_map_of_injective D.toG_injective]

theorem exists_conj_S_iff (s s' : SE) :
    (∃ c ∈ (D.S : Subgroup G), c⁻¹ * D.toG s * c = D.toG s') ↔
      ∃ c : SE, c⁻¹ * s * c = s' := by
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨c', rfl⟩ := D.exists_toG hc
    refine ⟨c', D.toG_injective ?_⟩
    rw [map_mul, map_mul, map_inv, h]
  · rintro ⟨c, h⟩
    exact ⟨D.toG c, D.toG_mem c, by rw [← map_inv, ← map_mul, ← map_mul, h]⟩

theorem exists_conj_invRep_G {u : G} (hu : u ∈ (D.S : Subgroup G))
    (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ i : Fin 9, ∃ c ∈ (D.S : Subgroup G), c⁻¹ * u * c = D.toG (SE.invRep i) := by
  obtain ⟨s, rfl⟩ := D.exists_toG hu
  have hs2 : s * s = 1 := D.toG_injective (by rw [map_mul, hu2, map_one])
  have hs1 : s ≠ 1 := fun h => hu1 (by rw [h, map_one])
  obtain ⟨i, c, hc⟩ := SE.exists_conj_invRep s hs2 hs1
  exact ⟨i, (D.exists_conj_S_iff s _).mpr ⟨c, hc⟩⟩

theorem card_centralizer_invRep_G (i : Fin 9) :
    Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep i)} : Set G)) =
      SE.invRepCent i := by
  rw [card_inf_centralizer_toG, SE.card_centralizer_invRep]

end GHSylow

end CFSG.ComponentClassification.GHarris
