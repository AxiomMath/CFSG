module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveSylow

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_isElemAbelian_centralizer_lift {A N : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {E : Subgroup (G ⧸ N)} (hE : IsElemAbelian p E)
    (hEimage : E ≤ (Subgroup.centralizer (A : Set G)).map (QuotientGroup.mk' N)) :
    ∃ E' : Subgroup G, IsElemAbelian p E' ∧
      E'.map (QuotientGroup.mk' N) = E ∧ Nat.card E' = Nat.card E ∧
      E' ≤ Subgroup.centralizer (A : Set G) := by
  let H : Subgroup G := Subgroup.centralizer (A : Set G)
  let ψ : ↥H →* (G ⧸ N) := (QuotientGroup.mk' N).comp H.subtype
  have hψrange : ψ.range = H.map (QuotientGroup.mk' N) := by
    ext x
    simp [ψ, MonoidHom.range_comp]
  have hErange : E ≤ ψ.range := by
    rw [hψrange]
    exact hEimage
  have hψker : ψ.ker = N.subgroupOf H := by
    ext x
    simp [ψ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hdvd : Nat.card (N.subgroupOf H) ∣ Nat.card N := by
    have hcard : Nat.card (N.subgroupOf H) = Nat.card (N ⊓ H : Subgroup G) := by
      rw [← Subgroup.subgroupOf_map_subtype N H,
        Subgroup.card_map_of_injective H.subtype_injective]
    rw [hcard]
    exact Subgroup.card_dvd_of_le (inf_le_left : N ⊓ H ≤ N)
  have hker : ¬ p ∣ Nat.card ψ.ker := by
    rw [hψker]
    exact fun h => hN (h.trans hdvd)
  obtain ⟨E', hE'e, hE'map, hE'card⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_lift_of_le_range ψ hker hErange hE
  refine ⟨E'.map H.subtype, ?_, ?_, ?_, Subgroup.map_subtype_le E'⟩
  · exact IsElemAbelian.map hE'e H.subtype
  · rw [Subgroup.map_map]
    exact hE'map
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hE'card]

end CFSG.GroupTheory

end
