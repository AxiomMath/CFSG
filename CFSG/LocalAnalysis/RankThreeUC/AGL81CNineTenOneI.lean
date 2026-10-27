module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem starImg_xSub (p : ℕ) (M H : Subgroup G) :
    starImg p H (xSub p M H) = centralizer (kStar p M H : Set (StarGroup p H)) := by
  unfold xSub CFSG.AGLEmbedding.d1PlusCore starImg
  have h1 : (Subgroup.map H.subtype
        ((Subgroup.centralizer (kStar p M H : Set (StarGroup p H))).comap
          (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)))).subgroupOf H
      = (Subgroup.centralizer (kStar p M H : Set (StarGroup p H))).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [h1, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem sSup_le_centralizer_sSup {X : Type*} [Group X] [Finite X] (A : Subgroup X) :
    sSup {C : Subgroup X | CFSG.IsComponent C ∧ C ≤ A} ≤
      centralizer ((sSup {C : Subgroup X | CFSG.IsComponent C ∧ ¬ C ≤ A} : Subgroup X) :
        Set X) := by
  refine sSup_le fun C hC => ?_
  rw [Subgroup.le_centralizer_iff]
  refine sSup_le fun D hD => ?_
  rcases CFSG.LocalCores.distinct_components_commute hD.1 hC.1 with h | h
  · exact absurd (h.symm ▸ hC.2) hD.2
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

private theorem inf_sup_le_of_normal_right {X : Type*} [Group X] {K B D : Subgroup X}
    (hK : K.Normal) (hDB : D ≤ B) : B ⊓ (K ⊔ D) ≤ (B ⊓ K) ⊔ D := by
  letI := hK
  intro x hx
  have hxK : x ∈ K ⊔ D := hx.2
  change x ∈ (↑(K ⊔ D) : Set X) at hxK
  rw [Subgroup.normal_mul K D] at hxK
  obtain ⟨k, hk, d, hd, rfl⟩ := hxK
  have hdB : d ∈ B := hDB hd
  have hkB : k ∈ B := by
    have h1 : (k * d) * d⁻¹ ∈ B := B.mul_mem hx.1 (B.inv_mem hdB)
    simpa [mul_assoc] using h1
  exact Subgroup.mul_subset (SetLike.coe_subset_coe.mpr le_sup_left)
    (SetLike.coe_subset_coe.mpr le_sup_right) ⟨k, ⟨hkB, hk⟩, d, hd, rfl⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
