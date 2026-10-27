module

public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
public import CFSG.FeitThompson.Foundations.SubgroupProductQuotient
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

theorem map_sup_mk'_eq_map_mk' (H N : Subgroup G) [N.Normal] :
    (H ⊔ N).map (QuotientGroup.mk' N) = H.map (QuotientGroup.mk' N) := by
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]

theorem ker_mk'_comp_subtype (H N : Subgroup G) [N.Normal] :
    ((QuotientGroup.mk' N).comp H.subtype).ker = (N ⊓ H).subgroupOf H := by
  ext x
  simp [Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]

theorem range_mk'_comp_subtype (H N : Subgroup G) [N.Normal] :
    ((QuotientGroup.mk' N).comp H.subtype).range = H.map (QuotientGroup.mk' N) := by
  rw [MonoidHom.range_comp, Subgroup.subtype_range]

noncomputable def quotientInfEquivMapMk' (H N : Subgroup G) [N.Normal] :
    H ⧸ (N ⊓ H).subgroupOf H ≃* H.map (QuotientGroup.mk' N) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_mk'_comp_subtype H N).symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (range_mk'_comp_subtype H N)))

theorem natCard_map_mk'_mul_natCard_inf (H N : Subgroup G) [N.Normal] :
    Nat.card (H.map (QuotientGroup.mk' N)) * Nat.card (N ⊓ H : Subgroup G) = Nat.card H := by
  have h : Nat.card ((N ⊓ H).subgroupOf H) = Nat.card (N ⊓ H : Subgroup G) :=
    Nat.card_eq_of_bijective _
      (Subgroup.subgroupOfEquivOfLe (inf_le_right (a := N) (b := H))).bijective
  rw [← range_mk'_comp_subtype H N, ← h, ← ker_mk'_comp_subtype H N, ← Subgroup.index_ker,
    Subgroup.index_mul_card]

theorem natCard_map_mk'_eq_natCard_div [Finite G] (H N : Subgroup G) [N.Normal] :
    Nat.card (H.map (QuotientGroup.mk' N)) = Nat.card H / Nat.card (N ⊓ H : Subgroup G) := by
  rw [Nat.card_eq_of_bijective _ (quotientInfEquivMapMk' H N).symm.bijective,
    natCard_quotient_eq_natCard_div,
    Nat.card_eq_of_bijective _
      (Subgroup.subgroupOfEquivOfLe (inf_le_right (a := N) (b := H))).bijective]

noncomputable def mapMk'EquivSupQuotient (H N : Subgroup G) [N.Normal] :
    H.map (QuotientGroup.mk' N) ≃* (N ⊔ H : Subgroup G) ⧸ N.subgroupOf (N ⊔ H) :=
  (quotientInfEquivMapMk' H N).symm.trans (quotientInfEquivSupQuotient N H)

theorem natCard_map_mk'_dvd (H N : Subgroup G) [N.Normal] :
    Nat.card (H.map (QuotientGroup.mk' N)) ∣ Nat.card H :=
  ⟨_, (natCard_map_mk'_mul_natCard_inf H N).symm⟩

theorem index_map_mk' (H N : Subgroup G) [N.Normal] :
    (H.map (QuotientGroup.mk' N)).index = (H ⊔ N).index := by
  rw [Subgroup.index_map, QuotientGroup.ker_mk', MonoidHom.range_eq_top_of_surjective _
    (QuotientGroup.mk'_surjective N), Subgroup.index_top, mul_one]

theorem index_map_mk'_dvd_index (H N : Subgroup G) [N.Normal] :
    (H.map (QuotientGroup.mk' N)).index ∣ H.index := by
  rw [index_map_mk']
  exact Subgroup.index_dvd_of_le le_sup_left

theorem IsHallSubgroup.map_sup_mk' [Finite G] {π : Set ℕ} {H : Subgroup G} (N : Subgroup G)
    [N.Normal] (h : IsHallSubgroup π H) :
    IsHallSubgroup π ((H ⊔ N).map (QuotientGroup.mk' N)) := by
  rw [map_sup_mk'_eq_map_mk']
  exact ⟨h.natCard.of_dvd (natCard_map_mk'_dvd H N) Nat.card_pos.ne',
    h.index.of_dvd (index_map_mk'_dvd_index H N) Subgroup.index_ne_zero_of_finite⟩

end
end CFSG.FeitThompson

