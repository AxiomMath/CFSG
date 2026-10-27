module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410OmX

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem fz410_card_Om {E P Q : Subgroup G} (hEP : E ≤ P) (hPQ : P ≤ Q)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ E) (hsq : ∀ x ∈ Q, x ^ 2 ∈ E)
    (hE : Nat.card E = 16) (hP : Nat.card P = 64) (hQ : Nat.card Q = 128) :
    Nat.card (Fz410Om E P Q) = 4 := by
  have hNnormal : (E.subgroupOf Q).Normal := by
    constructor
    intro n hn g
    have hnE : (n : G) ∈ E := hn
    have hgQ : (g : G) ∈ Q := g.2
    have hc := hcomm (g : G) hgQ (n : G) (le_trans hEP hPQ hnE)
    have heq : (g : G) * (n : G) * (g : G)⁻¹
        = ((g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹) * (n : G) := by group
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      heq]
    exact E.mul_mem hc hnE
  haveI : (E.subgroupOf Q).Normal := hNnormal
  have hcardN : Nat.card (E.subgroupOf Q) = 16 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans hEP hPQ)).toEquiv
    exact h.trans hE
  have hcardV : Nat.card (Q ⧸ E.subgroupOf Q) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf Q)
    rw [hQ, hcardN] at h
    refine Nat.mul_right_cancel (by norm_num : 0 < 16) ?_
    rw [← h]
  have hexp : ∀ v : Q ⧸ E.subgroupOf Q, v ^ 2 = 1 := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf Q) v
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    simpa using hsq (x : G) x.2
  have hPsub_comap :
      (((P.subgroupOf Q).map (QuotientGroup.mk' (E.subgroupOf Q))).comap
        (QuotientGroup.mk' (E.subgroupOf Q))) = P.subgroupOf Q := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk' (E.subgroupOf Q), sup_comm]
    exact sup_eq_right.mpr (Subgroup.subgroupOf_mono Q hEP)
  have hcardPbar :
      Nat.card ((P.subgroupOf Q).map (QuotientGroup.mk' (E.subgroupOf Q))) = 4 := by
    have hc := fz410x_om_card_comap (E.subgroupOf Q)
      ((P.subgroupOf Q).map (QuotientGroup.mk' (E.subgroupOf Q)))
    rw [hPsub_comap, show Nat.card (P.subgroupOf Q) = 64 from
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPQ).toEquiv).trans hP, hcardN] at hc
    refine (Nat.mul_left_cancel (by norm_num : 0 < 16) ?_).symm
    rw [← hc]
  calc Nat.card (Fz410Om E P Q)
      = Nat.card {H : Subgroup (Q ⧸ E.subgroupOf Q) //
          Nat.card H = 2 ∧
            ¬ H ≤ (P.subgroupOf Q).map (QuotientGroup.mk' (E.subgroupOf Q))} :=
        Nat.card_congr (fz410x_om_equiv hEP hPQ)
    _ = 4 := fz410x_om_card_subgroups _ hcardV hcardPbar hexp

end CFSG.OddStandard.SmallF3.FritzII
