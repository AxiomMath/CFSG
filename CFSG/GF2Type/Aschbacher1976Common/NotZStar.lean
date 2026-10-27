module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25

public section

namespace CFSG.GF2Type.Aschbacher1976Common

open CFSG.EvenSporadicStandard.Finkelstein77

theorem not_inZStar_of_isSimpleGroup {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2) : ¬ InZStar z := by
  rintro ⟨N, hNnormal, hNodd, hcomm⟩
  have hcenter : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact (hab (isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h) a b)).elim
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  ·
    have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := hcomm g
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
    rw [hcenter, Subgroup.mem_bot] at hzc
    rw [hzc, orderOf_one] at hz
    omega
  ·
    subst htop
    rw [Subgroup.card_top] at hNodd
    have h2 : orderOf z ∣ Nat.card G := orderOf_dvd_natCard z
    rw [hz] at h2
    obtain ⟨m, hm⟩ := hNodd
    obtain ⟨c, hc⟩ := h2
    omega

end CFSG.GF2Type.Aschbacher1976Common
