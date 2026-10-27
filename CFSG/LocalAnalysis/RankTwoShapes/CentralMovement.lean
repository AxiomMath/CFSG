module

public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution

public section

namespace CFSG.RankTwoShapes

theorem simple_central_sylow_involution_movement {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    (z : (S : Subgroup G)) (hzZ : z ∈ Subgroup.center (S : Subgroup G))
    (hz : orderOf z = 2) :
    ∃ g : G, g⁻¹ * (z : G) * g ∈ (S : Subgroup G) ∧ g⁻¹ * (z : G) * g ≠ z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hfact, -⟩ :=
    CFSG.Milestones.glauberman_zStar_central_sylow_involution S z hzZ hz hcon
  have hzG : orderOf (z : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hz
  have hcore : CFSG.oddCore G = ⊥ := by
    rcases (CFSG.oddCore_normal G).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (h ▸ Subgroup.mem_top (z : G))
        (CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hzG)
  have hcentral : ∀ g : G, g * (z : G) = (z : G) * g := by
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hfact g
    rw [hcore, Subgroup.mem_bot] at hk
    subst hk
    rw [mul_one]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have hzcenter : (z : G) ∈ Subgroup.center G :=
    Subgroup.mem_center_iff.mpr hcentral
  have hztop : Subgroup.center G = ⊤ := by
    rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.mem_bot] at hzcenter
      rw [hzcenter, orderOf_one] at hzG
      exact absurd hzG (by norm_num)
    · exact h
  obtain ⟨a, b, hab⟩ := hnonab
  apply hab
  have hb : b ∈ Subgroup.center G := hztop ▸ Subgroup.mem_top b
  exact (Subgroup.mem_center_iff.mp hb a)

end CFSG.RankTwoShapes
