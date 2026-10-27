module

public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

theorem exists_conj_commute_ne [Finite G] (hG : IsSimpleGroup G) {t : G} (ht : orderOf t = 2)
    (hnc : ∃ a b : G, a * b ≠ b * a) :
    ∃ g : G, g⁻¹ * t * g ≠ t ∧ (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) := by
  by_contra h
  have hiso : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t := by
    intro g hcomm
    by_contra hne
    exact h ⟨g⁻¹, by simpa using hne, by simpa using hcomm⟩
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rw [ht] at hpow
    simpa [pow_two] using hpow
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G t ht1 ht2 hiso
  haveI : N.Normal := hNn
  rcases hG.eq_bot_or_eq_top_of_normal N with hN0 | hNtop
  · have hz : t ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := hN g
      rw [hN0, Subgroup.mem_bot] at hg
      calc g * t = (g * t * g⁻¹ * t⁻¹) * t * g := by group
        _ = t * g := by rw [hg, one_mul]
    have hcenter_ne : Subgroup.center G ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hz
      exact ht1 hz
    have htop : Subgroup.center G = ⊤ :=
      (hG.eq_bot_or_eq_top_of_normal (Subgroup.center G)).resolve_left hcenter_ne
    haveI : IsMulCommutative G := Subgroup.center_eq_top_iff.mp htop
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (mul_comm a b)
  · rw [hNtop, Subgroup.card_top] at hNodd
    exact hNodd.not_two_dvd_nat (by rw [← ht]; exact orderOf_dvd_natCard t)

end CFSG.OddStandard.SmallF3.Omega
