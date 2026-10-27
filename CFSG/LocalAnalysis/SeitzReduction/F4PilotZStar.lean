module

public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

theorem orderOf_mul_eq_two_of_commute {G : Type*} [Group G] {t s : G} (ht : t * t = 1)
    (hs : s * s = 1) (hts : s * t = t * s) (hne : s ≠ t) : orderOf (t * s) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · calc (t * s) ^ 2 = t * (s * t) * s := by rw [sq]; group
      _ = (t * t) * (s * s) := by rw [hts]; group
      _ = 1 := by rw [ht, hs, one_mul]
  · intro h
    apply hne
    calc s = (t * t) * s := by rw [ht, one_mul]
      _ = t * (t * s) := by group
      _ = t := by rw [h, mul_one]

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_ne_commute_of_forall_odd_normal_eq_bot
    (hodd : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥) {t : G} (ht : t * t = 1)
    (htZ : t ∉ center G) :
    ∃ g : G, g⁻¹ * t * g ≠ t ∧ (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) := by
  have := Fintype.ofFinite G
  by_contra hcon
  have ht1 : t ≠ 1 := fun h => htZ (h ▸ one_mem _)
  have hiso : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    by_contra hne
    exact hcon ⟨g⁻¹, by rwa [inv_inv], by rwa [inv_inv]⟩
  obtain ⟨N, hN, hNodd, hNt⟩ := CFSG.ZStar.glauberman_zStar G t ht1 ht hiso
  have hNbot := hodd N hN hNodd
  refine htZ (mem_center_iff.2 fun g => ?_)
  have h1 := hNt g
  rw [hNbot, mem_bot, mul_inv_eq_one] at h1
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [h1]

omit [Finite G] in
theorem forall_odd_normal_eq_bot_and_not_mem_center_of_isSimpleGroup [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) :
    (∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥) ∧ t ∉ center G := by
  refine ⟨fun N hN hNodd => ?_, fun htZ => ?_⟩
  · rcases hN.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      rw [h, card_top] at hNodd
      have h2 : 2 ∣ Nat.card G := ht ▸ orderOf_dvd_natCard t
      exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 h2)
  · rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
    · rw [h, mem_bot] at htZ
      rw [htZ, orderOf_one] at ht
      exact absurd ht (by decide)
    · obtain ⟨a, b, hab⟩ := hnonab
      exact hab (mem_center_iff.1 (h ▸ mem_top b) a)

theorem exists_conj_ne_commute_of_isSimpleGroup [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) :
    ∃ g : G, g⁻¹ * t * g ≠ t ∧ (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) := by
  obtain ⟨hodd, htZ⟩ := forall_odd_normal_eq_bot_and_not_mem_center_of_isSimpleGroup hnonab ht
  exact exists_conj_ne_commute_of_forall_odd_normal_eq_bot hodd
    (by rw [← sq, ← ht, pow_orderOf_eq_one]) htZ

theorem exists_conj_ne_mem_centralizer_of_isSimpleGroup [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) :
    ∃ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) ∧ g⁻¹ * t * g ≠ t := by
  obtain ⟨g, hne, hc⟩ := exists_conj_ne_commute_of_isSimpleGroup hnonab ht
  exact ⟨g, mem_centralizer_singleton_iff.2 hc, hne⟩

theorem exists_conj_four_group_of_isSimpleGroup [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) :
    ∃ g : G, g⁻¹ * t * g ≠ t ∧ (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) ∧
      orderOf (g⁻¹ * t * g) = 2 ∧ orderOf (t * (g⁻¹ * t * g)) = 2 := by
  obtain ⟨g, hne, hc⟩ := exists_conj_ne_commute_of_isSimpleGroup hnonab ht
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hs2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2, mul_one, inv_mul_cancel]
  have hso : orderOf (g⁻¹ * t * g) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, ht]
  exact ⟨g, hne, hc, hso, orderOf_mul_eq_two_of_commute ht2 hs2 hc hne⟩

end CFSG.SeitzReduction.F4Pilot
