module

public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem z18_thompson_finish (hG : IsSimpleGroup G) (h4 : 4 ∣ Nat.card G) {P M : Subgroup G}
    (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) (hMP : M ≤ P) (hMidx : M.relIndex P = 2)
    {t : G} (ht2 : t * t = 1) (htP : t ∈ P) (htM : t ∉ M)
    (hdisj : ∀ g : G, g⁻¹ * t * g ∉ M) : False := by
  have ht1 : t ≠ 1 := fun h => htM (h ▸ M.one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
  have hmin : ∀ y ∈ P, y ∉ M → orderOf t ≤ orderOf y := by
    intro y _ hyM
    have hy1 : y ≠ 1 := fun h => hyM (h ▸ M.one_mem)
    have hpos : 0 < orderOf y := orderOf_pos y
    have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
    rw [hord]
    omega
  obtain ⟨N, hN, hN2⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hP hPidx hMP
    hMidx htP htM hmin hdisj
  haveI := hG
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
  · rw [Subgroup.index_bot] at hN2
    rw [hN2] at h4
    omega
  · rw [Subgroup.index_top] at hN2
    omega

theorem z18_final_of_index_two (hG : IsSimpleGroup G) (h4 : 4 ∣ Nat.card G) {P M K : Subgroup G}
    (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) (hMP : M ≤ P) (hMidx : M.relIndex P = 2)
    {t lam : G} (ht2 : t * t = 1) (htP : t ∈ P) (htM : t ∉ M)
    (hM : ∀ u ∈ M, u * u = 1 → u ∈ K ∨ ∃ k ∈ K, u = lam * k)
    (hK : ∀ g : G, ∀ u ∈ K, g⁻¹ * t * g ≠ u)
    (hlam : ∀ g : G, ∀ k ∈ K, g⁻¹ * t * g ≠ lam * k) : False := by
  refine z18_thompson_finish hG h4 hP hPidx hMP hMidx ht2 htP htM fun g hg => ?_
  have hsq : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group
  rcases hM _ hg hsq with hk | ⟨k, hk, hu⟩
  · exact hK g _ hk rfl
  · exact hlam g k hk hu

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
