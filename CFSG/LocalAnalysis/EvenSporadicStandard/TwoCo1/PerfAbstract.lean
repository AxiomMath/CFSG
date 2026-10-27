module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open scoped commutatorElement

theorem isPerfect_of_sq_eq_central {G Q : Type*} [Group G] [Group Q] [IsSimpleGroup Q]
    (π : G →* Q) (hπ : Function.Surjective π) {z J : G} (hz : z ∈ Subgroup.center G)
    (hz2 : z * z = 1) (hker : π.ker = Subgroup.zpowers z) (hJ : J * J = z)
    (hQ : ¬ (Nat.card Q).Prime) : Group.IsPerfect G := by
  have : ((commutator G).map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases Subgroup.Normal.eq_bot_or_eq_top ((commutator G).map π) with hM | hM
  · exfalso
    have hcomm : ∀ x y : Q, x * y = y * x := by
      intro x y
      obtain ⟨a, rfl⟩ := hπ x
      obtain ⟨b, rfl⟩ := hπ y
      have h1 : π ⁅a, b⁆ ∈ (commutator G).map π :=
        Subgroup.mem_map_of_mem π
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
      rw [hM, Subgroup.mem_bot, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    let : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcomm }
    exact hQ (IsSimpleGroup.prime_card (α := Q))
  · have hmem : ∀ g : G, ∃ n ∈ commutator G, π n = π g := fun g => by
      have h : π g ∈ (commutator G).map π := hM ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := h
      exact ⟨n, hn, hng⟩
    have hker_mem : ∀ n g : G, π n = π g → n⁻¹ * g ∈ Subgroup.zpowers z := fun n g h => by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    obtain ⟨n, hn, hnJ⟩ := hmem J
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hker_mem n J hnJ)
    have hJ' : J = n * z ^ m := by rw [hm, mul_inv_cancel_left]
    have hc : n * z ^ m = z ^ m * n :=
      Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hz m) n
    have hzz : z ^ m * z ^ m = 1 := by
      rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz2, one_zpow]
    have hzN : z ∈ commutator G := by
      have h : z = n * n := by
        calc z = J * J := hJ.symm
          _ = (n * z ^ m) * (n * z ^ m) := by rw [← hJ']
          _ = n * (z ^ m * n) * z ^ m := by simp only [mul_assoc]
          _ = n * (n * z ^ m) * z ^ m := by rw [hc]
          _ = n * n * (z ^ m * z ^ m) := by simp only [mul_assoc]
          _ = n * n := by rw [hzz, mul_one]
      rw [h]
      exact mul_mem hn hn
    have hkerN : ∀ g : G, g ∈ π.ker → g ∈ commutator G := fun g hg => by
      rw [hker] at hg
      exact Subgroup.zpowers_le.2 hzN hg
    refine Group.isPerfect_def.2 (eq_top_iff.2 fun g _ => ?_)
    obtain ⟨n', hn', hn'g⟩ := hmem g
    have h2 : n'⁻¹ * g ∈ commutator G := hkerN _ (by rw [hker]; exact hker_mem n' g hn'g)
    rw [← mul_inv_cancel_left n' g]
    exact mul_mem hn' h2

end CFSG.EvenSporadicStandard.TwoCo1
