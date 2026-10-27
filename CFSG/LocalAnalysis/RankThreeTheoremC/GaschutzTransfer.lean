module

public import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

open scoped IsMulCommutative in
theorem not_isMulCommutative_sylow_of_isPerfect {p : ℕ} [Fact p.Prime] {L : Type*} [Group L]
    [Finite L] (hL : Group.IsPerfect L) (S : Sylow p L) {z : L} (hz : z ∈ center L) (hz1 : z ≠ 1)
    (hzp : z ^ p = 1) : ¬ IsMulCommutative (S : Subgroup L) := by
  intro hS
  have hker : z ∈ (MonoidHom.transfer (MonoidHom.id (S : Subgroup L))).ker :=
    Abelianization.commutator_subset_ker _ (hL.commutator_eq_top ▸ mem_top z)
  have hkey : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * z ^ k * g₀ ∈ (S : Subgroup L) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
    rw [mem_center_iff.1 ((center L).pow_mem hz k) g₀⁻¹, inv_mul_cancel_right]
  have hVz := MonoidHom.transfer_eq_pow (MonoidHom.id (S : Subgroup L)) z hkey
  rw [MonoidHom.mem_ker.1 hker] at hVz
  have hpow : z ^ (S : Subgroup L).index = 1 := (congrArg Subtype.val hVz).symm
  have hdvd : orderOf z ∣ (S : Subgroup L).index := orderOf_dvd_of_pow_eq_one hpow
  rw [orderOf_eq_prime hzp hz1] at hdvd
  exact S.not_dvd_index hdvd

theorem not_isCyclic_sylow_of_isPerfect {p : ℕ} [Fact p.Prime] {L : Type*} [Group L] [Finite L]
    (hL : Group.IsPerfect L) (S : Sylow p L) {z : L} (hz : z ∈ center L) (hz1 : z ≠ 1)
    (hzp : z ^ p = 1) : ¬ IsCyclic (S : Subgroup L) := fun hc =>
  not_isMulCommutative_sylow_of_isPerfect hL S hz hz1 hzp hc.isMulCommutative

end CFSG.LocalAnalysis.RankThreeTheoremC
