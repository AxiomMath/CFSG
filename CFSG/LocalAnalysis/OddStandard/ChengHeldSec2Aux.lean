module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelQS

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.exists_pow_t (c : Chart4 d α) {x : G} (hx : x ∈ zpowers c.t) :
    ∃ n : ℕ, n < 4 ∧ x = c.t ^ n := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have hr : c.t ^ k = c.t ^ (k % 4) := by
    rw [← zpow_mod_orderOf, c.orderOf_t]
    norm_num
  refine ⟨(k % 4).toNat, by omega, ?_⟩
  rw [hr, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]

theorem Chart4.mem_zpowers_t_of_pow_four (c : Chart4 d α) (h : Hyp G A) {u : G} (hu : u ∈ d.Q)
    (hu4 : u ^ 4 = 1) : u ∈ zpowers c.t := by
  have := d.Q_isCyclic h
  have hu' : (⟨u, hu⟩ : d.Q) ∈ zpowers (⟨c.t, c.t_mem.1⟩ : d.Q) :=
    mem_zpowers_of_pow_eq_one (n := 4) (by norm_num)
      (by rw [← c.orderOf_t]; exact (Subgroup.orderOf_coe (⟨c.t, c.t_mem.1⟩ : d.Q)).symm)
      (Subtype.ext (by simpa using hu4))
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hu'
  exact mem_zpowers_iff.2 ⟨m, by simpa using congrArg Subtype.val hm⟩

end CFSG.OddStandard.ChengHeld
