module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

public section

namespace CFSG.GroupTheory

theorem exists_pow_eq_of_pow_eq_one_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {k : ℕ} (hk : k ∣ Nat.card G) {x : G} (hx : x ^ k = 1) :
    ∃ y : G, y ^ (Nat.card G / k) = x := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Nat.card G :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨m, -, hm⟩ :=
    Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp (hg x))
  have hmk : g ^ (m * k) = 1 := by
    rw [pow_mul, hm, hx]
  have hdvd : Nat.card G ∣ m * k := by
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.mpr hmk
  have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hk Nat.card_pos
  have hdvd' : Nat.card G / k ∣ m := by
    rw [Nat.div_dvd_iff_dvd_mul hk hkpos]
    simpa [Nat.mul_comm] using hdvd
  obtain ⟨c, hc⟩ := hdvd'
  refine ⟨g ^ c, ?_⟩
  rw [← pow_mul, Nat.mul_comm c (Nat.card G / k), ← hc, hm]

end CFSG.GroupTheory
