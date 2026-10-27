module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5

theorem exists_conj_le_of_odd_index {G : Type*} [Group G] [Finite G] {H R E : Subgroup G}
    (hRH : R ≤ H) (hEH : E ≤ H) (hR : IsPGroup 2 R) (hE : IsPGroup 2 E) {m : ℕ} (hm : Odd m)
    (hcard : Nat.card H = Nat.card R * m) : ∃ c ∈ H, ∀ x ∈ E, c * x * c⁻¹ ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRcard : Nat.card (R.subgroupOf H) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
  have hR' : IsPGroup 2 (R.subgroupOf H) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm
  have hindex : (R.subgroupOf H).index = m := by
    have h := (R.subgroupOf H).index_mul_card
    rw [hRcard, hcard] at h
    have hpos : 0 < Nat.card R := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  have hodd : ¬ 2 ∣ (R.subgroupOf H).index := by
    rw [hindex]
    exact fun h => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h)
  let RS : Sylow 2 H := hR'.toSylow hodd
  have hE' : IsPGroup 2 (E.subgroupOf H) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEH).symm
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q RS
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hEH hx⟩ : H) ∈ (Q : Subgroup H) := hQ (Subgroup.mem_subgroupOf.2 hx)
  have h1 := Subgroup.smul_mem_pointwise_smul (⟨x, hEH hx⟩ : H) (MulAut.conj g) (Q : Subgroup H) hxQ
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  exact Subgroup.mem_subgroupOf.1 h1

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5
