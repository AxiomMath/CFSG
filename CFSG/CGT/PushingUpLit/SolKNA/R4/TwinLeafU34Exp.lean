module

public import CFSG.GH74.Uniqueness.Bender.UnitaryOuterRoot

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG.GH74.Uniqueness.Bender

variable {K : Type*} [Group K]

theorem pow_four_eq_one_of_benderType [Finite K]
    {n e : ℕ} (h : BenderType K n 3 e) (Q : Sylow 2 K) {g : K} (hg : g ∈ (Q : Subgroup K)) :
    g ^ 4 = 1 := by
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have h4 : g * g * (g * g) = 1 := hc.center_sq (g * g) (h.sq_mem_rootCenter_unitary Q hg)
  calc g ^ 4 = g * g * (g * g) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h4

theorem no_orderOf_eight_of_benderType [Finite K]
    {n e : ℕ} (h : BenderType K n 3 e) {g : K} (hg : orderOf g = 8) : False := by
  have hcard : Nat.card ↥(Subgroup.zpowers g) = 2 ^ 3 := by
    rw [Nat.card_zpowers, hg]
    norm_num
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  have h4 : g ^ 4 = 1 := pow_four_eq_one_of_benderType h Q (hQ (Subgroup.mem_zpowers g))
  have hdvd : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  rw [hg] at hdvd
  omega

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
