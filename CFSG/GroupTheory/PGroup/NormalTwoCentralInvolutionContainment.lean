module


public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.NormalTwoCentralInvolutionContainment

theorem mem {H : Type*} [Group H] [Finite H] (hH2 : IsPGroup 2 H)
    (z : H) (hz : z ∈ Subgroup.center H) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (huniq : ∀ y ∈ Subgroup.center H, y ^ 2 = 1 → y ≠ 1 → y = z)
    (N : Subgroup H) [N.Normal] (hN : N ≠ ⊥) : z ∈ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent H := hH2.isNilpotent
  have hK : N ⊓ Subgroup.center H ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hN
  rw [ne_eq, Subgroup.eq_bot_iff_forall] at hK
  push Not at hK
  obtain ⟨x, hx, hx1⟩ := hK
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxN, hxC⟩ := hx
  have hdvd : 2 ∣ orderOf x := hH2.dvd_orderOf hx1
  have hord : orderOf (x ^ (orderOf x / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' hdvd
  have hyN : x ^ (orderOf x / 2) ∈ N := N.pow_mem hxN _
  have hyC : x ^ (orderOf x / 2) ∈ Subgroup.center H := Subgroup.pow_mem _ hxC _
  have hy2 : (x ^ (orderOf x / 2)) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (x ^ (orderOf x / 2))
    rwa [hord] at h
  have hy1 : x ^ (orderOf x / 2) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hyz := huniq _ hyC hy2 hy1
  rw [← hyz]
  exact hyN

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.NormalTwoCentralInvolutionContainment
