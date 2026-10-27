module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeEnum

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

private theorem lines_sixA_not_comm (h : IsF5Type a z) {x : G} (hx : x ∈ orb6A a a)
    (hcomm : a * x = x * a) : False := by
  have hcx : Commute a x := hcomm
  have h2 : (a * x) ^ 2 = 1 := by
    rw [hcx.mul_pow 2, sixA_a_sq h, sixA_x_sq h hx, one_mul]
  have hdvd : orderOf (a * x) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [(sixA_of_mem hx).2.1] at hdvd
  exact absurd hdvd (by norm_num)

theorem lines_sixA_inter (h : IsF5Type a z) {x : G} (hx : x ∈ orb6A a a) :
    Gxy a x ⊓ Subgroup.closure {a, (a * x) ^ 3} = Subgroup.zpowers ((a * x) ^ 3) := by
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    rcases eq_of_mem_closure_two (sixA_a_sq h) (sixA_b_sq h hx) (sixA_comm_ab h hx) hg.2 with
      rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exfalso
      exact lines_sixA_not_comm h hx (mem_Gx.mp (mem_Gxy.mp hg.1).2).symm
    · exact Subgroup.mem_zpowers _
    · exfalso
      have hxb : x * (a * x) ^ 3 = (a * x) ^ 3 * x := sixA_comm_xb h hx
      have hxab : x * (a * (a * x) ^ 3) = (a * (a * x) ^ 3) * x :=
        mem_Gx.mp (mem_Gxy.mp hg.1).2
      refine lines_sixA_not_comm h hx ?_
      have h1 : x * a * (a * x) ^ 3 = a * x * (a * x) ^ 3 := by
        calc x * a * (a * x) ^ 3 = x * (a * (a * x) ^ 3) := by rw [mul_assoc]
          _ = (a * (a * x) ^ 3) * x := hxab
          _ = a * ((a * x) ^ 3 * x) := by rw [mul_assoc]
          _ = a * (x * (a * x) ^ 3) := by rw [hxb]
          _ = a * x * (a * x) ^ 3 := by rw [← mul_assoc]
      exact (mul_right_cancel h1).symm
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr
      ⟨sixA_b_mem_Gxy_x h hx, Subgroup.subset_closure (by simp)⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
