module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutDefs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229Aut

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.GH74.GLS.Bg.TwoGroups

namespace Sigma3Rel

variable {G : Type*} [Group G] {ρ x : G}

theorem cube (h : Sigma3Rel ρ x) : ρ ^ 3 = 1 := by
  rw [← h.ord_ρ]
  exact pow_orderOf_eq_one ρ

theorem sq (h : Sigma3Rel ρ x) : x ^ 2 = 1 := by
  rw [← h.ord_x]
  exact pow_orderOf_eq_one x

theorem mul_self (h : Sigma3Rel ρ x) : x * x = 1 := by
  rw [← pow_two]
  exact h.sq

theorem ne_one (h : Sigma3Rel ρ x) : ρ ≠ 1 := by
  intro h1
  have := h.ord_ρ
  rw [h1, orderOf_one] at this
  omega

end Sigma3Rel

theorem no_sigma3_sylSU {T : Type} [Group T] (e : T ≃* SylSU3_4) {ρ x : MulAut T}
    (h : Sigma3Rel ρ x) : False := by
  refine CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229.no_s3_aut
    ⟨MulAut.congr e ρ, MulAut.congr e x, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact h.ne_one ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  · rw [← map_pow, h.cube, map_one]
  · rw [← map_pow, h.sq, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, h.conj, map_inv]

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
