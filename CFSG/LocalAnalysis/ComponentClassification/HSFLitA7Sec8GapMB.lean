module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8BCase

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

namespace MB

theorem sq_of_comm_t : ∀ x : MB, x * t = t * x → x ^ 4 = 1 ∧ (x ^ 2 = 1 ∨ x ^ 2 = z) := by
  decide +kernel

end MB

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace BData

variable (A : BData S F T₁)

theorem T_le_S₁ : S.data.T ≤ A.D₁.S₁ := A.h4.le.trans A.D₁.T₁_le

include A in
theorem sq_eq_z_of_mem_T {g : X} (hg : g ∈ S.data.T) (_h4 : g ^ 4 = 1) (h2 : g ^ 2 ≠ 1) :
    g ^ 2 = S.z := by
  obtain ⟨x, rfl⟩ : ∃ x : MB, A.ι x = g := by
    have : g ∈ A.ι.range := A.range_ι ▸ A.T_le_S₁ hg
    exact this
  have hxt : x * MB.t = MB.t * x := by
    apply A.ι_injective
    rw [map_mul, map_mul, A.ι_t]
    exact S.data.commute_t hg
  rcases (MB.sq_of_comm_t x hxt).2 with h | h
  · exact absurd (by rw [← map_pow, h, map_one]) h2
  · rw [← map_pow, h, A.ι_z]

end BData

end Sec8

end CFSG.ComponentClassification.HSFLit
