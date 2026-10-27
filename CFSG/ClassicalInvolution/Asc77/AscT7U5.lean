module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Out

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T7U

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {R N : Subgroup G} {x y : G} {n : ℕ}

theorem shiftCoord (c : T7F2.QuatCoord R x y n) : T7F2.QuatCoord R x (y * x) n := by
  refine ⟨c.ha, R.mul_mem c.hb c.ha, ?_, c.hn, c.hord, ?_, ?_⟩
  · calc y * x * x * (y * x)⁻¹ = y * x * y⁻¹ := by group
      _ = x⁻¹ := c.hbab
  · have := c.sq_mul 1
    simpa using this
  · intro r hr
    rcases c.cover r hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · refine Or.inr ⟨i - 1, ?_⟩
      rw [zpow_sub_one]
      group

theorem isFAut_of_action_pm {n' : ℕ} (s : T7F2.Out.Setting R N x y (n' + 2))
    (hN2 : IsPGroup 2 ↥N) {m : G} (hm : m ∈ N)
    (hx : m * x * m⁻¹ = x ^ ((1 : ℤ) + 2 ^ (n' + 2)))
    (hy : m * y * m⁻¹ = y ∨ m * y * m⁻¹ = y * x ^ (2 ^ (n' + 2))) : IsFAut R m := by
  rcases hy with hy | hy
  · exact T7F2.Out.isFAut_of_action s hN2 hm hx hy
  · have c := s.coord
    have s' : T7F2.Out.Setting R N x (y * x) (n' + 2) := ⟨shiftCoord c, s.hRN, s.hNR, s.hNa⟩
    refine T7F2.Out.isFAut_of_action s' hN2 hm hx ?_
    have h1 : m * (y * x) * m⁻¹ = (m * y * m⁻¹) * (m * x * m⁻¹) := by group
    rw [h1, hy, hx]
    have h2 : y * x ^ (2 ^ (n' + 2)) * x ^ ((1 : ℤ) + 2 ^ (n' + 2)) = y * x := by
      have e : x ^ (2 ^ (n' + 2)) * x ^ ((1 : ℤ) + 2 ^ (n' + 2)) = x := by
        rw [← zpow_natCast, ← zpow_add]
        have : x ^ (((2 ^ (n' + 2) : ℕ) : ℤ) + ((1 : ℤ) + 2 ^ (n' + 2))) = x ^ (1 : ℤ) := by
          rw [c.zpow_eq_iff]
          refine ⟨1, ?_⟩
          push_cast
          ring
        simpa using this
      rw [mul_assoc, e]
    exact h2

end CFSG.ClassicalInvolution.Asc77.T7U
