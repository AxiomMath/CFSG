module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fx_exists_commuting_nine (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (g : ↥(simGroup Q)) {w : ↥(omegaProj hQ)}
    (hw : w ∈ ffFix hQ (by omega) (QuotientGroup.mk g : ProjSim Q)) (h9 : orderOf w = 9) :
    ∃ u : OGroup Q, simAct Q g u = u ∧ u ^ 9 = 1 ∧ u ^ 3 ≠ 1 := by
  obtain ⟨y, -, hact, hyw⟩ := (ff6m_mem_ffFix_sim_iff hQ hdim hsgn g w).mp hw
  have hord : orderOf (toProj Q y) = 9 := by rw [hyw, Subgroup.orderOf_coe, h9]
  have hpow : ∀ n : ℕ, toProj Q (y ^ n) = toProj Q y ^ n := fun n => map_pow _ _ _
  have hy9 : y ^ 9 ∈ piGroup Q := by
    refine (QuotientGroup.eq_one_iff (y ^ 9)).mp ?_
    change toProj Q (y ^ 9) = 1
    rw [hpow, ← hord, pow_orderOf_eq_one]
  have hy18 : y ^ 18 = 1 := by
    have h18 : y ^ 18 = (y ^ 9) ^ 2 := by rw [← pow_mul]
    rcases mem_piGroup_iff.mp hy9 with h | h
    · rw [h18, h, one_pow]
    · rw [h18, h, sq]
      exact piOrth_mul_self
  have hcomm : Commute (piOrth Q) y :=
    (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) y).symm
  refine ⟨y ^ 10, ?_, ?_, ?_⟩
  · rw [map_pow]
    rcases hact with h | h
    · rw [h]
    · rw [h, hcomm.mul_pow]
      have h10 : piOrth Q ^ 10 = 1 := by
        rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul, sq, piOrth_mul_self, one_pow]
      rw [h10, one_mul]
  · rw [← pow_mul, show 10 * 9 = 18 * 5 from rfl, pow_mul, hy18, one_pow]
  · intro h
    have h30 : y ^ 12 = 1 := by
      have h1 : (y ^ 10) ^ 3 = y ^ 18 * y ^ 12 := by
        rw [← pow_mul, ← pow_add]
      rw [hy18, one_mul] at h1
      rw [← h1]
      exact h
    have h12 : toProj Q y ^ 12 = 1 := by rw [← hpow, h30, map_one]
    have := orderOf_dvd_of_pow_eq_one h12
    rw [hord] at this
    omega

end CFSG.OddStandard.SmallF3.Omega
