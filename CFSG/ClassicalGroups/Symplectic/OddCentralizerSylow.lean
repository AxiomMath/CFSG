module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR7iii

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.SymplecticPilot

theorem odd_centralizer_sylow_le_center_sp {m : ℕ} (hm : 3 ≤ m) {F : Type} [Field F]
    [Finite F] [CharP F 2] (U : Sylow 2 (StatedSp m F)) {x : StatedSp m F}
    (hxodd : Odd (orderOf x))
    (hxc : x ∈ Subgroup.centralizer
      ((U : Subgroup (StatedSp m F)) : Set (StatedSp m F))) :
    x ∈ Subgroup.center (StatedSp m F) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Subgroup.one_mem _
  exfalso
  have hxU : ∀ u ∈ (U : Subgroup (StatedSp (n + 3) F)), u * x = x * u :=
    fun u hu => Subgroup.mem_centralizer_iff.mp hxc u hu
  obtain ⟨κ, c, hc⟩ := exists_conj_eq_spRep (K := F) (n := n) (U := U) hx1 hxU
  have hsp2 : spRep (K := F) n κ ^ 2 = 1 := by
    rw [pow_two, spRep, twoCentralRep, twoCentralElt_mul]
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    rw [show (κ.params F).1 + (κ.params F).1 = 0 by rw [← two_mul, h2, zero_mul],
      show (κ.params F).2 + (κ.params F).2 = 0 by rw [← two_mul, h2, zero_mul],
      twoCentralElt_zero]
  have hspne : spRep (K := F) n κ ≠ 1 := spRep_ne_one n κ
  have hspord : orderOf (spRep (K := F) n κ) = 2 :=
    orderOf_eq_prime hsp2 hspne
  have hconj : orderOf (c * x * c⁻¹) = orderOf x := by
    rw [← MulAut.conj_apply]
    exact MulEquiv.orderOf_eq (MulAut.conj c) x
  rw [hc, hspord] at hconj
  have h2dvd : 2 ∣ orderOf x := by rw [← hconj]
  exact hxodd.not_two_dvd_nat h2dvd

end CFSG.ClassicalGroups.Symplectic
