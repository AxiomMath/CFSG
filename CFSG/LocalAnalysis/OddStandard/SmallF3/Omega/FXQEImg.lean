module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem fx_qe_image_ne {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ) (hL : IsOm6Z2 L) {z : G}
    (hzL : z ∈ L) (hzz : z * z = 1) (hz1 : z ≠ 1) (hzc : z ∉ centerIn L) :
    φ ⟨z, hzL⟩ ≠ 1 ∧ ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) ≠ piOrth Q := by
  have hoc : OddCentralCover φ := h.oddCentralCover hL
  let w : ↥L := ⟨z, hzL⟩
  have hww : w * w = 1 := by
    apply Subtype.ext
    change z * z = (1 : G)
    exact hzz
  have hw1 : w ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  constructor
  · intro h1
    exact hw1 (hoc.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h1) hww)
  · intro himg
    have hφw_cent : φ w ∈ Subgroup.center (omegaGroup hQ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, himg]
      exact mul_piOrth_comm (y : OGroup Q)
    have hw_center : w ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      have hl : φ l ∈ centralizer ({φ w} : Set (omegaGroup hQ)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_center_iff.mp hφw_cent (φ l)
      have hl' : l ∈ centralizer ({w} : Set ↥L) := by
        rw [hoc.centralizer_singleton_eq_comap hww, Subgroup.mem_comap]
        exact hl
      exact Subgroup.mem_centralizer_singleton_iff.mp hl'
    exact hzc ⟨w, hw_center, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
