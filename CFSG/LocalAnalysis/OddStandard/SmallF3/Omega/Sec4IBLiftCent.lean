module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem sec4ILift_cent (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {P : Subgroup G} (hP : IsSylow2Of P L) {fr : Sec4IFrame Sec4IQ}
    (hfr : Sec4IGood fr ((P.subgroupOf L).map (sec4IRho e))) :
    centralizer (sec4ILiftB e fr P : Set G) ⊓ L = sec4ILiftB e fr P ⊔ centerIn L := by
  have hmap := sec4ILift_map_eq hL e hP hfr
  have hmax := sec4ILift_isMax hL e hP hfr
  apply le_antisymm
  · intro x hx
    obtain ⟨hxC, hxL⟩ := Subgroup.mem_inf.mp hx
    have hcent : sec4IRho e ⟨x, hxL⟩ ∈
        Subgroup.centralizer (sec4IB0 fr : Set (ProjOrth Sec4IQ)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hmap] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      have hbB : (b : G) ∈ sec4ILiftB e fr P := hb
      have hcomm : (b : G) * x = x * (b : G) := Subgroup.mem_centralizer_iff.mp hxC b hbB
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
    rw [sec4I_centralizer_B0 sec4IQ_nondegenerate fr, ← hmap] at hcent
    obtain ⟨b, hb, hbx⟩ := hcent
    have hbB : (b : G) ∈ sec4ILiftB e fr P := hb
    have hker : b⁻¹ * (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [← sec4IRho_eq_one_iff e, map_mul, map_inv, hbx, inv_mul_cancel]
    have hxeq : x = (b : G) * ((b : G)⁻¹ * x) := by group
    rw [hxeq]
    exact Subgroup.mul_mem_sup hbB ⟨b⁻¹ * ⟨x, hxL⟩, hker, rfl⟩
  · refine sup_le ?_ ?_
    · refine le_inf ?_ (sec4ILiftB_le_L e fr P)
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      haveI : IsMulCommutative ↥(sec4ILiftB e fr P) := hmax.2.1.1
      exact mul_comm_of_mem_isMulCommutative (sec4ILiftB e fr P) hc hb
    · refine le_inf ?_ (by
        rintro _ ⟨z, -, rfl⟩
        exact z.2)
      rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcL : c ∈ L := sec4ILiftB_le_L e fr P hc
      have := Subgroup.mem_center_iff.mp hz ⟨c, hcL⟩
      exact congrArg Subtype.val this

end CFSG.OddStandard.SmallF3.Omega
