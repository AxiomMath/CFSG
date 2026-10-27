module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8Rho
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8Aut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8MainT2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec5pe8m_odd_mem_kerG
    {G : Type} [Group G] [Finite G] {X : Type} [Group X] [Finite X] {t z : G} {T : Subgroup G}
    {π : ↥(centralizer ({z} : Set G)) →* X} (hyp : Sec5OPHyp t z T π)
    (hout : Sec5G8Outcome (sec5op_Tb z T π)) {L : Subgroup G} {k : G}
    (hkH : k ∈ centralizer ({z} : Set G)) (hkL : k ∈ L) (hk : Odd (orderOf k))
    (hkT : ∀ x ∈ T, x * k = k * x) (htT : ∀ x ∈ T, x * t = t * x)
    (hLA : ∀ w ∈ sec5op_Y t z, w * t = t * w → Nat.Coprime (orderOf w) 6 →
      w ∈ centralizer (L : Set G)) :
    k ∈ sec5op_kerG z T π := by
  have htb : π ⟨t, hyp.tH⟩ ∈ sec5op_Tb z T π := by
    rw [sec5op_Tb]
    exact Subgroup.mem_map.mpr
      ⟨⟨t, hyp.tH⟩, Subgroup.mem_subgroupOf.mpr hyp.tT, rfl⟩
  have hg : Odd (orderOf (π ⟨k, hkH⟩)) := by
    have h1 : orderOf (π ⟨k, hkH⟩) ∣
        orderOf (⟨k, hkH⟩ : ↥(centralizer ({z} : Set G))) :=
      orderOf_map_dvd π _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hk h1
  have hgT : ∀ a ∈ sec5op_Tb z T π,
      π ⟨k, hkH⟩ * a * (π ⟨k, hkH⟩)⁻¹ = a := by
    intro a ha
    rw [sec5op_Tb, Subgroup.mem_map] at ha
    obtain ⟨⟨x, hxH⟩, hxT, rfl⟩ := ha
    have hxT' : x ∈ T := Subgroup.mem_subgroupOf.mp hxT
    have hcomm : x * k = k * x := hkT x hxT'
    have hmul : (⟨k, hkH⟩ : ↥(centralizer ({z} : Set G))) * ⟨x, hxH⟩ *
        ⟨k, hkH⟩⁻¹ = ⟨x, hxH⟩ := by
      apply Subtype.ext
      show k * x * k⁻¹ = x
      rw [hcomm.symm]
      group
    rw [← map_mul, ← map_inv, ← map_mul, hmul]
  have hc : ∀ a ∈ sec5op_Tb z T π,
      π ⟨t, hyp.tH⟩ * a = a * π ⟨t, hyp.tH⟩ := by
    intro a ha
    rw [sec5op_Tb, Subgroup.mem_map] at ha
    obtain ⟨⟨x, hxH⟩, hxT, rfl⟩ := ha
    have hxT' : x ∈ T := Subgroup.mem_subgroupOf.mp hxT
    have hcomm : t * x = x * t := (htT x hxT').symm
    have hmul : (⟨t, hyp.tH⟩ : ↥(centralizer ({z} : Set G))) * ⟨x, hxH⟩ =
        ⟨x, hxH⟩ * ⟨t, hyp.tH⟩ := by
      apply Subtype.ext
      show t * x = x * t
      exact hcomm
    rw [← map_mul, hmul, map_mul]
  have ht2 : orderOf (sec5g_pi (sec5op_Tb z T π)
      ⟨π ⟨t, hyp.tH⟩, Subgroup.subset_normalClosure htb⟩) = 2 := by
    have h : (⟨π ⟨t, hyp.tH⟩, Subgroup.subset_normalClosure htb⟩ :
        ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))) =
        ⟨π ⟨t, sec5op_Y_le hyp.tH (sec5op_t_mem_Y t z)⟩,
          sec5op_pi_mem hyp (sec5op_t_mem_Y t z)⟩ := Subtype.ext rfl
    rw [h]
    exact sec5pe8m_cls_t_order hyp
  have hfix : ∀ c : Sec5GBar (sec5op_Tb z T π),
      c * sec5g_pi (sec5op_Tb z T π)
          ⟨π ⟨t, hyp.tH⟩, Subgroup.subset_normalClosure htb⟩ =
        sec5g_pi (sec5op_Tb z T π)
          ⟨π ⟨t, hyp.tH⟩, Subgroup.subset_normalClosure htb⟩ * c →
      Nat.Coprime (orderOf c) 6 →
        sec5op_act (sec5op_Tb z T π) (π ⟨k, hkH⟩) c = c := by
    intro c hct hc6
    exact sec5pe8_fix hyp hkH hkL hLA c hc6 hct
  have hact : sec5op_act (sec5op_Tb z T π) (π ⟨k, hkH⟩) = 1 :=
    sec5pe8_act_eq_one sec5pe8_aut_statement hout hg hgT htb hc ht2 hfix
  refine (sec5op_mem_kerG_iff).mpr ⟨hkH, ?_⟩
  exact hact

end CFSG.OddStandard.SmallF3.Omega
