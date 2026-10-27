module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.GLS.Th2.P412

theorem sec5pe8_act_eq_one (hAut : Sec5PE8AutStatement) {X : Type} [Group X] [Finite X]
    {Tb : Subgroup X} (hout : Sec5G8Outcome Tb) {g : X} (hg : Odd (orderOf g))
    (hgT : ∀ a ∈ Tb, g * a * g⁻¹ = a) {tb : X} (htb : tb ∈ Tb) (hc : ∀ a ∈ Tb, tb * a = a * tb)
    (ht2 : orderOf (sec5g_pi Tb ⟨tb, Subgroup.subset_normalClosure htb⟩) = 2)
    (hfix : ∀ c : Sec5GBar Tb,
      c * sec5g_pi Tb ⟨tb, Subgroup.subset_normalClosure htb⟩ =
        sec5g_pi Tb ⟨tb, Subgroup.subset_normalClosure htb⟩ * c →
      Nat.Coprime (orderOf c) 6 → sec5op_act Tb g c = c) :
    sec5op_act Tb g = 1 := by
  haveI : Finite (Sec5GBar Tb) := inferInstance
  obtain ⟨P, hPimg, hD8, -, -, hshape⟩ := hout
  set tb' : Sec5GBar Tb := sec5g_pi Tb ⟨tb, Subgroup.subset_normalClosure htb⟩ with htb'
  have htb'mem : tb' ∈ (P : Subgroup (Sec5GBar Tb)) := by
    rw [hPimg, Sec5GImg]
    refine Subgroup.mem_map.2 ⟨⟨tb, Subgroup.subset_normalClosure htb⟩,
      Subgroup.mem_subgroupOf.2 htb, ?_⟩
    rw [htb']
  refine hAut (Sec5GBar Tb) P hD8 hshape tb' htb'mem ?_ ?_ (sec5op_act Tb g) ?_ ?_
    (by simpa only [htb'] using hfix)
  · rw [htb']; exact ht2
  · intro g' hg'
    rw [hPimg, Sec5GImg] at hg'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hg'
    rw [htb']
    simp only [← map_mul]
    exact congrArg (sec5g_pi Tb)
      (Subtype.ext (hc (a : X) (Subgroup.mem_subgroupOf.1 ha)))
  · exact Odd.of_dvd_nat hg (orderOf_map_dvd (sec5op_act Tb) g)
  · intro x hx
    rw [hPimg, Sec5GImg] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have h1 : sec5op_act Tb g (sec5g_pi Tb a) =
        sec5g_pi Tb (MulAut.conjNormal (H := normalClosure (Tb : Set X)) g a) := by
      change psiAut (normalClosure (Tb : Set X)) g (sec5g_pi Tb a) = _
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, psiAut_mk]
    have h2 : MulAut.conjNormal (H := normalClosure (Tb : Set X)) g a = a := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact hgT (a : X) (Subgroup.mem_subgroupOf.1 ha)
    rw [h1, h2]

end CFSG.OddStandard.SmallF3.Omega
