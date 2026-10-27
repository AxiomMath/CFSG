module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F11
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Dictionary
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F11.Pin
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F11.Rigid
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelCd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUnique
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueIndex

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.Sporadic.Fi23 (Cd card_centralizer_d)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem sq_eq_one_of_mem_E0
    {y : Q3} (hy : y ∈ E0) :
    y ^ 2 = 1 := by
  obtain ⟨m, -, rfl⟩ := exists_epsMask_of_mem_E0 hy
  rw [sq]
  exact epsMask_mul_self m

theorem exists_equiv_Cd_mem_E0_iff :
    ∃ ψ : ↥L0 ≃* ↥Cd, ∀ x : ↥L0, (x : Q3) ∈ E0 ↔ ψ x ∈ DS81.E0 := by
  obtain ⟨ψ₀⟩ := L0_equiv_Cd
  haveI : Finite ↥Cd := Nat.finite_of_card_ne_zero (by
    have h : Nat.card ↥Cd = 129123503308800 := card_centralizer_d
    omega)
  have hsq : ∀ x ∈ E0.subgroupOf L0, x ^ 2 = 1 := by
    intro x hx
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact sq_eq_one_of_mem_E0 (Subgroup.mem_subgroupOf.1 hx)
  have hcard : Nat.card ↥(E0.subgroupOf L0) = 2 ^ 11 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E0_le_B0.trans B0_le_L0)).toEquiv).trans
      card_E0
  obtain ⟨ψ, hψ⟩ := @exists_equiv_mem_iff_of_odd_index_normalizer ↥L0 ↥Cd inferInstance
    inferInstance inferInstance ψ₀ (E0.subgroupOf L0) DS81.E0 (2 ^ 11) DS81.E0_odd_index hsq hcard
    DS81.E0_unique
  exact ⟨ψ, fun x => Subgroup.mem_subgroupOf.symm.trans (hψ x)⟩

theorem center_L0_le_E0 :
    Subgroup.center ↥L0 ≤ E0.subgroupOf L0 := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_Cd_mem_E0_iff
  exact @center_le_of_equiv ↥L0 ↥Cd inferInstance inferInstance ψ (E0.subgroupOf L0) DS81.E0
    (fun x => Subgroup.mem_subgroupOf.trans (hψ x)) DS81.E0_center_le

theorem mem_E0_of_mem_center_L0
    {z : ↥L0}
    (hz : z ∈ Subgroup.center ↥L0) : (z : Q3) ∈ E0 :=
  Subgroup.mem_subgroupOf.1 (center_L0_le_E0 hz)

theorem mem_center_L0_iff
    {z : ↥L0} :
    z ∈ Subgroup.center ↥L0 ↔ (z : Q3) = 1 ∨ (z : Q3) = t0 := by
  have key : ∀ z : ↥L0, z ∈ Subgroup.center ↥L0 → (z : Q3) = 1 ∨ (z : Q3) = t0 := by
    intro z hz
    refine eq_of_mem_E0_of_commute_B0 (mem_E0_of_mem_center_L0 hz) fun b hb => ?_
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨b, B0_le_L0 hb⟩)
  refine ⟨key z, fun h => ?_⟩
  have hcard : Nat.card ↥(Subgroup.center ↥L0) = 2 := card_center_L0
  haveI : Finite ↥(Subgroup.center ↥L0) := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial ↥(Subgroup.center ↥L0) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨z0, hz0⟩ := exists_ne (1 : ↥(Subgroup.center ↥L0))
  have hz0' : ((z0 : ↥L0) : Q3) ≠ 1 := fun h' => hz0 (Subtype.ext (Subtype.ext h'))
  have hz0t : ((z0 : ↥L0) : Q3) = t0 := (key z0 z0.2).resolve_left hz0'
  rcases h with h | h
  · rw [show z = 1 from Subtype.ext h]
    exact one_mem _
  · rw [show z = z0 from Subtype.ext (h.trans hz0t.symm)]
    exact z0.2

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
