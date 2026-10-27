module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.SplusRange
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.Splus

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.S25

open Subgroup

theorem splusFact_of_noLiftV4 {H : Type*} [Group H] [Finite H] {z : H} {R0 : Subgroup H}
    (hzR : z ∈ R0) (hR0 : IsPGroup 2 R0)
    {ψ : ↥(centralizer ({z} : Set H)) →* Equiv.Perm (Fin 5)}
    (hker : ψ.ker = R0.subgroupOf (centralizer ({z} : Set H))) (hno : NoLiftV4 z ψ) :
    SplusFact z := by
  intro Y hY hperf f hf hfk
  let ψY : ↥Y →* Equiv.Perm (Fin 5) := ψ.comp (Subgroup.inclusion hY)
  have hn : ψY.ker = f.ker := ker_comp_inclusion_eq hzR hR0 hker hY hf hfk
  have hr : ψY.range = alternatingGroup (Fin 5) :=
    range_comp_inclusion_eq hzR hR0 hker hY hperf hf hfk
  obtain ⟨u0, hu0⟩ := MonoidHom.mem_range.mp (by rw [hr]; exact a1_mem)
  obtain ⟨v0, hv0⟩ := MonoidHom.mem_range.mp (by rw [hr]; exact a2_mem)
  have hcomm : a1 * a2 * a1⁻¹ * a2⁻¹ = 1 := by
    rw [inv_eq_of_mul_eq_one_right a1_sq, inv_eq_of_mul_eq_one_right a2_sq, a1_a2_comm,
      mul_assoc a2 a1 a1, a1_sq, mul_one, a2_sq]
  refine hno (Subgroup.inclusion hY u0) (Subgroup.inclusion hY v0) hu0 hv0 ?_ ?_ ?_
  · have hk : u0 ^ 2 ∈ ψY.ker := by
      rw [MonoidHom.mem_ker, map_pow, hu0, pow_two, a1_sq]
    have hfk' : u0 ^ 2 ∈ (zpowers z).subgroupOf Y := hfk (hn ▸ hk)
    simpa [Subgroup.coe_pow, Subgroup.coe_inclusion] using Subgroup.mem_subgroupOf.mp hfk'
  · have hk : v0 ^ 2 ∈ ψY.ker := by
      rw [MonoidHom.mem_ker, map_pow, hv0, pow_two, a2_sq]
    have hfk' : v0 ^ 2 ∈ (zpowers z).subgroupOf Y := hfk (hn ▸ hk)
    simpa [Subgroup.coe_pow, Subgroup.coe_inclusion] using Subgroup.mem_subgroupOf.mp hfk'
  · have hk : u0 * v0 * u0⁻¹ * v0⁻¹ ∈ ψY.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hu0, hv0]
      exact hcomm
    have hfk' : u0 * v0 * u0⁻¹ * v0⁻¹ ∈ (zpowers z).subgroupOf Y := hfk (hn ▸ hk)
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] using
      Subgroup.mem_subgroupOf.mp hfk'

end CFSG.EvenSporadicStandard.HNRecog.Harada.S25
