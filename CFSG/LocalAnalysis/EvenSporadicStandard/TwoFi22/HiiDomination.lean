module

public import CFSG.Sporadic.Fi22.LH.Xi

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_commute_of_mem_lhOrbit
    {i : Fin 2} {T : Set D} (hT : T ∈ lhOrbit i) (f : D) : ∃ x ∈ T, (f : J) * x = x * f := by
  by_cases hfT : f ∈ T
  · exact ⟨f, hfT, rfl⟩
  obtain ⟨g, rfl⟩ := hT
  have hf' := notMem_conjPerm_image hfT
  obtain ⟨k, hk⟩ := ptD.surjective ((Pair.conjPerm pair_D g).symm f)
  rw [← hk] at hf'
  have hkB : bitAt lhc.B[i.val]! k.val = false := by
    rw [ptD_mem_lhRoot] at hf'
    simpa using hf'
  obtain ⟨⟨x, hx, hxB, hxc⟩, -⟩ := domOK_spec
    (lh_parts.2.2.2.2.2.2.2.2.2.1 i.val i.2).2.2.2.2.2.1 k.2 hkB
  refine ⟨Pair.conjPerm pair_D g (ptD ⟨x, hx⟩), ⟨ptD ⟨x, hx⟩, ptD_mem_lhRoot.2 hxB, rfl⟩, ?_⟩
  have hfk : f = Pair.conjPerm pair_D g (ptD k) := by
    rw [hk, Equiv.apply_symm_apply]
  rw [hfk, conjPerm_commute_iff]
  exact (ptD_commute_iff k ⟨x, hx⟩).2 hxc

end CFSG.Sporadic.Fi22
