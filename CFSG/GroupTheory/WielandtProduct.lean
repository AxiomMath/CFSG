module

public import CFSG.GroupTheory.WielandtProductFinal
public import CFSG.Quasithin.Vol2.Ch4Sec4Inputs

public section

namespace CFSG.Quasithin.H13

open scoped Pointwise

theorem wielandtCoprimeProduct_holds : WielandtCoprimeProduct := by
  intro G _ _ A B hA hB hcop hAB
  refine CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product A B hA hB hcop fun g => ?_
  have hg : g ∈ (A : Set G) * (B : Set G) := hAB ▸ Set.mem_univ g
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hg
  exact ⟨a, ha, b, hb, rfl⟩

end CFSG.Quasithin.H13
