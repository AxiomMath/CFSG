module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieBase
public import CFSG.Sporadic.Schreier.TitsComponent
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Sporadic.Schreier.Tits CFSG.ComponentClassification.OuterAutomorphisms

theorem titsD_involutory_aut_inner
    (α : MulAut titsD) (hα : α * α = 1) :
    α ∈ inner titsD := by
  obtain ⟨hbij, -, hmap, -⟩ := CTUC_Tits_derived_full_automorphism_realization
  obtain ⟨a, rfl⟩ := hbij.2 α
  have haa : a * a = 1 := hbij.1 (by rw [map_mul, hα, map_one])
  by_cases ha1 : a = 1
  · rw [ha1, map_one]
    exact Subgroup.one_mem _
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (a : Equiv.Perm (Fin 1755)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [pow_two]; exact haa) ha1
    have hD := titsA_involution_mem_D a.2 hord
    rw [← hmap]
    exact ⟨a, Subgroup.mem_subgroupOf.mpr hD, rfl⟩

theorem tabIdentFor_tits
    : TabIdentFor @Ident.FamTits := by
  intro G _ _ X K t hs hX
  obtain ⟨hsimple, hmodel⟩ := hX
  obtain ⟨e⟩ := titsModelEquiv ↥X 2 1 hmodel
  exfalso
  exact hs.false_of_all_inner hsimple e titsD_involutory_aut_inner
    (fun y hy B => titsD_involution_centralizer_component_free y hy B)

end CFSG.QuasithinUnique.Id2519
