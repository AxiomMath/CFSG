
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneSylowPBase

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneGqFacts
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

section P

end P

section Conj

theorem not_two_dvd_index_Psub (u : Bool) : ¬ 2 ∣ ((Psub u).subgroupOf (Gq u)).index := by
  have h := Subgroup.index_mul_card ((Psub u).subgroupOf (Gq u))
  rw [card_Psub_subgroupOf, card_Gq] at h
  cases u <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h <;> omega

@[expose] def sylowP (u : Bool) : Sylow 2 (Gq u) :=
  (isPGroup_Psub u).toSylow (not_two_dvd_index_Psub u)

theorem exists_conj_le_Psub {u : Bool} {Q : Subgroup (Equiv.Perm (Fin 64))} (hQ : Q ≤ Gq u)
    (hQp : IsPGroup 2 Q) : ∃ g ∈ Gq u, ∀ σ ∈ Q, g * σ * g⁻¹ ∈ Psub u := by
  have hQ'p : IsPGroup 2 (Q.subgroupOf (Gq u)) :=
    hQp.comap_of_injective (Gq u).subtype (Subgroup.subtype_injective _)
  obtain ⟨S', hS'⟩ := hQ'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Gq u) (sylowP u) S'
  refine ⟨((g⁻¹ : Gq u) : Equiv.Perm (Fin 64)), (g⁻¹).2, fun σ hσ => ?_⟩
  have h1 : (⟨σ, hQ hσ⟩ : Gq u) ∈ (S' : Subgroup (Gq u)) := hS' (Subgroup.mem_subgroupOf.2 hσ)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : (g⁻¹ * ⟨σ, hQ hσ⟩ * g : Gq u) ∈ (Psub u).subgroupOf (Gq u) := by
    simpa [sylowP, MulAut.inv_def, MulAut.conj_symm_apply] using h1
  have h3 := Subgroup.mem_subgroupOf.1 h2
  simpa [mul_assoc] using h3

end Conj

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
