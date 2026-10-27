module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBasic

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.LocalCores CFSG.QuasithinUnique
open scoped commutatorElement

theorem exists_mul_of_mem_sup_of_normalizer {X : Type*} [Group X] {L A : Subgroup X}
    (hAn : A ≤ Subgroup.normalizer (L : Set X)) {x : X} (hx : x ∈ L ⊔ A) :
    ∃ l ∈ L, ∃ a ∈ A, x = l * a := by
  let S : Subgroup X :=
    { carrier := {x | ∃ l ∈ L, ∃ a ∈ A, x = l * a}
      one_mem' := ⟨1, L.one_mem, 1, A.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, a₁, ha₁, rfl⟩ ⟨l₂, hl₂, a₂, ha₂, rfl⟩
        refine ⟨l₁ * (a₁ * l₂ * a₁⁻¹),
          L.mul_mem hl₁ (Layer.conj_mem_of_mem_normalizer (hAn ha₁) hl₂), a₁ * a₂,
          A.mul_mem ha₁ ha₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨l, hl, a, ha, rfl⟩
        refine ⟨a⁻¹ * l⁻¹ * a, Layer.conj_inv_mem_of_mem_normalizer (hAn ha) (L.inv_mem hl), a⁻¹,
          A.inv_mem ha, ?_⟩
        group }
  have hle : L ⊔ A ≤ S := sup_le (fun l hl => ⟨l, hl, 1, A.one_mem, (mul_one l).symm⟩)
    (fun a ha => ⟨1, L.one_mem, a, ha, (one_mul a).symm⟩)
  exact hle hx

end CFSG.QuasithinUnique.Setup.Family
