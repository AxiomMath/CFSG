module

public import CFSG.LocalAnalysis.EvenBN.GMS.LocalSelection
public import CFSG.LocalAnalysis.EvenBN.GMS.StrongClosure

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open Subgroup
open scoped MatrixGroups

namespace LocalSetting

variable {H : Type} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}


theorem layer_selection (h : LocalSetting A t U V D n) (hF : LocalFieldBound A t n) :
        centralizer (CFSG.layer H : Set H) = ⊥ ∧ A ≤ CFSG.layer H ∧
      CFSG.layer H = normalClosure (A : Set H) ∧ V ≤ CFSG.layer H ∧
      Xor
        (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ n ∧
          ∃ (ψ : CFSG.layer H ≃* SL(2, k) × SL(2, k)) (α : A ≃* SL(2, k)),
            (∀ (a : A) (x : CFSG.layer H), (x : H) = a → ψ x = (α a, α a)) ∧
            ∀ (x y : CFSG.layer H) (y₁ y₂ : SL(2, k)), (y : H) = t⁻¹ * x * t →
              ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
        (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 ∧
          ∃ ψ : CFSG.layer H ≃* SL(2, k₂),
            (∀ x y : CFSG.layer H, (y : H) = t⁻¹ * x * t →
              ((ψ y : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
                (ψ x : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ n)) ∧
            ∀ g : SL(2, k₂), g ∈ (A.subgroupOf (CFSG.layer H)).map ψ.toMonoidHom ↔
              ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ n =
                (g : Matrix (Fin 2) (Fin 2) k₂) i j)  := by
  obtain ⟨S, hVS, hclosed⟩ := h.exists_sylow_stronglyClosed hF
  exact h.layer_selection_of_stronglyClosed S hVS hclosed

end LocalSetting

end CFSG.LocalAnalysis.EvenBN.GMS
