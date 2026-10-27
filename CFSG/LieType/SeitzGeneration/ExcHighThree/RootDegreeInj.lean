module

public import CFSG.LieType.Chevalley.ProductInjectivity

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}


theorem pinnedX_list_prod_injective_deg {R : Type} [CommRing R]
    (φ : (Fin τ.rank → ℤ) →+ ℤ) (L : List (Fin τ.rank → ℤ))
    (hnd : L.Nodup) (hL : ∀ α ∈ L, IsRoot τ α ∧ 0 < φ α) (c c' : (Fin τ.rank → ℤ) → R)
    (heq : (L.map fun α => pinnedX τ R α (c α)).prod =
      (L.map fun α => pinnedX τ R α (c' α)).prod) :
    ∀ α ∈ L, c α = c' α := by
  have h := congrArg (fun g : (Module.End R (RootModule τ R))ˣ =>
    (g : Module.End R (RootModule τ R))) heq
  rw [coe_list_prod_pinnedX c L fun α hα => (hL α hα).1,
    coe_list_prod_pinnedX c' L fun α hα => (hL α hα).1] at h
  have key := RootOperatorFamily.prod_eltOr_injective_of_ring (rootOperatorFamily τ) (φ := φ)
    L hnd hL _ _ h
  intro α hα
  have h1 := congrArg (((rootOperatorFamily τ).pinnedFamilySign α : R) * ·) (key α hα)
  simp only [← mul_assoc, (rootOperatorFamily τ).pinnedFamilySign_mul_self, one_mul] at h1
  exact h1

theorem prod_ne_one_of_degree_pos {R : Type} [CommRing R] [Nontrivial R]
    (φ : (Fin τ.rank → ℤ) →+ ℤ) {n : ℕ}
    (γ : Fin n → Fin τ.rank → ℤ) (hγ : Function.Injective γ)
    (hpos : ∀ i, IsRoot τ (γ i) ∧ 0 < φ (γ i)) (c : Fin n → R) (i0 : Fin n) (hc : c i0 ≠ 0) :
    (List.ofFn fun i => pinnedX τ R (γ i) (c i)).prod ≠ 1 := by
  have hL : ∀ α ∈ List.ofFn γ, IsRoot τ α ∧ 0 < φ α := by
    intro α hα
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hα
    exact hpos i
  have hprod : ∀ d : Fin n → R, (List.ofFn fun i => pinnedX τ R (γ i) (d i)) =
      (List.ofFn γ).map fun α => pinnedX τ R α (Function.extend γ d 0 α) := by
    intro d
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply, hγ.extend_apply]
  intro h
  have heq : ((List.ofFn γ).map fun α => pinnedX τ R α (Function.extend γ c 0 α)).prod =
      ((List.ofFn γ).map fun α => pinnedX τ R α ((fun _ => (0 : R)) α)).prod := by
    rw [← hprod c, h]
    simp only [pinnedX_zero, List.map_const', List.prod_replicate, one_pow]
  refine hc ?_
  have := pinnedX_list_prod_injective_deg φ (List.ofFn γ) (List.nodup_ofFn.2 hγ) hL
    (Function.extend γ c 0) (fun _ => (0 : R)) heq (γ i0) (List.mem_ofFn.2 ⟨i0, rfl⟩)
  simpa [hγ.extend_apply] using this

end CFSG.LieType.SeitzGeneration.ExcHighThree
