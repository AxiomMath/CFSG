module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore

public noncomputable section

namespace CFSG.HardMathSupport.Lang.D4Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang

variable {K : Type} [Field K]

theorem rootDiagUnit_sq_mem_adjointGroup_D4 (b : Fin 4 → Kˣ) :
    rootDiagUnit Tag.D4 (fun j : Fin 4 => b j ^ 2) ∈ adjointGroup Tag.D4 K := by
  set c : Fin 4 → Kˣ := ![b 0 ^ 2 * b 1 * b 2 ^ 2 * b 3, b 0 * b 1 ^ 2 * b 2 ^ 2 * b 3,
    b 0 ^ 2 * b 1 ^ 2 * b 2 ^ 4 * b 3 ^ 2, b 0 * b 1 * b 2 ^ 2 * b 3 ^ 2] with hc
  have hprod := list_prod_torusElt_eq_rootDiagUnit (τ := Tag.D4) (K := K) c
  have hmem : ((List.finRange Tag.D4.rank).map fun j => torusElt Tag.D4 K j (c j)).prod ∈
      adjointGroup Tag.D4 K := by
    refine list_prod_mem fun x hx => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact torusElt_mem_adjointGroup j (c j)
  rw [hprod] at hmem
  set Acar : Matrix (Fin 4) (Fin 4) ℤ := Tag.D4.cartan with hAcar
  have hcartan : ∀ l : Fin 4, (cartanChar (τ := Tag.D4) c) l = c 0 ^ (Acar 0 l) *
      c 1 ^ (Acar 1 l) * c 2 ^ (Acar 2 l) * c 3 ^ (Acar 3 l) := by
    intro l
    exact Fin.prod_univ_four (fun j : Fin 4 => c j ^ (Acar j l))
  have heq : (fun j : Fin 4 => b j ^ 2) = cartanChar (τ := Tag.D4) c := by
    funext l
    rw [hcartan l]
    apply Additive.ofMul.injective
    have hA : Acar = !![2, 0, -1, 0; 0, 2, -1, 0; -1, -1, 2, -1; 0, 0, -1, 2] := rfl
    fin_cases l <;>
      simp [hc, hA] <;> module
  rw [heq]
  exact hmem

theorem sq_mem_adjointGroup_of_mem_inndiagGroup {γ : ModGL Tag.D4 K}
    (hγ : γ ∈ inndiagGroup Tag.D4 K) : γ ^ 2 ∈ adjointGroup Tag.D4 K := by
  obtain ⟨b, j, hj, rfl⟩ := hγ
  have h1 : (rootDiagUnit Tag.D4 b)⁻¹ * j * rootDiagUnit Tag.D4 b ∈ adjointGroup Tag.D4 K := by
    have := conj_rootDiagUnit_mem_adjointGroup (τ := Tag.D4) (K := K) b⁻¹ hj
    rwa [← rootDiagUnit_inv, inv_inv] at this
  have h2 : rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 b ∈ adjointGroup Tag.D4 K := by
    have hbb : b * b = fun j : Fin 4 => b j ^ 2 := funext fun l => (pow_two (b l)).symm
    rw [← rootDiagUnit_mul, hbb]
    exact rootDiagUnit_sq_mem_adjointGroup_D4 (K := K) b
  have e : (rootDiagUnit Tag.D4 b * j) ^ 2 = (rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 b) *
      ((rootDiagUnit Tag.D4 b)⁻¹ * j * rootDiagUnit Tag.D4 b) * j := by
    rw [pow_two]
    group
  rw [e]
  exact mul_mem (mul_mem h2 h1) hj

end CFSG.HardMathSupport.Lang.D4Three
