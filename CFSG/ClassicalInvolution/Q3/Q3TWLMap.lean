module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Universal.Spin.Chevalley.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin

variable {K : Type*} [Field K] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}

theorem spinAction_spinGroupMap (f : Q₁ →qᵢ Q₂) (x : spinGroup Q₁) (v : V₁) :
    spinAction Q₂ (f.spinGroupMap x) (f v) = f (spinAction Q₁ x v) := by
  apply ι_injective' Q₂
  have h2 := congrArg (CliffordAlgebra.map f) (ι_spinAction Q₁ x v)
  rw [map_mul, map_mul, CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι] at h2
  rw [ι_spinAction, h2, ← map_inv f.spinGroupMap x, QuadraticMap.Isometry.coe_spinGroupMap_apply,
    QuadraticMap.Isometry.coe_spinGroupMap_apply]

theorem ker_spinGroupMap_le_center (f : Q₁ →qᵢ Q₂) (hf : Function.Injective f) :
    f.spinGroupMap.ker ≤ Subgroup.center (spinGroup Q₁) := by
  intro x hx
  apply ker_spinAction_le_center Q₁
  rw [MonoidHom.mem_ker]
  refine LinearEquiv.ext fun v => hf ?_
  have h := spinAction_spinGroupMap f x v
  rw [MonoidHom.mem_ker.mp hx, map_one] at h
  exact h.symm

theorem spinGroupMap_comp_longRoot {n₁ n₂ : ℕ} (f : Q₁ →qᵢ Q₂) (F₁ : HypFrame Q₁ n₁)
    (F₂ : HypFrame Q₂ n₂) {i j : Fin n₁} {i' j' : Fin n₂} (hij : i ≠ j) (hij' : i' ≠ j')
    (s t : Bool) (hi : f (F₁.vec i s) = F₂.vec i' s) (hj : f (F₁.vec j t) = F₂.vec j' t) :
    f.spinGroupMap.comp (F₁.longRoot hij s t) = F₂.longRoot hij' s t := by
  refine MonoidHom.ext fun c => ?_
  rw [← ofAdd_toAdd c]
  apply Subtype.ext
  rw [MonoidHom.comp_apply, QuadraticMap.Isometry.coe_spinGroupMap_apply, F₁.coe_longRoot,
    F₂.coe_longRoot, map_add, map_one, map_smul, map_mul, CliffordAlgebra.map_apply_ι,
    CliffordAlgebra.map_apply_ι, hi, hj]

theorem spinGroupMap_comp_shortRoot {n₁ n₂ : ℕ} (f : Q₁ →qᵢ Q₂) (F₁ : OddFrame Q₁ n₁)
    (F₂ : OddFrame Q₂ n₂) (i : Fin n₁) (i' : Fin n₂) (s : Bool) (hz : f F₁.z = F₂.z)
    (hi : f (F₁.vec i s) = F₂.vec i' s) :
    f.spinGroupMap.comp (F₁.shortRoot i s) = F₂.shortRoot i' s := by
  refine MonoidHom.ext fun c => ?_
  rw [← ofAdd_toAdd c]
  apply Subtype.ext
  rw [MonoidHom.comp_apply, QuadraticMap.Isometry.coe_spinGroupMap_apply, F₁.coe_shortRoot,
    F₂.coe_shortRoot, map_add, map_one, map_smul, map_mul, CliffordAlgebra.map_apply_ι,
    CliffordAlgebra.map_apply_ι, hi, hz]

theorem map_range_eq_of_comp_eq {A B C : Type*} [Group A] [Group B] [Group C] (Θ : B →* C)
    (φ : A →* B) (ψ : A →* C) (h : Θ.comp φ = ψ) : φ.range.map Θ = ψ.range := by
  rw [MonoidHom.map_range, h]

theorem range_eq_iSup_of_map_eq {A B : Type*} [Group A] [Group B] {ι : Type*} (Θ : A →* B)
    (R₁ : ι → Subgroup A) (R₂ : ι → Subgroup B) (hgen : ⨆ i, R₁ i = ⊤)
    (hmap : ∀ i, (R₁ i).map Θ = R₂ i) : Θ.range = ⨆ i, R₂ i := by
  rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_iSup]
  exact iSup_congr hmap

end CFSG.ClassicalInvolution.Q3.Q3TW
