module

public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.FixedPointFree
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.ComplementActsFreelyKernelCharacters
import CFSG.FeitThompson.Foundations.CoprimeActionFittingFaithful
import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open SemidirectProduct
open NormalInduction (conjClassFun conjClassFun_apply coe_conjNormal_inv)

variable {H E : Type*} [Group H] [Group E] {φ : E →* MulAut H}

instance instFintypeSemidirectProduct [Fintype H] [Fintype E] : Fintype (H ⋊[φ] E) :=
  Fintype.ofEquiv (H × E) equivProd.symm

instance instNormalRangeInl : ((inl : H →* H ⋊[φ] E).range).Normal := range_inl_normal

theorem index_range_inl : ((inl : H →* H ⋊[φ] E).range).index = Nat.card E := by
  rw [range_inl_eq_ker_rightHom, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ rightHom_surjective]
  simp

theorem mem_classFun_comp_mulEquiv {W : Type*} [Group W] {f : H → ℂ} (e : W ≃* H)
    (hf : f ∈ classFun H) : f ∘ e ∈ classFun W :=
  mem_classFun.2 fun _ _ h => mem_classFun.1 hf _ _ (MonoidHom.map_isConj (e : W →* H) h)

def kernelClassFun (φ : E →* MulAut H) (θ : H → ℂ) :
    ((inl : H →* H ⋊[φ] E).range) → ℂ := fun x => θ (x : H ⋊[φ] E).left

@[simp] theorem kernelClassFun_apply (θ : H → ℂ) (x : (inl : H →* H ⋊[φ] E).range) :
    kernelClassFun φ θ x = θ (x : H ⋊[φ] E).left := (rfl)

@[simp] theorem kernelClassFun_one (θ : H → ℂ) : kernelClassFun φ θ 1 = θ 1 := (rfl)

theorem kernelClassFun_injective : Function.Injective (kernelClassFun (H := H) (E := E) φ) := by
  intro θ ψ h
  funext x
  exact congrFun h ⟨inl x, ⟨x, rfl⟩⟩

noncomputable def mulEquivRangeInl (φ : E →* MulAut H) : H ≃* (inl : H →* H ⋊[φ] E).range :=
  MonoidHom.ofInjective inl_injective

theorem coe_mulEquivRangeInl_symm (x : (inl : H →* H ⋊[φ] E).range) :
    ((mulEquivRangeInl φ).symm x : H) = (x : H ⋊[φ] E).left := by
  apply inl_injective (φ := φ)
  have h1 : ((mulEquivRangeInl φ) ((mulEquivRangeInl φ).symm x) : H ⋊[φ] E) = (x : H ⋊[φ] E) := by
    rw [MulEquiv.apply_symm_apply]
  rw [show (inl ((mulEquivRangeInl φ).symm x) : H ⋊[φ] E)
      = ((mulEquivRangeInl φ) ((mulEquivRangeInl φ).symm x) : H ⋊[φ] E) from rfl, h1]
  obtain ⟨y, hy⟩ := x.2
  rw [← hy]
  simp

theorem kernelClassFun_eq_comp (θ : H → ℂ) :
    kernelClassFun φ θ = θ ∘ (mulEquivRangeInl φ).symm := by
  funext x
  rw [Function.comp_apply, kernelClassFun_apply, coe_mulEquivRangeInl_symm]

theorem kernelClassFun_mem_classFun {θ : H → ℂ} (hθ : θ ∈ classFun H) :
    kernelClassFun φ θ ∈ classFun ((inl : H →* H ⋊[φ] E).range) := by
  rw [kernelClassFun_eq_comp]
  exact mem_classFun_comp_mulEquiv _ hθ

theorem kernelClassFun_mem_Irr {θ : H → ℂ} (hθ : θ ∈ Irr H) :
    kernelClassFun φ θ ∈ Irr ((inl : H →* H ⋊[φ] E).range) := by
  have h : θ ∈ NormalInduction.irrChars H := by rw [normalInduction_irrChars_eq_Irr]; exact hθ
  have h2 := NormalInduction.mem_irrChars_comp_mulEquiv h (mulEquivRangeInl φ).symm
  rw [normalInduction_irrChars_eq_Irr] at h2
  rw [kernelClassFun_eq_comp]
  exact h2

theorem coe_conj_inr (u : E) (x : (inl : H →* H ⋊[φ] E).range) :
    ((inr u : H ⋊[φ] E)⁻¹ * (x : H ⋊[φ] E) * inr u) = inl ((φ u).symm (x : H ⋊[φ] E).left) := by
  obtain ⟨y, hy⟩ := x.2
  rw [← hy, show ((φ u).symm : H → H) (inl y : H ⋊[φ] E).left = ((φ u)⁻¹ : MulAut H) y from rfl,
    inl_aut_inv, ← map_inv]

theorem conjClassFun_inr_kernelClassFun (u : E) (θ : H → ℂ) :
    conjClassFun (inl : H →* H ⋊[φ] E).range (inr u) (kernelClassFun φ θ)
      = kernelClassFun φ (θ ∘ (φ u).symm) := by
  funext x
  rw [conjClassFun_apply, kernelClassFun_apply, kernelClassFun_apply, Function.comp_apply]
  have h : ((MulAut.conjNormal (inr u : H ⋊[φ] E)⁻¹ x : (inl : H →* H ⋊[φ] E).range)
      : H ⋊[φ] E) = inl ((φ u).symm (x : H ⋊[φ] E).left) := by
    rw [coe_conjNormal_inv]
    exact coe_conj_inr u x
  rw [h, left_inl]

theorem conjClassFun_kernelClassFun (t : H ⋊[φ] E) {θ : H → ℂ} (hθ : θ ∈ classFun H) :
    conjClassFun (inl : H →* H ⋊[φ] E).range t (kernelClassFun φ θ)
      = kernelClassFun φ (θ ∘ (φ t.right).symm) := by
  conv_lhs => rw [← inl_left_mul_inr_right t]
  rw [conjClassFun_mul, conjClassFun_inr_kernelClassFun]
  exact mem_inertiaGroup.1 (le_inertiaGroup ((inl : H →* H ⋊[φ] E).range)
    (kernelClassFun_mem_classFun (mem_classFun_comp_mulEquiv (φ t.right).symm hθ))
    ⟨t.left, rfl⟩)

theorem inertiaGroup_kernelClassFun [Finite H] [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) {θ : H → ℂ}
    (hθ : θ ∈ Irr H) (hθ1 : θ ≠ 1) :
    inertiaGroup ((inl : H →* H ⋊[φ] E).range) (kernelClassFun φ θ)
      = (inl : H →* H ⋊[φ] E).range := by
  refine le_antisymm (fun t ht => ?_)
    (le_inertiaGroup _ (kernelClassFun_mem_classFun (Irr_subset_classFun hθ)))
  rw [mem_inertiaGroup, conjClassFun_kernelClassFun t (Irr_subset_classFun hθ)] at ht
  have h1 : θ ∘ (φ t.right).symm = θ := kernelClassFun_injective ht
  have h2 : ∀ x : H, θ (φ t.right⁻¹ x) = θ x := by
    intro x
    have h := congrFun h1 x
    rwa [map_inv, show ((φ t.right)⁻¹ : MulAut H) x = (φ t.right).symm x from rfl]
  have h3 : t.right⁻¹ = 1 := eq_one_of_comp_eq_self_of_ne_one hφ hθ hθ1 h2
  rw [range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  simpa using inv_eq_one.1 h3

variable [Fintype H] [Fintype E]

theorem cfInner_self_indClassFun_kernelClassFun [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) {θ : H → ℂ}
    (hθ : θ ∈ Irr H) (hθ1 : θ ≠ 1) :
    cfInner (indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ))
        (indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ)) = 1 := by
  rw [cfInner_self_indClassFun _ (kernelClassFun_mem_Irr hθ),
    inertiaGroup_kernelClassFun hφ hθ hθ1, Subgroup.relIndex_self]
  simp

theorem indClassFun_kernelClassFun_mem_Irr [Nontrivial H]
    (hφ : ∀ v : E, v ≠ 1 → MonoidHom.FixedPointFree (φ v : H → H)) {θ : H → ℂ}
    (hθ : θ ∈ Irr H) (hθ1 : θ ≠ 1) :
    indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ) ∈ Irr (H ⋊[φ] E) := by
  obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_of_mem_indFam
    ((inl : H →* H ⋊[φ] E).range)
    ((mem_indFam _).2 ⟨kernelClassFun φ θ, kernelClassFun_mem_Irr hθ, rfl⟩)
  refine mem_Irr.2 ⟨W, ?_, hW⟩
  rw [isIrreducible_iff_cfInner_self_eq_one, ← fdRepCharacter_eq W, hW]
  exact cfInner_self_indClassFun_kernelClassFun hφ hθ hθ1

theorem indClassFun_kernelClassFun_one (θ : H → ℂ) :
    indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ) 1
      = (Nat.card E : ℂ) * θ 1 := by
  rw [NormalInducedFamily.indClassFun_one_eq_index_mul, index_range_inl, kernelClassFun_one]

theorem indClassFun_kernelClassFun_eq_iff {θ ψ : H → ℂ} (hθ : θ ∈ Irr H) (hψ : ψ ∈ Irr H) :
    indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ θ)
        = indClassFun (inl : H →* H ⋊[φ] E).range (kernelClassFun φ ψ)
      ↔ ∃ u : E, ψ ∘ (φ u) = θ := by
  rw [NormalInducedFamily.indClassFun_eq_iff_exists_conjClassFun _
    (kernelClassFun_mem_Irr hθ) (kernelClassFun_mem_Irr hψ)]
  constructor
  · rintro ⟨t, ht⟩
    rw [conjClassFun_kernelClassFun t (Irr_subset_classFun hψ)] at ht
    refine ⟨t.right⁻¹, ?_⟩
    have h := kernelClassFun_injective ht
    rw [map_inv]
    exact h
  · rintro ⟨u, hu⟩
    refine ⟨inr u⁻¹, ?_⟩
    rw [conjClassFun_kernelClassFun _ (Irr_subset_classFun hψ), right_inr]
    congr 1
    rw [map_inv]
    exact hu

end CFSG.FeitThompson
