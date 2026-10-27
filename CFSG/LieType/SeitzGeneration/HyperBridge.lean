module

public import CFSG.LieType.SeitzGeneration.HyperLeaf
public import CFSG.LieType.Seitz.Defs

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LieType.Seitz

variable {Y : Type*} [Group Y]

@[expose] def actionImage (K : Subgroup Y) [K.Normal] (E : Subgroup Y) : Subgroup (MulAut K) :=
  E.map MulAut.conjNormal

theorem hyperGen_of_seitzHyperGamma (p : ℕ) (K E : Subgroup Y) [K.Normal]
    (h : seitzHyperGamma p (actionImage K E) = ⊤) : HyperGen p K E := by
  intro k hk
  have hk' : (⟨k, hk⟩ : K) ∈ seitzHyperGamma p (actionImage K E) := h ▸ Subgroup.mem_top _
  have hle : seitzHyperGamma p (actionImage K E) ≤ (Subgroup.closure {k : Y | k ∈ K ∧
      ∃ F : Subgroup Y, F ≤ E ∧ F.relIndex E = p ∧ ∀ f ∈ F, f * k = k * f}).comap K.subtype := by
    refine iSup₂_le fun F' hF' k₀ hk₀ => ?_
    apply Subgroup.subset_closure
    refine ⟨k₀.2, E ⊓ F'.comap MulAut.conjNormal, inf_le_left, ?_, fun f hf => ?_⟩
    · rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]
      exact hF'.2
    · have h1 := congrArg Subtype.val (hk₀ (MulAut.conjNormal f) hf.2)
      rw [MulAut.conjNormal_apply] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
  exact hle hk'

end CFSG.LieType.SeitzGeneration
