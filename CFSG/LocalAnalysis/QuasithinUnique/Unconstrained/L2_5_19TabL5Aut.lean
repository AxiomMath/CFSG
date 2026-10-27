module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL5Basic
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.L5

open Matrix
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBGraphForm

theorem proj_inj : Function.Injective (proj 5 (ZMod 2)) := by
  intro g h hgh
  have h1 : g⁻¹ * h ∈ scalars 5 (ZMod 2) := QuotientGroup.eq.1 hgh
  have h2 : g⁻¹ * h ∈ Subgroup.center S := by rw [← scalars_eq_center]; exact h1
  rw [center_S] at h2
  have h3 : g⁻¹ * h = 1 := h2
  calc g = g * 1 := (mul_one g).symm
    _ = g * (g⁻¹ * h) := by rw [h3]
    _ = h := by group

@[expose] noncomputable def projEquiv : S ≃* projectiveSL 5 (ZMod 2) :=
  { Equiv.ofBijective (proj 5 (ZMod 2)) ⟨proj_inj, proj_surjective 5 (ZMod 2)⟩ with
    map_mul' := map_mul _ }

theorem projEquiv_apply (g : S) : projEquiv g = proj 5 (ZMod 2) g := rfl

theorem field_trivial (σ : ZMod 2 ≃+* ZMod 2) : σ = 1 := by
  ext x
  fin_cases x
  · exact map_zero σ
  · exact map_one σ

noncomputable abbrev dl : MulAut S := slGraphAut 5 (ZMod 2)

theorem dl_apply (g : S) : dl g = (g⁻¹).transpose := rfl

theorem aut_form (α : MulAut S) :
    ∃ (a : S) (ε : ℕ), ε ≤ 1 ∧ α = MulAut.conj a * dl ^ ε := by
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := ZMod 2) (n := 5) (by norm_num)
  obtain ⟨A, σ, ε, hε, hβ⟩ := hgen ((MulAut.congr projEquiv) α)
  have hdet : (A : Matrix (Fin 5) (Fin 5) (ZMod 2)).det = 1 := by
    have hu : IsUnit (A : Matrix (Fin 5) (Fin 5) (ZMod 2)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
    obtain ⟨u, hu⟩ := hu
    have hu1 : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
    rw [← hu, hu1 u]
    rfl
  obtain ⟨a, ha⟩ : ∃ a : S, (a : Matrix (Fin 5) (Fin 5) (ZMod 2)) = A := ⟨⟨A, hdet⟩, rfl⟩
  have hA : Matrix.SpecialLinearGroup.toGL a = A := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact ha
  have hσ : σ = 1 := field_trivial σ
  refine ⟨a, ε, hε, ?_⟩
  have hδ : ∀ g : S, projEquiv (dl g) = dualAut 5 (ZMod 2) (projEquiv g) := by
    intro g
    rw [projEquiv_apply, projEquiv_apply, dualAut_proj]
    rfl
  have hc : ∀ g : S, (MulAut.congr projEquiv α) (projEquiv g) = projEquiv (α g) := by
    intro g
    simp [MulAut.congr_apply]
  have hβ' : (MulAut.congr projEquiv) α =
      MulAut.conj (projEquiv a) * dualAut 5 (ZMod 2) ^ ε := by
    rw [hβ, hσ, map_one, mul_one, ← hA, conjAut_toGL, projEquiv_apply]
  apply MulEquiv.ext
  intro g
  apply projEquiv.injective
  rw [← hc g, hβ']
  interval_cases ε
  · simp [MulAut.conj_apply, map_mul, map_inv]
  · simp only [pow_one, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    rw [← hδ]

end CFSG.QuasithinUnique.Id2519.Tab.L5
