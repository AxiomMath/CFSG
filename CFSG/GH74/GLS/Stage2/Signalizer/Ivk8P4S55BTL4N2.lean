module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4N
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenB

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

variable {F : Type} [Field F] [Finite F] {p : ℕ} {W : Subgroup (projectiveSL 4 F)}

theorem mem_normalizer_preGL_of_conjAut {A : GL (Fin 4) F}
    (hA : ∀ w ∈ W, conjAut 4 F A w ∈ W) :
    A ∈ normalizer ((preGL W : Subgroup (GL (Fin 4) F)) : Set _) := by
  refine mem_normalizer_of_conj_le fun x hx => ?_
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨slConjugation 4 F A s, ?_, toGL_slConjugation 4 F A s⟩
  show proj 4 F (slConjugation 4 F A s) ∈ W
  rw [← conjAut_proj]
  exact hA _ hs

theorem mem_normalizer_preGL_of_proj {g : SpecialLinearGroup (Fin 4) F}
    (hg : ∀ w ∈ W, proj 4 F g * w * (proj 4 F g)⁻¹ ∈ W) :
    SpecialLinearGroup.toGL g ∈ normalizer ((preGL W : Subgroup (GL (Fin 4) F)) : Set _) := by
  refine mem_normalizer_of_conj_le fun x hx => ?_
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨g * s * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  show proj 4 F (g * s * g⁻¹) ∈ W
  rw [map_mul, map_mul, map_inv]
  exact hg _ hs

omit [Finite F] in
theorem isPElt_graph {A : GL (Fin 4) F} (hA : ∀ w ∈ W, (conjAut 4 F A * dualAut 4 F) w ∈ W) :
    ∀ x, IsPElt p W x → ∃ y, IsPElt p W y ∧ (y : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) * ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rintro _ ⟨⟨s, hs, rfl⟩, n, hn⟩
  set t := slConjugation 4 F A (slGraphAut 4 F s) with ht
  have hsn : s ^ p ^ n = 1 :=
    SpecialLinearGroup.toGL_injective (by rw [map_pow, hn, map_one])
  refine ⟨SpecialLinearGroup.toGL t, ⟨⟨t, ?_, rfl⟩, n, ?_⟩, ?_⟩
  · show proj 4 F t ∈ W
    rw [ht, ← conjAut_proj]
    have := hA _ hs
    rwa [MulAut.mul_apply, dualAut_proj] at this
  · rw [← map_pow, ht, ← map_pow, ← map_pow, hsn, map_one, map_one, map_one]
  · rw [SpecialLinearGroup.coe_GL_coe_matrix, ht, coe_slConjugation, ← map_inv]
    rfl

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
