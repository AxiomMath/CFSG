module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4C
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4N2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag BS4
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open scoped commutatorElement

variable {F : Type} [Field F] {W I : Subgroup (projectiveSL 4 F)}

abbrev Hc (I : Subgroup (projectiveSL 4 F)) : Subgroup (GL (Fin 4) F) :=
  ⁅I.comap (proj 4 F), I.comap (proj 4 F)⁆.map SpecialLinearGroup.toGL

theorem false_of_comm (hI : ⁅I, I⁆ = I) (hIne : I ≠ ⊥)
    (hc : ∀ z ∈ ⁅Hc I, Hc I⁆, ∀ w ∈ ⁅Hc I, Hc I⁆, z * w = w * z) : False := by
  have hD := comm_of_map (φ := SpecialLinearGroup.toGL)
    SpecialLinearGroup.toGL_injective hc
  have hπ : (⁅⁅I.comap (proj 4 F), I.comap (proj 4 F)⁆,
      ⁅I.comap (proj 4 F), I.comap (proj 4 F)⁆⁆).map (proj 4 F) = I := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      map_comap_eq_self_of_surjective (proj_surjective 4 F), hI, hI]
  apply hIne
  rw [← hI, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  rw [← hπ] at ha hb
  obtain ⟨d, hd, rfl⟩ := hb
  obtain ⟨d', hd', rfl⟩ := ha
  rw [← map_mul, ← map_mul, hD d hd d' hd']

theorem stab_of_mem_Hc [Finite F] {N : Submodule F (Fin 4 → F)}
    (hIW : I ≤ normalizer (W : Set (projectiveSL 4 F)))
    (hN : ∀ A : GL (Fin 4) F,
      A ∈ normalizer ((preGL W : Subgroup (GL (Fin 4) F)) : Set (GL (Fin 4) F)) →
        ∀ v ∈ N, (A : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N) :
    ∀ x ∈ Hc I, ∀ v ∈ N, (x : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N := by
  rintro _ ⟨s, hs, rfl⟩
  have hsI : proj 4 F s ∈ I := Subgroup.commutator_le_self (I.comap (proj 4 F)) hs
  exact hN _ (mem_normalizer_preGL_of_proj fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hIW hsI) w).mp hw)

theorem comm_of_lin {A : GL (Fin 4) F} (hA : ∀ x ∈ I, conjAut 4 F A x = x) :
    ∀ x ∈ Hc I, A * x = x * A := by
  rintro _ ⟨s, hs, rfl⟩
  have h := eq_of_mem_commutator (φ := (slConjugation 4 F A).toMonoidHom)
    (fun t ht => by
      rw [MulEquiv.coe_toMonoidHom, ← conjAut_proj]
      exact hA _ ht) s hs
  have e := congrArg SpecialLinearGroup.toGL h
  rw [MulEquiv.coe_toMonoidHom, toGL_slConjugation] at e
  calc A * SpecialLinearGroup.toGL s
      = A * SpecialLinearGroup.toGL s * A⁻¹ * A := by group
    _ = SpecialLinearGroup.toGL s * A := by rw [e]

theorem form_of_graph {A : GL (Fin 4) F}
    (hA : ∀ x ∈ I, (conjAut 4 F A * dualAut 4 F) x = x) :
    ∀ x ∈ Hc I, (x : Matrix (Fin 4) (Fin 4) F)ᵀ *
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) =
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rintro _ ⟨s, hs, rfl⟩
  have h := eq_of_mem_commutator
    (φ := (slConjugation 4 F A).toMonoidHom.comp (slGraphAut 4 F).toMonoidHom)
    (fun t ht => by
      have := hA _ ht
      rwa [MulAut.mul_apply, dualAut_proj, conjAut_proj] at this) s hs
  exact transpose_mul_of_graph h

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
