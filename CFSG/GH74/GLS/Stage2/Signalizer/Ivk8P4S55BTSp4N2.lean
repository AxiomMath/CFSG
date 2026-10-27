module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4N

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BS4

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {F : Type} [Field F] [Finite F] {p : ℕ} {W : Subgroup (StatedProj (StatedSp 2 F))}

theorem mem_normalizer_preGL {A : GL (Fin 2 ⊕ Fin 2) F}
    (h : ∀ s : StatedSp 2 F, proj 2 F s ∈ W → ∃ t : StatedSp 2 F, proj 2 F t ∈ W ∧
      (t : GL (Fin 2 ⊕ Fin 2) F) = A * s * A⁻¹) :
    A ∈ normalizer ((preGL W : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) : Set _) := by
  refine mem_normalizer_of_conj_le fun x hx => ?_
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, hte⟩ := h s hs
  exact ⟨t, ht, hte⟩

theorem mem_normalizer_preGL_of_conjAut {A : gsp 2 F} (hA : ∀ w ∈ W, conjAut 2 F A w ∈ W) :
    (A : GL (Fin 2 ⊕ Fin 2) F) ∈ normalizer ((preGL W : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) :
      Set _) :=
  mem_normalizer_preGL fun s hs => ⟨conjSp 2 F A s, by rw [← conjAut_proj]; exact hA _ hs,
    coe_conjSp A s⟩

theorem mem_normalizer_preGL_of_proj {g : StatedSp 2 F}
    (hg : ∀ w ∈ W, proj 2 F g * w * (proj 2 F g)⁻¹ ∈ W) :
    (g : GL (Fin 2 ⊕ Fin 2) F) ∈ normalizer ((preGL W : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) :
      Set _) :=
  mem_normalizer_preGL fun s hs => ⟨g * s * g⁻¹, by
    rw [map_mul, map_mul, map_inv]; exact hg _ hs, rfl⟩

variable [Fact p.Prime] [CharP F p]

theorem exists_isotropic_subspace (hp2 : p ≠ 2) (hW : W ≠ ⊥) (hWp : IsPGroup p ↥W) :
    ∃ N : Submodule F (Fin 2 ⊕ Fin 2 → F), N ≠ ⊥ ∧ IsTotallyIsotropic (pairedSympForm F 2) N ∧
      ∀ A : GL (Fin 2 ⊕ Fin 2) F,
        A ∈ normalizer ((preGL W : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) : Set (GL (Fin 2 ⊕ Fin 2) F)) →
          ∀ v ∈ N, (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈ N := by
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem hp2 hW hWp
  refine ⟨fixSp p W ⊓ comSp p W, fun h => hv0 (by rw [h] at hv; exact hv),
    fun x hx y hy => pairedSympForm_fixSp_comSp hx.1 hy.2, fun A hA u hu =>
      ⟨mulVec_mem_fixSp hA hu.1, mulVec_mem_comSp hA hu.2⟩⟩

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
