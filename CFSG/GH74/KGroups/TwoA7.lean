module

public import CFSG.GH74.GLS.IVK.Lifted.TwoA7
public import CFSG.GH74.KGroups.TwoA7NotF
public import CFSG.GH74.KGroups.TwoA7Syl
public import CFSG.GH74.KGroups.TwoA7Main
public import CFSG.GH74.KGroups.TwoA7CompSwap
public import CFSG.GH74.KGroups.TwoA7CompThree
public import CFSG.GH74.KGroups.TwoA7Four

public section

namespace CFSG.GH74.KGroups.TwoA7

open CFSG CFSG.ClassicalInvolution.Hat2A7 Equiv Equiv.Perm Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm2.Recip

section Final

variable {E : Type} [Group E] [Finite E] {π : E →* A7} {z : E}

theorem conj3
    (h : IsDoubleCoverA7 π z) (hq : CFSG.IsQuasisimple E) (φ : MulAut E)
    (hφ2 : φ * φ = 1) (hout : φ ∉ innOf E) (hK : IsKGroupNative E) : IsFAutomorphism E φ := by
  have hφ1 : φ ≠ 1 := fun h1 => hout (h1 ▸ Subgroup.one_mem _)
  have hord : orderOf φ = 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hφ2) hφ1
  refine ⟨hq, hK, pRank_eq_one h, ⟨1, hord⟩, ?_⟩
  rcases outer_involution_cases h φ hφ2 hout with hs | h3
  · exact Or.inl (exists_pComponent_swap h φ hs)
  · exact Or.inr (hasSolvableTwoComponentSL23_fixed h φ h3)

theorem conj7
    (h : IsDoubleCoverA7 π z) (hcen : ∀ w : E, w ∈ Subgroup.center E ↔ (w = 1 ∨ w = z))
    (φ : MulAut E) (hf : IsFAutomorphism E φ) (hφ1 : φ ≠ 1) (P : Subgroup E)
    (hP : CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In P ⊤) (hinv : ∀ p ∈ P, φ p ∈ P) :
    ∃ y ∈ P, orderOf y = 4 ∧ φ y = y := by
  have hφ2 := conj2 h hcen φ hf
  have hout : φ ∉ innOf E := by
    rintro ⟨q, rfl⟩
    by_cases hq : q ∈ Subgroup.center E
    · apply hφ1
      ext x
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [← Subgroup.mem_center_iff.1 hq x, mul_inv_cancel_right]
    · exact conj1 h hcen q hq hf
  exact four_fixed h φ hφ2 hout P hP hinv

end Final

theorem ii4_2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7 := by
  intro Q _ _ hQ
  obtain ⟨π, z, h, hcen⟩ := exists_cover hQ
  exact ⟨fun c hc => conj1 h hcen c hc, fun φ hφ => conj2 h hcen φ hφ,
    fun φ hφ2 hout hK => conj3 h hQ.1 φ hφ2 hout hK, index_innOf h, fun T => conj5 h T,
    fun c hc hcc W hW hWc => conj6 h hcen c hc hcc W hW hWc,
    fun φ hf hφ1 P hP hinv => conj7 h hcen φ hf hφ1 P hP hinv⟩

end CFSG.GH74.KGroups.TwoA7
