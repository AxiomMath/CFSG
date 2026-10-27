module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleTools
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddOrbitWitness

public section

namespace CFSG.ComponentClassification.GrSLit.Single

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem not_le_coreActionKernel_of_diagonal {a : X} {J K M : Subgroup X}
    (hJa : J ≤ centralizer ({a} : Set X)) (hJc : IsPComponent 2 (J.subgroupOf
      (centralizer ({a} : Set X)))) (hJM : J ≤ M) (hKM : K ≤ M) (hK'M : conjugate K a ≤ M)
    (hJNK : J ≤ normalizer (K : Set X)) (hJNK' : J ≤ normalizer ((conjugate K a : Subgroup X) :
      Set X))
    (hOK : oddIn K ≤ oddIn M) (hOK' : oddIn (conjugate K a) ≤ oddIn M)
    (hJKK : J ≤ K ⊔ conjugate K a ⊔ oddIn M) (haa : a * a = 1)
    (hJ : J ≤ coreActionKernel K ∨ J ≤ coreActionKernel (conjugate K a)) : False := by
  have hconj : ∀ L : Subgroup X, J ≤ coreActionKernel L → J ≤ coreActionKernel (conjugate L a) :=
    fun L hL j hj => FooteLit.mem_coreActionKernel_conjugate (by
      rw [show a * j * a⁻¹ = j by
        rw [(mem_centralizer_singleton_iff.mp (hJa hj)).symm, mul_inv_cancel_right]]
      exact hL hj)
  have hKaa : conjugate (conjugate K a) a = K := by
    rw [UnbalancedLayer.conjugate_conjugate, haa, UnbalancedLayer.conjugate_one]
  have hJK : J ≤ coreActionKernel K ∧ J ≤ coreActionKernel (conjugate K a) := by
    rcases hJ with h | h
    · exact ⟨h, hconj K h⟩
    · exact ⟨hKaa ▸ hconj _ h, h⟩
  have hOM : M ≤ normalizer ((oddIn M : Subgroup X) : Set X) := GrS4.self_le_normalizer_oddIn M
  let Z : Subgroup X :=
    { carrier := {x | x ∈ M ∧ ∀ j ∈ J, ⁅j, x⁆ ∈ oddIn M}
      one_mem' := ⟨one_mem _, fun j _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
      mul_mem' := by
        rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
        refine ⟨mul_mem hxM hyM, fun j hj => ?_⟩
        rw [show ⁅j, x * y⁆ = ⁅j, x⁆ * (x * ⁅j, y⁆ * x⁻¹) by
          simp only [commutatorElement_def]; group]
        exact mul_mem (hx j hj) ((mem_normalizer_iff.mp (hOM hxM) _).mp (hy j hj))
      inv_mem' := by
        rintro x ⟨hxM, hx⟩
        refine ⟨inv_mem hxM, fun j hj => ?_⟩
        rw [show ⁅j, x⁻¹⁆ = x⁻¹ * ⁅j, x⁆⁻¹ * x⁻¹⁻¹ by simp only [commutatorElement_def]; group]
        exact (mem_normalizer_iff.mp (hOM (inv_mem hxM)) _).mp (inv_mem (hx j hj)) }
  have hLZ : ∀ L : Subgroup X, L ≤ M → J ≤ normalizer (L : Set X) → J ≤ coreActionKernel L →
      oddIn L ≤ oddIn M → L ≤ Z := by
    intro L hLM hJNL hJL hOL k hk
    refine ⟨hLM hk, fun j hj => ?_⟩
    have h1 := (hJL hj).2 k⁻¹ (inv_mem hk)
    have h2 := GrS4.conj_mem_oddIn_of_mem_normalizer (hJNL hj) h1
    rw [show j * (k⁻¹⁻¹ * j⁻¹ * k⁻¹ * j) * j⁻¹ = ⁅j, k⁆ by
      simp only [commutatorElement_def]; group] at h2
    exact hOL h2
  have hOZ : oddIn M ≤ Z := fun o ho => ⟨map_subtype_le _ ho, fun j hj => by
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp (hOM (hJM hj)) o).mp ho) (inv_mem ho)⟩
  have hJZ : J ≤ Z := hJKK.trans (sup_le (sup_le (hLZ K hKM hJNK hJK.1 hOK)
    (hLZ _ hK'M hJNK' hJK.2 hOK')) hOZ)
  have hJO : J ≤ oddIn M := by
    rw [← GSThmB.commutator_eq_self_of_isPComponent hJa hJc, commutator_le]
    intro j₁ hj₁ j₂ hj₂
    exact (hJZ hj₂).2 j₁ hj₁
  exact GrS4.not_odd_card_of_isPComponent hJa hJc
    (Odd.of_dvd_nat (UnbalancedCorr.odd_card_map_pPrimeCore M) (card_dvd_of_le hJO))

end CFSG.ComponentClassification.GrSLit.Single
