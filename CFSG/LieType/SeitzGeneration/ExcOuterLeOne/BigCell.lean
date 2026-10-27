module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.CTP

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section BigCell

variable {τ : Tag} {K : Type} [Field K]

theorem exists_rootSL2 {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ (φ : Matrix.SpecialLinearGroup (Fin 2) K →* ↥(adjointGroup τ K)) (ε₁ ε₂ : ℤ),
      (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ ∀ c : K,
        φ (u2 c) = xPar (rootOperatorFamily τ) γ ((ε₁ : K) * c) ∧
          φ (l2 c) = xPar (rootOperatorFamily τ) (-γ) ((ε₂ : K) * c) := by
  have hmem := (exceptional_Lang_root_rank_one_data τ K γ).2.2.2.2.1
  have hγn : IsRoot τ (-γ) := CFSG.LieType.Chevalley.IsRoot.neg hγ
  have hcoe : ∀ (δ : Fin τ.rank → ℤ) (hδ : IsRoot τ δ) (c : K),
      ((xPar (rootOperatorFamily τ) δ c : adjointGroup τ K) : ModGL τ K) =
        (rootOperatorFamily τ).eltUnit K ⟨δ, hδ⟩ c := by
    intro δ hδ c
    rw [CFSG.LieType.Steinberg.Adjoint.xPar_of_isRoot hδ]
    rfl
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := K) hγ
  obtain ⟨e, he, hee⟩ : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ ((e : ℤ) : K) = ε := by
    rcases mul_self_eq_one_iff.1 hε with h | h
    · exact ⟨1, Or.inl rfl, by simp [h]⟩
    · exact ⟨-1, Or.inr rfl, by simp [h]⟩
  have hu : ∀ c : K, rootSL2 τ K γ (CFSG.RankThree.PartOne.CTP.u2 c) =
      (rootOperatorFamily τ).eltUnit K ⟨γ, hγ⟩
        ((((rootOperatorFamily τ).pinnedFamilySign γ * (pinnedData τ γ).2.2 : ℤ) : K) * c) := by
    intro c
    rw [show CFSG.RankThree.PartOne.CTP.u2 c = CFSG.LieType.Chevalley.uSL c from
        Subtype.ext ((CFSG.RankThree.PartOne.CTP.u2_coe c).trans
          (CFSG.LieType.Chevalley.coe_uSL c).symm),
      rootSL2_uSL_eq γ c, (rootOperatorFamily τ).pinnedX_eq_eltUnit K hγ]
    congr 1
    rw [zsmul_eq_mul]
    push_cast
    ring
  have hl : ∀ c : K, rootSL2 τ K γ (CFSG.RankThree.PartOne.CTP.l2 c) =
      (rootOperatorFamily τ).eltUnit K ⟨-γ, hγn⟩
        ((((rootOperatorFamily τ).pinnedFamilySign (-γ) * e : ℤ) : K) * c) := by
    intro c
    rw [show CFSG.RankThree.PartOne.CTP.l2 c = CFSG.LieType.Chevalley.vSL c from
        Subtype.ext ((CFSG.RankThree.PartOne.CTP.l2_coe c).trans
          (CFSG.LieType.Chevalley.coe_vSL c).symm),
      hv c, (rootOperatorFamily τ).pinnedX_eq_eltUnit K hγn]
    congr 1
    rw [← hee]
    push_cast
    ring
  refine ⟨(rootSL2 τ K γ).codRestrict (adjointGroup τ K) hmem,
    (rootOperatorFamily τ).pinnedFamilySign γ * (pinnedData τ γ).2.2,
    (rootOperatorFamily τ).pinnedFamilySign (-γ) * e, ?_, ?_, fun c => ⟨?_, ?_⟩⟩
  · rcases (rootOperatorFamily τ).pinnedFamilySign_eq γ with h | h <;>
      rcases pinnedSign_eq τ γ with h' | h' <;> simp [h, h']
  · rcases (rootOperatorFamily τ).pinnedFamilySign_eq (-γ) with h | h <;>
      rcases he with h' | h' <;> simp [h, h']
  · exact Subtype.ext ((hu c).trans (hcoe γ hγ _).symm)
  · exact Subtype.ext ((hl c).trans (hcoe (-γ) hγn _).symm)

end BigCell

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
