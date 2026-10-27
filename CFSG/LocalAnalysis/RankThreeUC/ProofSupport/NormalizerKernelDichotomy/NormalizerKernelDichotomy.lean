module

public import CFSG.LocalAnalysis.RankThreeUC.Section11.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section11.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section6.IsFrobeniusKernelComplement
import all CFSG.LocalAnalysis.RankThreeUC.Section6.IsFrobeniusKernelComplement
public import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
import all CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.NormalizerKernelDichotomy

open Subgroup CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem kernel_eq_bot_or_le {M X V₀ V K : Subgroup G} (hXM : X ≤ M) (hKM : K ≤ M)
    (hKX : K ≤ normalizer (X : Set G)) (hV : M ≤ normalizer (V : Set G))
    (hV₀ : M ≤ normalizer (V₀ : Set G))
    (hirr : Section6.IsIrreducibleUnder K X) :
    X ⊓ centralizerOnQuotient M V₀ V = ⊥ ∨ X ≤ centralizerOnQuotient M V₀ V := by
  haveI := centralizerOnQuotientIn_normal hV hV₀
  have hnorm : K ≤ normalizer ((X ⊓ centralizerOnQuotient M V₀ V : Subgroup G) : Set G) := by
    have key : ∀ k ∈ K, ∀ x ∈ X ⊓ centralizerOnQuotient M V₀ V,
        k * x * k⁻¹ ∈ X ⊓ centralizerOnQuotient M V₀ V := by
      intro k hk x hx
      obtain ⟨hxX, hxC⟩ := mem_inf.mp hx
      refine mem_inf.mpr ⟨?_, ?_⟩
      · exact (mem_normalizer_iff.mp (hKX hk) x).mp hxX
      · have := (centralizerOnQuotientIn_normal hV hV₀).conj_mem ⟨x, (show x ∈ centralizerOnQuotient M V₀ V from hxC).1⟩
          (show x ∈ centralizerOnQuotient M V₀ V from hxC) ⟨k, hKM hk⟩
        exact this
    intro k hk
    rw [mem_normalizer_iff]
    intro x
    refine ⟨key k hk x, fun hx => ?_⟩
    have := key k⁻¹ (inv_mem hk) _ hx
    simpa [mul_assoc] using this
  rcases (show _ ∧ _ from hirr).2 _ inf_le_left hnorm with h | h
  · exact Or.inl h
  · right
    rw [← h]; exact inf_le_right

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.NormalizerKernelDichotomy
