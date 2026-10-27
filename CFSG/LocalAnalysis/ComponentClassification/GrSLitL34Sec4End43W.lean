module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46
public import CFSG.LocalAnalysis.ComponentClassification.Sol78PSp4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4DiagMem
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem isAbelianTwoOfRank_map_conj {E : Subgroup G} (hE : IsAbelianTwoOfRank 3 E) (h : G) :
    IsAbelianTwoOfRank 3 (E.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨F, hFE, hF, hF8⟩ := exists_isElemTwo_eight hE
  refine ⟨hE.1.map _, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul, hE.2.1 u hu v hv]
  · refine le_pRank_of_isElemTwo (map_mono hFE) (hF.map_conj h) (k := 3) ?_
    rw [card_map_of_injective (MulAut.conj h).injective, hF8]
    norm_num

theorem mem_normalizer_of_map_le' {W S E : Subgroup G}
    (hWS : ∀ E : Subgroup G, E ≤ S → IsAbelianTwoOfRank 3 E → wGroup E = W) (hES : E ≤ S)
    (hE : IsAbelianTwoOfRank 3 E) {h : G} (hEh : E.map (MulAut.conj h).toMonoidHom ≤ S) :
    h ∈ normalizer (W : Set G) := by
  have h1 := hWS _ hEh (isAbelianTwoOfRank_map_conj hE h)
  rw [wGroup_map_conj, hWS E hES hE] at h1
  exact mem_normalizer_iff_map_conj_eq.mpr h1

end CFSG.ComponentClassification.GrSLit.GrS4

