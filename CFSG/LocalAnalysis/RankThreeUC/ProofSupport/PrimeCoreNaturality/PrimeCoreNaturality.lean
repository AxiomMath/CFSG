module


public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreConjugacy

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimeCoreNaturality

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem map_primeCore (p : ℕ) (e : MulAut G) (H : Subgroup G) :
    rankThreePrimeCore p (H.map e.toMonoidHom) = (rankThreePrimeCore p H).map e.toMonoidHom := by
  have map_symm_map (e : MulAut G) (H : Subgroup G) :
      (H.map e.symm.toMonoidHom).map e.toMonoidHom = H := by
    simpa using map_automorphism_symm_map H e.symm
  have map_primeCore_le (p : ℕ) (e : MulAut G) (H : Subgroup G) :
      (rankThreePrimeCore p H).map e.toMonoidHom ≤ rankThreePrimeCore p (H.map e.toMonoidHom) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    rintro N ⟨hNH, hNn, hcop⟩
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨Subgroup.map_mono hNH, ?_, ?_⟩
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hNH),
        ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hNn)
    · rwa [Subgroup.card_map_of_injective e.injective]
  refine le_antisymm ?_ (map_primeCore_le p e H)
  have h1 := map_primeCore_le p e.symm (H.map e.toMonoidHom)
  have h2 := Subgroup.map_mono (f := e.toMonoidHom) h1
  rwa [map_automorphism_symm_map, map_symm_map] at h2

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimeCoreNaturality
