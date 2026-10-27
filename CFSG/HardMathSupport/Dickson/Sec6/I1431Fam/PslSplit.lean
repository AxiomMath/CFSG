module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslHb
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.CALinearPrimary

variable {n : ℕ} {K : Type} [Field K] [Finite K] {a : SpecialLinearGroup (Fin n) K}

theorem sl_block_split (hpk : (3 : K) ≠ 0) (hap : a ^ 3 = 1) {h : K[X]}
    (hh : h ∈ primaryFactors ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)))
    (hm2 : primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) h = 2)
    {β : SpecialLinearGroup (Fin n) K} (hβa : β * a = a * β) (hβ3 : β ^ 3 = 1) :
    ∃ s ∈ (linearSpecialBlock (slGL n K a) h).comap (slGL n K),
      ∃ c ∈ Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin n) K)),
        (∀ m ∈ (linearSpecialBlock (slGL n K a) h).comap (slGL n K), c * m = m * c) ∧
          β = s * c := by
  have hsq := squarefree_minpoly_slGL hpk hap
  have hgc : slGL n K β ∈ gl_centralizer (slGL n K a) := by
    show slGL n K β ∈ Subgroup.centralizer ({slGL n K a} : Set _)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hβa]
  have hg3 : slGL n K β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  obtain ⟨sg, hsg, cg, hcg, hcomm, hgsc⟩ := exists_block_split hsq hh hm2 hgc hg3
  obtain ⟨s, hs⟩ := linearSpecialBlock_le_range_slGL hsq hh hsg
  have hcgs : slGL n K (s⁻¹ * β) = cg := by
    rw [map_mul, map_inv, hs, hgsc]
    group
  refine ⟨s, by rw [Subgroup.mem_comap, hs]; exact hsg, s⁻¹ * β, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply slGL_injective
    rw [map_mul (slGL n K) (s⁻¹ * β) a, map_mul (slGL n K) a (s⁻¹ * β), hcgs]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcg : cg ∈ Subgroup.centralizer
      ({slGL n K a} : Set (LinearMap.GeneralLinearGroup K (Fin n → K))))
  · intro m hm
    apply slGL_injective
    rw [map_mul (slGL n K) (s⁻¹ * β) m, map_mul (slGL n K) m (s⁻¹ * β), hcgs]
    exact hcomm _ hm
  · rw [mul_inv_cancel_left]

end CFSG.HardMathSupport.Dickson.Sec6.I1431
