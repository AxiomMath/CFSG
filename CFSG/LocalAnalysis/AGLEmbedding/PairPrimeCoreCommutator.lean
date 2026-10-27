module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Pair
import CFSG.LocalAnalysis.AGLEmbedding.PhaseTwo

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem AGLPair.commutator_primeCore_le_twoCore (h : AGLPair p M H R) {X : Subgroup G}
    (hXR : X ≤ R) (hXQ : ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal) :
    ⁅GLBPrimeCore p H, X⁆ ≤ pCoreOf 2 M := by
  have hXM : X ≤ M := hXR.trans h.le_M
  have hQM : pCoreOf 2 M ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hQN : pCoreOf 2 M ≤ GLBPrimeCore p H := h.twoCore_M_le.trans h.twoCore_le_primeCore
  have hMXQ : M ≤ Subgroup.normalizer ((X ⊔ pCoreOf 2 M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hXM hQM)).mp hXQ
  refine (commutator_le_inf_of_le_normalizer le_sup_left (h.primeCore_le.trans hMXQ)
    ((hXR.trans h.le_H).trans (le_normalizer_glbPrimeCore p H))).trans ?_
  rintro y ⟨hyN, hyXQ⟩
  have hy : y ∈ ((X ⊔ pCoreOf 2 M : Subgroup G) : Set G) := hyXQ
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X _
    (hXM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))] at hy
  obtain ⟨x, hx, q, hq, rfl⟩ := hy
  have hxN : x ∈ GLBPrimeCore p H := by
    simpa using (GLBPrimeCore p H).mul_mem hyN ((GLBPrimeCore p H).inv_mem (hQN hq))
  have hmem : x ∈ X ⊓ GLBPrimeCore p H := ⟨hx, hxN⟩
  rw [inf_eq_bot_of_isPGroup h.prime (h.isPGroup_R.to_le hXR) (glbPrimeCore_coprime p H),
    Subgroup.mem_bot] at hmem
  simpa [hmem] using hq

end CFSG.AGLEmbeddingD2
