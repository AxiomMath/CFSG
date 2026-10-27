module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPhaseThree
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open scoped commutatorElement

theorem not_commutator_thompsonJ_le {G : Type} [Group G] [Finite G] {p : ℕ} {M H R L : Subgroup G}
    (h : CFSG.AGLEmbeddingD2.AGLPair p M H R)
    (hL : CFSG.AGLEmbedding.IsWeakSBlock M (CFSG.Open.pCoreOf 2 H) L) :
    ¬ ⁅L, CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H)⁆ ≤
      CFSG.Open.pCoreOf 2 M := by
  intro hcomm
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup G,
      T = CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) ⊔
        CFSG.Open.pCoreOf 2 M := ⟨_, rfl⟩
  have hJT : CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) ≤ T := by
    rw [hTdef]; exact le_sup_left
  have hTS : T ≤ CFSG.Open.pCoreOf 2 H := by
    rw [hTdef]
    exact sup_le (CFSG.Quasithin.B6.thompsonJ_le _) h.twoCore_M_le
  have hJeq : CFSG.Quasithin.thompsonJ T =
      CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) :=
    CFSG.Quasithin.B6.thompsonJ_eq_of_le hJT hTS
  have hconj : ∀ g ∈ L, ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro g hg
    have hJc : CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) ≤
        (CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) ⊔
          CFSG.Open.pCoreOf 2 M).comap (MulAut.conj g).toMonoidHom := by
      intro j hj
      rw [Subgroup.mem_comap]
      show g * j * g⁻¹ ∈
        CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) ⊔ CFSG.Open.pCoreOf 2 M
      have e : g * j * g⁻¹ = ⁅g, j⁆ * j := by
        rw [commutatorElement_def]; group
      rw [e]
      exact (CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) ⊔
          CFSG.Open.pCoreOf 2 M).mul_mem
        (Subgroup.mem_sup_right (hcomm (Subgroup.commutator_mem_commutator hg hj)))
        (Subgroup.mem_sup_left hj)
    have hQc : CFSG.Open.pCoreOf 2 M ≤
        (CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) ⊔
          CFSG.Open.pCoreOf 2 M).comap (MulAut.conj g).toMonoidHom := by
      intro q hq
      rw [Subgroup.mem_comap]
      show g * q * g⁻¹ ∈
        CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) ⊔ CFSG.Open.pCoreOf 2 M
      have hgN := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
        (hL.le hg)
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hgN q).mp hq)
    have hTc := sup_le hJc hQc
    rw [← hTdef] at hTc
    intro t ht
    have h2 := hTc ht
    rw [Subgroup.mem_comap] at h2
    exact h2
  have hLN : ∀ g ∈ L, g ∈ Subgroup.normalizer
      (CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) : Set G) := by
    intro g hg
    have hgT : g ∈ Subgroup.normalizer (T : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · intro ht
        exact hconj g hg t ht
      · intro ht
        have h1 := hconj g⁻¹ (inv_mem hg) _ ht
        have e : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
        rw [e] at h1
        exact h1
    have hcj := CFSG.Quasithin.cjSub_thompsonJ hgT
    rw [hJeq] at hcj
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcj
  have hLM : L ≤ M ⊓ Subgroup.normalizer
      (CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) : Set G) :=
    fun g hg => ⟨hL.le hg, hLN g hg⟩
  rw [h.normalizer_thompsonJ_eq.1] at hLM
  apply hL.not_le_normalizer
  intro g hg
  rw [h.normalizer_twoCore_H]
  exact (hLM hg).1

end CFSG.AGLEmbeddingD2.McLaughlin

end
