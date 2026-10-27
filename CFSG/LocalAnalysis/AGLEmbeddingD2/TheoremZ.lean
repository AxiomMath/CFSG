module

public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZ

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

structure AGLJConfig {G : Type} [Group G] [Finite G] (p : ℕ) (M H R X : Subgroup G) : Prop where
  pair : AGLPair p M H R
  le_R : X ≤ R
  ne_bot : X ≠ ⊥
  normal_sup : ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal
  commutator_le : ⁅GLBPrimeCore p H, X⁆ ≤ pCoreOf 2 M
  centralizer_le : (H ⊓ M) ⊓ Subgroup.centralizer (X : Set G) ≤ X ⊔ GLBPrimeCore p H

@[expose] def AGLJCompetitorsOn {G : Type} [Group G] (C : Subgroup G → Prop)
    (R X : Subgroup G) : Prop :=
  ∀ H : Subgroup G, C H → ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' →
    nclIn H X ≤ H' → R ≤ H' → C H' ∧ nclIn H X ≤ nclIn H' X

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R X : Subgroup G}

theorem AGLJConfig.commutator_nclIn_le (h : AGLJConfig p M H R X) :
    ⁅GLBPrimeCore p H, nclIn H X⁆ ≤ pCoreOf 2 H :=
  CFSG.AGLEmbedding.commutator_nclIn_le (h.le_R.trans h.pair.le_H)
    (le_normalizer_glbPrimeCore p H)
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
    (h.commutator_le.trans h.pair.twoCore_M_le)

theorem false_of_agljCompetitorsOn {C : Subgroup G → Prop}
    (hC : ∀ H, C H → AGLJConfig p M H R X) (hcomp : AGLJCompetitorsOn C R X)
    {H : Subgroup G} (h : C H) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G) : False := by
  obtain ⟨H₀, h₀, hmax⟩ := Set.exists_max_image {H' : Subgroup G | C H'}
    (fun H' => Nat.card (nclIn H' X)) (Set.toFinite _) ⟨H, h⟩
  have hc₀ := hC H₀ h₀
  refine hc₀.pair.false_of_unique_over hc₀.le_R hc₀.normal_sup hc₀.commutator_le
    hc₀.centralizer_le hc₀.commutator_nclIn_le (fun H' hH' hJH' hRH' => ?_) hCGT hD2
  obtain ⟨h', hJJ'⟩ := hcomp H₀ h₀ H' hH' hJH' hRH'
  have heq : nclIn H₀ X = nclIn H' X := Subgroup.eq_of_le_of_card_ge hJJ' (hmax H' h')
  have hJn' : ((nclIn H₀ X).subgroupOf H').Normal := heq ▸ nclIn_normal H' X
  have hAJ : pCoreOf 2 (GLBPrimeCore p (nclIn H₀ X)) ≤ nclIn H₀ X :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans (glbPrimeCore_le p _)
  have hNA : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p (nclIn H₀ X)) : Set G) = H₀ :=
    maxTwoLocal_normalizer_eq_of_normal hc₀.pair.maxTwoLocal_H
      (hc₀.pair.pCoreOf_two_primeCore_ne_bot hc₀.le_R hc₀.ne_bot)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
      (hAJ.trans (nclIn_le_self H₀ X))
      (normal_pCoreOf_two_glbPrimeCore p (nclIn_le_self H₀ X) (nclIn_normal H₀ X))
  have hH'H : H' ≤ H₀ := hNA ▸ (Subgroup.normal_subgroupOf_iff_le_normalizer (hAJ.trans hJH')).mp
    (normal_pCoreOf_two_glbPrimeCore p hJH' hJn')
  exact (hH'.2 H₀ hc₀.pair.maxTwoLocal_H.1 hH'H).symm

end Config

end CFSG.AGLEmbeddingD2
