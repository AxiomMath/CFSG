module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSylow
public import CFSG.LocalAnalysis.ComponentClassification.Sol76F316Tools

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem pPrimeCore_le_of_cover (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {N : Subgroup X}
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin n)) {Y : Subgroup X} (hYN : Y ≤ N)
    (hYH : Y ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hYK : Y ≤ UnbalancedLayer.coreActionKernel M)
    (hsupY : Y ⊔ (pPrimeCore 2 ↥N).map N.subtype = N) :
    (pPrimeCore 2 ↥N).map N.subtype ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  obtain ⟨θY, -⟩ := exists_coreQuot_of_sup hYN hsupY θN
  have hYr : 2 ≤ CFSG.Open.pRank 2 Y := by
    have h1 := Sol78.three_le_pRank_of_coreQuotient (by omega) θY
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h1
    omega
  have hCY : ∀ y ∈ Y, orderOf y = 2 →
      centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
    intro y hy hy2
    have hy1 : zpowers y ≠ ⊥ := fun h => by
      rw [zpowers_eq_bot] at h
      rw [h, orderOf_one] at hy2
      omega
    have h1 := S.centralizer_le_of_le_coreActionKernel h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup
      (zpowers_le.mpr (hYH hy)) (zpowers_le.mpr (hYK hy))
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])) hy1
    rwa [UnbalancedLayer.centralizer_zpowers_eq] at h1
  refine Sol76T13.le_of_coprime_of_pRank hYr hCY ?_
    (fun y hy => Sol76.le_normalizer_oddCoreIn N (hYN hy))
  rw [card_map_of_injective N.subtype_injective]
  exact pPrimeCore_coprime_card

end Sig36

end CFSG.ComponentClassification.SolMax
