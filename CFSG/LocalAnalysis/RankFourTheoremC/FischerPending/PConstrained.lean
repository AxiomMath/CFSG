module

public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Core

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.le_of_two_le_pRank_inf_Op_p'p (hS : ObstructionSetting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H)
    (hR2 : 2 ≤ CFSG.Open.pRank p
      (((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype)) : H ≤ M := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hM := hext.obstruction.1
  obtain ⟨A, hAP, hA, hAc⟩ := hS.exists_elemAbelian_card_eq hp P
  have hKM : (CFSG.pPrimeCore p H).map H.subtype ≤ M := by
    have hcop : ¬ p ∣ Nat.card ((CFSG.pPrimeCore p H).map H.subtype) := by
      rw [card_map_of_injective H.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd hprime).1 CFSG.pPrimeCore_coprime_card
    exact hS.le_of_elemAbelian_normalizes hp hM hAP hA hAc hcop
      ((hAP.trans hPH).trans (CFSG.ABGTheoremB.le_normalizer_map_subtype H _))
  exact le_of_normalizer_inf_Op_p'p_le hPH hKM
    (hext.normalizer_le_of_normal hPD (map_inf_Op_p'p_le hPH) (le_normalizer_inf_Op_p'p hPH) hR2)

theorem ObstructionSetting.le_of_isPConstrained (hS : ObstructionSetting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H)
    (hH : CFSG.ABGLocalTools.IsPConstrained p H) : H ≤ M := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨A, hAP, hA, hAc⟩ := hS.exists_elemAbelian_card_eq hp P
  refine hS.le_of_two_le_pRank_inf_Op_p'p hp hext hPD hPH
    (two_le_pRank_inf_Op_p'p_of_not_isCyclic hodd hPH fun hRc => ?_)
  have hle := card_le_of_isCyclic_of_centralizer_le hodd P.isPGroup' (map_inf_Op_p'p_le hPH)
    (le_normalizer_inf_Op_p'p hPH) (inf_centralizer_le_of_isPConstrained hPH hH) hRc hAP hA
  rw [hAc] at hle
  have := (Nat.pow_le_pow_iff_right hprime.one_lt).1 hle
  omega

end CFSG.LocalAnalysis.RankFourTheoremC
