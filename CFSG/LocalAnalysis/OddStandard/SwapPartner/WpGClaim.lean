module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGBounds
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGComp
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGLocal
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGOrbit

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

theorem claimA {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}
    (hC : CentData z ι) (hP2 : ¬ IsConj z (z * ι τ₀)) {t : TwoSec (z * ι τ₀)}
    {Sg V K : Subgroup (TwoSec (z * ι τ₀))}
    (hO : CFSG.pPrimeCore 2 (TwoSec (z * ι τ₀)) = ⊥) (H : WreathCase t Sg V K) {c : G}
    (hc : IsConj z c) (hcx : c ∈ centralizer ({z * ι τ₀} : Set G)) :
    pairOrder c (z * ι τ₀) = N10 1 ∧
      (QuotientGroup.mk ⟨c, hcx⟩ : TwoSec (z * ι τ₀)) ∉
        normalizer (K : Set (TwoSec (z * ι τ₀))) := by
  have hx : (z * ι τ₀) * (z * ι τ₀) = 1 := x₂_mul_self hC
  have hc2 : c * c = 1 := mul_self_of_isConj hC hc
  obtain ⟨g, σ, hgc, hσ, hσ1, hgx, hpo, hk1, hk5⟩ := exists_type hC hP2 hc hcx
  obtain ⟨e⟩ := H.iso
  by_cases hcN : (QuotientGroup.mk ⟨c, hcx⟩ : TwoSec (z * ι τ₀)) ∈
      normalizer (K : Set (TwoSec (z * ι τ₀)))
  · exfalso
    have hA : AllowedPair (N10 (Multiset.card σ.cycleType))
        (WreathCase.theta H e ⟨QuotientGroup.mk ⟨c, hcx⟩, hcN⟩) :=
      allowedPair_of_inner H e hcx hc2 hcN hpo
    obtain ⟨k, hk⟩ : ∃ k, k = Multiset.card σ.cycleType := ⟨_, rfl⟩
    rw [← hk] at hpo hk1 hk5 hA
    interval_cases k
    · obtain ⟨D, hD, hDcard⟩ := exists_simpleNormalIn hC hσ hσ1 (by omega) hgx
      rw [hgc] at hD
      rw [← hk] at hDcard
      norm_num [Nat.factorial] at hDcard
      have h := WreathCase.card_le_altCentCard8_of_simpleNormalIn hx hO H e hcx hc2 hcN hD
      rw [hDcard] at h
      exact false_of_allowedPair_one hA h
    · obtain ⟨D, hD, hDcard⟩ := exists_simpleNormalIn hC hσ hσ1 (by omega) hgx
      rw [hgc] at hD
      rw [← hk] at hDcard
      norm_num [Nat.factorial] at hDcard
      have h := WreathCase.card_le_altCentCard8_of_simpleNormalIn hx hO H e hcx hc2 hcN hD
      rw [hDcard] at h
      exact false_of_allowedPair_two hA h
    · have hn : Nat.card (centralizer
          ({(QuotientGroup.mk ⟨c, hcx⟩ : TwoSec (z * ι τ₀))} :
            Set (TwoSec (z * ι τ₀)))) ≤ N10 3 :=
        (card_centralizer_twoSec_le hcx).trans hpo.le
      have h := WreathCase.two_mul_card_range_le H e hcN hn (AllowedPair (N10 3))
        (fun f hf => allowedPair_of_conj H e hcx hc2 hpo f hf)
      obtain ⟨g₀, hg₀, hg1, hg2⟩ := WreathCase.exists_odd_odd H e
      exact false_of_allowedPair_three (WreathCase.theta H e).range
        (WreathCase.alt_prod_alt_le_range H e) hg₀ hg1 hg2 h
    · exact false_of_allowedPair_four hA
    · have hn : Nat.card (centralizer
          ({(QuotientGroup.mk ⟨c, hcx⟩ : TwoSec (z * ι τ₀))} :
            Set (TwoSec (z * ι τ₀)))) ≤ N10 5 :=
        (card_centralizer_twoSec_le hcx).trans hpo.le
      have h := WreathCase.two_mul_card_range_le H e hcN hn (AllowedPair (N10 5))
        (fun f hf => allowedPair_of_conj H e hcx hc2 hpo f hf)
      obtain ⟨g₀, hg₀, hg1, hg2⟩ := WreathCase.exists_odd_odd H e
      exact false_of_allowedPair_five (WreathCase.theta H e).range
        (WreathCase.alt_prod_alt_le_range H e) hg₀ hg1 hg2 h
  · exact ⟨by
      have hle := two_mul_le_pairOrder_of_outer H hcx hc2 hcN
      rw [hpo] at hle
      have hk := eq_one_of_two_mul_le_N10 hk1 hk5 hle
      rw [hpo, hk], hcN⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
