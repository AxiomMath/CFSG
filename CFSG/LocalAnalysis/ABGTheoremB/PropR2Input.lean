module

public import CFSG.LocalAnalysis.ABGTheoremB.PropR2
public import CFSG.LocalAnalysis.ABGTheoremB.V56Inputs
import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.LocalAnalysis.ABGTheoremB.Statements
public import CFSG.LocalAnalysis.ABGTheoremB.V4Defs

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

private theorem isSylowOf_inf_oddCoreIn_of_maximal (hσ : σ.IsValid) {K U : Subgroup G}
    (hDK : σ.D ≤ K) (hU : U ∈ maximals (signalizers K σ.D σ.p)) :
    IsSylowOf σ.p (U ⊓ oddCoreIn K) (oddCoreIn K) := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  obtain ⟨⟨hUK, hUp, hDU, -⟩, hmax⟩ := hU
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hKO : K ≤ Subgroup.normalizer ((oddCoreIn K : Subgroup G) : Set G) :=
    le_normalizer_oddCoreIn K
  have hUodd : Odd (Nat.card U) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUp
    rw [hk]
    exact (hσ.p_prime.eq_two_or_odd'.resolve_left hσ.p_ne_two).pow
  have hXodd : Odd (Nat.card (oddCoreIn K ⊔ U : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd (hUK.trans hKO) (odd_card_oddCoreIn K) hUodd
  have hDX : σ.D ≤ Subgroup.normalizer ((oddCoreIn K ⊔ U : Subgroup G) : Set G) :=
    le_trans (le_inf (hDK.trans hKO) hDU) (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨R, hR, hUR, hDR⟩ := exists_isSylowOf_normalized_ge_of_odd hσ.p_prime hD2 hDX hXodd
    le_sup_right hUp hDU
  have hRp : IsPGroup σ.p R := hR.isPGroup
  have hRD : R ⊓ σ.D = ⊥ := by
    have hcop : Nat.Coprime (Nat.card R) (Nat.card σ.D) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hD2
      rw [hk, hm]
      exact Nat.Coprime.pow k m ((Nat.coprime_primes hσ.p_prime Nat.prime_two).mpr hσ.p_ne_two)
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hRK : R ≤ K := hR.le.trans (sup_le (oddCoreIn_le K) hUK)
  have hRU : R = U := hmax R ⟨hRK, hRp, hDR, hRD⟩ hUR
  rw [hRU] at hR
  exact hR.inf_of_le_normalizer le_sup_left (sup_le (Subgroup.le_normalizer) (hUK.trans hKO))

theorem propR2Input_of (hσ : σ.IsValid) (h91 : σ.PropIV91)
    (h_II61D : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) → ∀ r : ℕ, r.Prime →
      r ≠ 2 → CFSG.pCore r H ≠ ⊥ → CFSG.pPrimeCore r H ≤ CFSG.oddCore H → IsPStable r H)
    (h_R23 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J,
      ∀ P : Subgroup G, IsSylowOf σ.p P σ.C → σ.D ≤ Subgroup.normalizer (P : Set G) →
      ∀ K ∈ σ.familyMstar σ.p, W ≤ K →
      ∀ U ∈ maximals (signalizersPerm K σ.D W σ.p), U ∈ maximals (signalizers K σ.D σ.p) →
      P ≤ U → pPrimeCoreIn σ.p (U ⊔ W) = ⊥ →
      ∀ L : Subgroup G, oddCoreIn K < L → L ≤ K → K ≤ Subgroup.normalizer (L : Set G) →
        K ≤ L ⊔ (K ⊓ Subgroup.normalizer ((oddCoreIn K ⊔ U : Subgroup G) : Set G))) :
    ∀ J : Subgroup G, σ.IsV21Layer J → V56.PropR2Input σ J := by
  intro J hJ hHyp W hW P hP hDP K hK hWK U hU1 hU2 hPU hUW
  have hUO := isSylowOf_inf_oddCoreIn_of_maximal σ hσ hK.2.1 hU2
  have hMO : CFSG.pPrimeCore σ.p K ≤ CFSG.oddCore K := by
    refine le_sSup ⟨CFSG.pPrimeCore_normal (p := σ.p) (G := K), ?_⟩
    rw [← Subgroup.card_map_of_injective K.subtype_injective]
    exact hK.2.2.2
  have hst : IsPStable σ.p K :=
    h_II61D K hK.2.1 hK.2.2.1 σ.p hσ.p_prime hσ.p_ne_two hK.1.pCore_ne_bot hMO
  exact σ.propR2 hσ hK hU2.1 hUO (h91 σ.p hHyp K hK) hst
    (h_R23 J hJ hHyp W hW P hP hDP K hK hWK U hU1 hU2 hPU hUW)

end Setting

end CFSG.ABGTheoremB
