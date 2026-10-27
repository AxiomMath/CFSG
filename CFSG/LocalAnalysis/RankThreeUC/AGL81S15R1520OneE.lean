module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneD
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.QuasithinUnique CFSG.Open Subgroup

theorem pRank_map_eq_of_coprime_kernel {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {p : ℕ} [Fact p.Prime] (f : X →* Y) (D : Subgroup X)
    (hD : ¬ p ∣ Nat.card ↥(D ⊓ f.ker)) : Open.pRank p (D.map f) = Open.pRank p D := by
  have hrange : (f.comp D.subtype).range = D.map f := by
    rw [MonoidHom.range_comp, range_subtype]
  have hker : ¬ p ∣ Nat.card (f.comp D.subtype).ker := by
    have h : (f.comp D.subtype).ker = (D ⊓ f.ker).subgroupOf D := by
      ext x
      simp [MonoidHom.mem_ker, mem_subgroupOf]
    rw [h, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : D ⊓ f.ker ≤ D)).toEquiv]
    exact hD
  have h1 : Open.pRank p (⊤ : Subgroup (↥D ⧸ (f.comp D.subtype).ker)) =
      Open.pRank p (⊤ : Subgroup ↥D) :=
    CFSG.SectionRank.pRank_quotient_eq (f.comp D.subtype).ker hker
  have h2 : Open.pRank p (⊤ : Subgroup (↥D ⧸ (f.comp D.subtype).ker)) =
      Open.pRank p (⊤ : Subgroup ↥(f.comp D.subtype).range) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt
      (QuotientGroup.quotientKerEquivRange (f.comp D.subtype))
  calc Open.pRank p (D.map f) = Open.pRank p (f.comp D.subtype).range := by rw [hrange]
    _ = Open.pRank p (⊤ : Subgroup ↥(f.comp D.subtype).range) :=
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
    _ = Open.pRank p (⊤ : Subgroup ↥D) := h2.symm.trans h1
    _ = Open.pRank p D := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup D).symm

theorem pRank_quotient_pPrimeCore_le_one
    (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {M : Type} [Group M] [Finite M]
    (hK : CFSG.IsKGroup M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : CharTwo (⊤ : Subgroup M)) {T : Subgroup M} (hT : IsSylowTwoOf T ⊤)
    (hN : ∀ T₀ : Subgroup M, T₀ ≠ ⊥ → T₀ ≤ T → (T₀.subgroupOf T).Characteristic →
      Open.pRank p (normalizer (T₀ : Set M)) ≤ 1)
    {A : Subgroup M} [A.Normal] (hWA : CFSG.pPrimeCore p M ≤ A)
    (h3 : ¬ 3 ∣ (CFSG.pPrimeCore p M).relIndex A) :
    Open.pRank p (A.map (QuotientGroup.mk' (CFSG.pPrimeCore p M))) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  have hrkA : 1 < Open.pRank p (A.map (QuotientGroup.mk' (CFSG.pPrimeCore p M))) := not_le.1 hcon
  have hOW : pCoreOf 2 (⊤ : Subgroup M) ≤ CFSG.pPrimeCore p M := by
    rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore]
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := M)).exists_card_eq
    exact le_sSup ⟨inferInstance, by
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)⟩
  obtain ⟨D, hTD, hD3, hDc, hAD⟩ := exists_threePrime_overgroup hM hT hWA hOW h3
  have hDrk : 1 < Open.pRank p D := by
    have hW1 : ¬ p ∣ Nat.card ↥(D ⊓ (QuotientGroup.mk' (CFSG.pPrimeCore p M)).ker) := by
      rw [QuotientGroup.ker_mk']
      exact fun h => (Nat.Prime.coprime_iff_not_dvd hp).1
        (CFSG.pPrimeCore_coprime_card (p := p) (G := M))
        (h.trans (card_dvd_of_le inf_le_right))
    have h1 : A.map (QuotientGroup.mk' (CFSG.pPrimeCore p M)) ≤
        D.map (QuotientGroup.mk' (CFSG.pPrimeCore p M)) := by
      calc A.map (QuotientGroup.mk' (CFSG.pPrimeCore p M))
          ≤ (D ⊔ CFSG.pPrimeCore p M).map (QuotientGroup.mk' (CFSG.pPrimeCore p M)) :=
            map_mono hAD
        _ = D.map (QuotientGroup.mk' (CFSG.pPrimeCore p M)) := by
            rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
    exact lt_of_lt_of_le hrkA ((CFSG.SectionRank.pRank_mono hp.one_lt h1).trans
      (pRank_map_eq_of_coprime_kernel _ D hW1).le)
  have hTD' : IsSylowTwoOf T D := by
    have h1 : T.relIndex D ∣ T.index := relIndex_dvd_index_of_le hTD
    rw [← relIndex_top_right] at h1
    exact ⟨hTD, hT.2.1, fun h => hT.2.2 (h.trans h1)⟩
  obtain ⟨T₀, hne, hle, hchar, hrk⟩ := k520_2_of_isKGroup_sub hSz hK hD3 hDc hTD' hp hp2 hDrk
  exact absurd (hN T₀ hne hle hchar) (not_le.2 hrk)

end CFSG.LocalAnalysis.RankThreeUC.S15
