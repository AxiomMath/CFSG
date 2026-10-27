module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbFi22
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVEven
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaFi22
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltCover
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltOuter
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltBasic
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarRes

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.card_rbar_inf_alt (hd : D1OneSmallData p P M H R Rbar K)
    (hp57 : p = 5 ∨ p = 7) (hA : IsAltTwoP p K) :
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) =
      p ^ 2 := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, hT₁, -, -, -, hT₁nc, -⟩ := hd.exists_sylow
  rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp T₁.isPGroup'
  rw [hn]
  have hdvd : p ^ n ∣ Nat.card K := hn ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨e⟩ := hA
  rw [Nat.card_congr e.toEquiv] at hdvd
  have := hp.two_le
  have h2 := two_mul_card_alternatingGroup_fin (n := 2 * p) (by omega)
  have hn3 : n < 3 := by
    by_contra h3
    have h4 : p ^ 3 ∣ (2 * p).factorial :=
      h2 ▸ ((pow_dvd_pow p (by omega : 3 ≤ n)).trans hdvd).trans (dvd_mul_left _ _)
    rcases hp57 with rfl | rfl
    · exact absurd h4 (by decide)
    · exact absurd h4 (by norm_num [Nat.factorial])
  have hn2 : 2 ≤ n := by
    by_contra h2'
    apply hT₁nc
    interval_cases n
    · have : Subsingleton (T₁ : Subgroup K) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hn, pow_zero])).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (by rw [hn, pow_one])
  rw [show n = 2 by omega]

theorem D1OneSmallData.false_of_ibNormal_alt (hUP : KFactUPrimeSmall) (hSch : KFactCatalogSchreier)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hB : D1IbAltInputs) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hnIa : ¬ D1SmallIa p H K) (hB0 : D1CzB0 p R z)
    (hVH : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H)
    (hp57 : p = 5 ∨ p = 7) (hA : IsAltTwoP p K) (hFi : ¬ (p = 5 ∧ IsFi22 K)) : False := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have hp5 : 5 ≤ p := by rcases hp57 with rfl | rfl <;> norm_num
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := centralizer_le_of_normalizer_vz_le hVH
  have hL : ¬ (p = 3 ∧ IsLinThreeFour K) := fun h => by omega
  have hLa : D1SmallLa p M H Rbar K := d1SmallLa_of_not hL
  obtain ⟨hcardR, hdec⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 hLa
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzp1 : z ^ p = 1 := by rw [← hz.2.1]; exact pow_orderOf_eq_one z
  have hexpR : ∀ r ∈ R, r ^ p = 1 := by
    intro r hr
    obtain ⟨t, ht, i, rfl⟩ := hdec r hr
    have hc : Commute t (z ^ i) := Commute.pow_right
      (show Commute t z from Subgroup.mem_centralizer_singleton_iff.mp
        (hRC (d1LiftX_le p H R K ht))) i
    rw [hc.mul_pow, hd.pow_eq_one_of_mem_d1LiftX hExp ht, ← pow_mul, mul_comm, pow_mul, hzp1,
      one_pow, one_mul]
  have hph := hd.toPhaseThree hUP hL hFi
  obtain ⟨T₁, -, hs, hn, hcat, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hzM : z ∈ M := hph.le_M hz.1
  have hzN : z ∈ blockNormalizer M H := mem_blockNormalizer.mpr fun L hL' =>
    hph.mem_normalizer_block_of_five hd.cfg.ind hB.h85 hB.h86 hB.h93 hB.hD2 hB.hK2 hB.hC3 hB.hK5
      hp5 ⟨hz.2.2.1, hzM⟩ hz.2.1 hL'
  have hcfg : D1IbAltConfig p P M H R Rbar K z :=
    { data := hd
      elt := hz
      b0 := hB0
      cz_le := hCz
      prime57 := hp57
      alt := hA
      not_fi22 := hFi
      phase := hph
      dec := hdec
      exp := hexpR
      card_T := D1OneSmallData.card_rbar_inf_alt hd hp57 hA
      card_R_le := hcardR
      rbar_le := hd.rbar_le_sup_centralizer hOut hLa
      out := hSch K hs hn hcat
      uprime := hUP K hs hn hcat p hp hp2 T₁ hTnc hΓT hd.small hL hFi
      cover := D1OneSmallData.exists_cover_blocks hd hz hzM hnIa hcardR hzN }
  exact hcfg.false_main hB hOrb

@[expose] def D1SmallGEVIbNormalAllRest4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    ¬ D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    ¬ D1SmallOuterR p H Rbar K →
    ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    GLBIsMaxTwoLocal H →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    D1GEVStarSmall p P M R z K →
    (∀ Hs : Subgroup G, GLBIsMaxTwoLocal Hs →
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs →
      ∀ hzHs : z ∈ Hs, ¬ (Subgroup.zpowers
        (QuotientGroup.mk' (primeComplementCore (G := Hs) p) ⟨z, hzHs⟩)).Normal) →
    p = 3 → False

theorem d1SmallGEVIbNormalAllRest3_of_rest4 (hGst : StmtSmallGuest) (hFA : KFactFi22AltSection)
    (hK6 : KFactFi22GuestRank) (hUP : KFactUPrimeSmall) (hSch : KFactCatalogSchreier)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hB : D1IbAltInputs) (h4 : D1SmallGEVIbNormalAllRest4) : D1SmallGEVIbNormalAllRest3 := by
  intro G _ _ p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hgp hcomm hnot hH hVH hsm hall hcase
  by_cases hp3 : p = 3
  · exact h4 G p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hgp hcomm hnot hH hVH hsm hall hp3
  have hA : IsAltTwoP p K := hcase.resolve_left hp3
  by_cases hFi : p = 5 ∧ IsFi22 K
  · exact hGst G p P M H R Rbar K hd (Or.inr ⟨hFi.1, hFi.2,
      mem_glbBetaFour_of_le_pRank Nat.prime_three (by norm_num) hd.cfg.ext.maxTwoLocal_H.1 le_rfl
        (four_le_pRank_of_fi22 hFA hK6 hFi.2)⟩)
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have hp57 : p = 5 ∨ p = 7 := by
    have h11 : p < 11 := by
      by_contra h
      exact hgp ⟨hA, by omega, Or.inl (by omega)⟩
    have := hp.two_le
    interval_cases p
    · exact absurd rfl hp2
    · exact absurd rfl hp3
    · exact absurd hp (by decide)
    · left; rfl
    · exact absurd hp (by decide)
    · right; rfl
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
  exact D1OneSmallData.false_of_ibNormal_alt hUP hSch hOut hExp hOrb hB hd hz hnIa hB0 hVH hp57 hA
    hFi

end CFSG.AGLEmbedding
