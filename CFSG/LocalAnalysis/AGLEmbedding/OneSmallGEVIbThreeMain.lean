module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormal
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThree
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreAltSix
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPOdd
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_ib_three_m11 (hUP : KFactUPrimeSmall)
    (hSch : KFactCatalogSchreier) (hΓ : KFactSmallGammaSolvableSpor)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hSh3 : KFactSmallSylowShapeThree) (hK : CitedBlockToralThreeIb) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hnIa : ¬ D1SmallIa p H K) (hB0 : D1CzB0 p R z) (hOR : ¬ D1SmallOuterR p H Rbar K)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) (hp3 : p = 3) (hA6 : ¬ IsAltTwoP 3 K)
    (hU3 : ¬ IsSmallUnitary 3 K) (hL34 : ¬ IsLinThreeFour K) : False := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hF : ¬ (3 = 5 ∧ IsFi22 K) := fun h => absurd h.1 (by norm_num)
  have hL : ¬ (3 = 3 ∧ IsLinThreeFour K) := fun h => hL34 h.2
  have h3 := hd.toPhaseThree hUP hL hF
  obtain ⟨T₁, hT₁, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hUPK := hUP K hs hn hc 3 hp hp2 T₁ hTnc hΓT hd.small hL hF
  have hsolv := hΓ K hs hn hc 3 hp hp2 T₁ hTnc hΓT hd.small
    (fun h => hA6 (isAltTwoP_of_isSmallLinTwo_three h)) hU3 hA6 hL hF
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = 3 ^ 2 := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective,
      hSh3 K hs hn hc T₁ hTnc hΓT hd.small hU3]
  obtain ⟨hR, hdec⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut (fun _ _ => hOR))
  have hexpR := hd.pow_eq_one_of_d1LiftX_decomp hExp hz hdec
  have hperf := hd.perf_barM h3 hT₁ hUPK (hSch K hs hn hc) hsolv hR
  have hcov := hd.cover_ib_three rfl hz hnIa h3 h84 h86 hD2 hCz hR
  have hfus := hd.mem_fusionSet_of_not_mem hOut hExp hOrb hz hB0 rfl hA6 hL34 hcard
  have hinv := hd.exists_conj_eq_inv hOrb hz hdec rfl hA6 hcard
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hRz : ∀ r ∈ R, z * r = r * z := fun r hr =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)).symm
  have hsyl := exists_sylow_inf_of_sylow hB0 h3.le_M
  obtain ⟨E, hER, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 hp R
  rw [hd.pRank_R] at hEcard
  exact h3.false_of_toral_three_ib rfl h84 h85 h93 hD2 hSch hK hperf hz.1 hz.2.1 hCz hcov hsyl
    (hd.d1LiftX_facts hz).1 hRz hexpR hfus hinv ⟨E, hER, hEel, hEcard⟩

theorem D1OneSmallData.false_of_ib_three_a6 (hUP : KFactUPrimeSmall)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders)
    (hInvK : KFactAltSixSylowInvert) (hK : CitedBlockToralThreeIb) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hnIa : ¬ D1SmallIa p H K) (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hA : IsAltTwoP 3 K)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) : False := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hL34 : ¬ IsLinThreeFour K := not_l34_of_a6 hO hA
  have hL : ¬ (3 = 3 ∧ IsLinThreeFour K) := fun h => hL34 h.2
  have hF : ¬ (3 = 5 ∧ IsFi22 K) := fun h => absurd h.1 (by norm_num)
  have h3 := hd.toPhaseThree hUP hL hF
  obtain ⟨T₁, hT₁, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hUPK := hUP K hs hn hc 3 hp (by norm_num) T₁ hTnc hΓT hd.small hL hF
  have hsolv := hΓ3 K hs hn hc T₁ hTnc hΓT hd.small (Or.inl hA)
  obtain ⟨hR, hdec⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (d1SmallLa_of_not hL)
  have hperf := hd.perf_barM h3 hT₁ hUPK (hSch K hs hn hc) hsolv hR
  have hcov := hd.cover_ib_three rfl hz hnIa h3 h84 h86 hD2 hCz hR
  have hexpR := hd.pow_eq_one_of_d1LiftX_decomp hExp hz hdec
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  obtain ⟨hzT, -⟩ := hd.d1LiftX_facts hz
  have hfus := mem_fusionSet_of_not_mem_of_mul (d1LiftX_le 3 H R K) hz.1 hRz hexpR hdec
    (hd.forall_mul_mem_fusionSet_of_a6 hOut hExp hOrb hSh3 hO hz hB0 rfl hA)
  have hinv := D1OneSmallData.exists_conj_eq_inv_a6 hInvK hd hz hdec rfl hA
  have hsyl := exists_sylow_inf_of_sylow hB0 h3.le_M
  obtain ⟨E, hER, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 hp R
  rw [hd.pRank_R] at hEcard
  exact h3.false_of_toral_three_ib rfl h84 h85 h93 hD2 hSch hK hperf hz.1 hz.2.1 hCz hcov hsyl
    hzT (fun r hr => (hRz r hr).symm) hexpR hfus hinv ⟨E, hER, hEel, hEcard⟩

theorem D1OneSmallData.false_of_ib_three_l34 (hUE : KFactUPrimeExc)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders) (hK : CitedBlockToralThreeIb)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hnIa : ¬ D1SmallIa p H K) (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K) (h3 : D1PhaseThree p P M H R)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) : False := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hE : (3 = 3 ∧ IsLinThreeFour K) ∨ (3 = 5 ∧ IsFi22 K) := Or.inl ⟨rfl, hL⟩
  obtain ⟨T₁, hT₁, hY, -⟩ := hd.inf_eq_glbCore_of_exc hUE hE
  obtain ⟨T, hT, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  obtain rfl : T₁ = T :=
    Sylow.ext (Subgroup.map_injective K.subtype_injective (hT₁.trans hT.symm))
  have hsolv := hΓ3 K hs hn hc T₁ hTnc hΓT hd.small (Or.inr (Or.inr hL))
  have hU3 : ¬ IsSmallUnitary 3 K := fun h => (not_l34_and_not_a6_of_u33 hO h).1 hL
  have hA6 : ¬ IsAltTwoP 3 K := fun h => not_l34_of_a6 hO h hL
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = 3 ^ 2 := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective,
      hSh3 K hs hn hc T₁ hTnc hΓT hd.small hU3]
  obtain ⟨hR, hdec⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut (fun _ _ => hOR))
  have hperf := hd.perf_barM_of_eq h3 hY (hSch K hs hn hc) hsolv hR
  have hcov := hd.cover_ib_three rfl hz hnIa h3 h84 h86 hD2 hCz hR
  have hexpR := hd.pow_eq_one_of_d1LiftX_decomp hExp hz hdec
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  obtain ⟨hdvd, hinv₁, hinv₂⟩ := D1OneSmallData.fusion_count hd hz hB0 hdec hexpR
  have hT1 : (((d1LiftX 3 H R K : Subgroup G) : Set G) \ {1}).ncard = 3 ^ 2 - 1 := by
    obtain ⟨-, hTc⟩ := hd.d1LiftX_facts hz
    rw [Set.ncard_sdiff_singleton_of_mem (d1LiftX 3 H R K).one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) (hTc.trans hcard)
  rcases hd.orbit_sizes hOrb hz hdec (fun h => by omega) hcard with h | ⟨-, h5, -⟩ | ⟨hA, -⟩
  · have h8 := eq_eight_of_dvd (h _ hinv₁) (h _ hinv₂) hdvd
    have heq := Set.eq_of_subset_of_ncard_le hinv₂.1 (by rw [h8, hT1])
    have hz1 : z ≠ 1 := fun h1 => by
      have := hz.2.1
      rw [h1, orderOf_one] at this
      omega
    have hzt : ∀ t ∈ d1LiftX 3 H R K, z * t ∈ fusionSet R z := by
      intro t ht
      by_cases ht1 : t = 1
      · rw [ht1, mul_one]; exact self_mem_fusionSet hz1
      · have : t ∈ {t | t ∈ d1LiftX 3 H R K ∧ z * t ∈ fusionSet R z} \ {1} :=
          heq ▸ ⟨ht, ht1⟩
        exact this.1.2
    have hfus := mem_fusionSet_of_not_mem_of_mul (d1LiftX_le 3 H R K) hz.1 hRz hexpR hdec hzt
    have hinv := hd.exists_conj_eq_inv hOrb hz hdec rfl hA6 hcard
    have hsyl := exists_sylow_inf_of_sylow hB0 h3.le_M
    obtain ⟨E, hER, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 hp R
    rw [hd.pRank_R] at hEcard
    exact h3.false_of_toral_three_ib rfl h84 h85 h93 hD2 hSch hK hperf hz.1 hz.2.1 hCz hcov hsyl
      (hd.d1LiftX_facts hz).1 (fun r hr => (hRz r hr).symm) hexpR hfus hinv
      ⟨E, hER, hEel, hEcard⟩
  · omega
  · exact absurd hA hA6


end CFSG.AGLEmbedding
