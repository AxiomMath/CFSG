module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThree
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeMain
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPOdd
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_l34_ia_of_phaseThree (hUE : KFactUPrimeExc)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders) (hK : CitedBlockToralThree)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hI : D1SmallIa p H K) (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
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
  have hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y) :=
    fun Y hY' hYp =>
      D1OneSmallData.coprime_card_of_perfect_of_eq hd hI hY (hSch K hs hn hc) hsolv hY' hYp
  have hU3 : ¬ IsSmallUnitary 3 K := fun h => (not_l34_and_not_a6_of_u33 hO h).1 hL
  have hA6 : ¬ IsAltTwoP 3 K := fun h => not_l34_of_a6 hO h hL
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = 3 ^ 2 := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective,
      hSh3 K hs hn hc T₁ hTnc hΓT hd.small hU3]
  obtain ⟨-, hdec⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut (fun _ _ => hOR))
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
    exact h3.false_of_toral_three rfl h84 h85 h86 h93 hD2 hK hperf hz.1 hz.2.1 hCz hsyl
      (hd.d1LiftX_facts hz).1 (fun r hr => (hRz r hr).symm) hexpR hfus hinv
      ⟨E, hER, hEel, hEcard⟩
  · omega
  · exact absurd hA hA6

theorem D1OneSmallData.false_of_l34_ia (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hK : CitedBlockToralThree) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hI : D1SmallIa p H K) (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K) (hU2 : ¬ D1SmallU2Fails p M H K)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) : False :=
  hd.false_of_l34_ia_of_phaseThree hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hK h84 h85 h86 h93 hD2 hz
    hI hB0 hp3 hL hOR (hd.toPhaseThree_of_exc hUE (Or.inl ⟨hp3, hL⟩) hU2) hCz

theorem D1OneSmallData.false_of_l34_ia_of_core (hUE : KFactUPrimeExc)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders) (hK : CitedBlockToralThree)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hI : D1SmallIa p H K) (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K)
    (hU : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) : False :=
  hd.false_of_l34_ia_of_phaseThree hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hK h84 h85 h86 h93 hD2 hz
    hI hB0 hp3 hL hOR (hd.cfg.ext.toPhaseThree hd.cfg.glob hU) hCz

theorem d1SmallGEVNormalL34U2_of_ph (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hK : CitedBlockToralThree) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hPh : D1SmallGEVNormalL34Ph) : D1SmallGEVNormalL34U2 := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hcomm hnot hV hCz hcore hA
  by_cases hU : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H
  · exact D1OneSmallData.false_of_l34_ia_of_core hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hK h84 h85
      h86 h93 hD2 hd hz hI hB0 hp3 hL hOR hU hCz
  · exact hPh G p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hU hcomm hnot hV hCz
      hcore hA

end CFSG.AGLEmbedding
