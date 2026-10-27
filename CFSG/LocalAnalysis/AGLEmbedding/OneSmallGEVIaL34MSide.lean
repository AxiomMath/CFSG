module

public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtToral
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUCons
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeFusion

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.mSideAt_twoCore_inf (hUE : KFactUPrimeExc) (hO : KFactSmallThreeOrders)
    (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) (hI : D1SmallIa p H K) (hp3 : p = 3)
    (hL : IsLinThreeFour K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hA : Asc81bHyp M (pCoreOf 2 (H ⊓ M))) : D1MSideAt M (pCoreOf 2 (H ⊓ M)) := by
  obtain ⟨hN, -, -, hQU⟩ := hd.normalizer_twoCore_inf_eq hUE hO hNO h93 hD2 hI hp3 hL hS
  refine ⟨(hd.cfg.ext.isKGroup_of_isKProper hd.cfg.glob.kProper).1, hd.cfg.glob.toAGLGlobal,
    hd.cfg.ext.maxTwoLocal_M, hA, hQU, fun hle => ?_⟩
  have hUQ : pCoreOf 2 (H ⊓ M) = pCoreOf 2 M := le_antisymm hle hQU
  have hNM : Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
    (maxTwoLocal_eq_normalizer_pCoreOf M hd.cfg.ext.maxTwoLocal_M).symm
  rw [hUQ, hNM] at hN
  exact hd.cfg.ext.inf_lt_right.ne hN.symm

theorem D1OneSmallData.false_of_l34_ia_of_asc81bHyp (hUE : KFactUPrimeExc)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders)
    (hNO : KFactL34NotOrthogonal) (hK : CitedBlockToralThree)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hI : D1SmallIa p H K) (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hA : Asc81bHyp M (pCoreOf 2 (H ⊓ M))) : False := by
  have hMS := hd.mSideAt_twoCore_inf hUE hO hNO h93 hD2 hI hp3 hL hS hA
  obtain ⟨-, hNM, -, -⟩ := hd.normalizer_twoCore_inf_eq hUE hO hNO h93 hD2 hI hp3 hL hS
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hE : (3 = 3 ∧ IsLinThreeFour K) ∨ (3 = 5 ∧ IsFi22 K) := Or.inl ⟨rfl, hL⟩
  obtain ⟨T₁, hT₁, hY, -⟩ := hd.inf_eq_glbCore_of_exc hUE hE
  obtain ⟨T, hT, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  obtain rfl : T₁ = T :=
    Sylow.ext (Subgroup.map_injective K.subtype_injective (hT₁.trans hT.symm))
  have hsolv := hΓ3 K hs hn hc T₁ hTnc hΓT hd.small (Or.inr (Or.inr hL))
  have hperf : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) →
      ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y) :=
    fun Y hY' hYp => D1OneSmallData.coprime_card_of_perfect_of_eq hd hI hY (hSch K hs hn hc)
      hsolv (hY'.trans hNM.le) hYp
  have hCzU : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) := by
    intro g hg
    have hgHM : g ∈ M ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) := by
      rw [hNM]; exact ⟨hCz hg.2, hg.1⟩
    exact hgHM.2
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
    have hsyl := exists_sylow_inf_of_sylow hB0 hd.cfg.ext.le_M
    obtain ⟨E, hER, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 hp R
    rw [hd.pRank_R] at hEcard
    exact hMS.false_of_toral_three hd.cfg.ext.le_M hd.cfg.ext.normalizer_le h84 h85 h86 h93 hD2
      hK hperf hz.1 hz.2.1 hCzU hsyl
      (hd.d1LiftX_facts hz).1 (fun r hr => (hRz r hr).symm) hexpR hfus hinv
      ⟨E, hER, hEel, hEcard⟩
  · omega
  · exact absurd hA hA6

end CFSG.AGLEmbedding
