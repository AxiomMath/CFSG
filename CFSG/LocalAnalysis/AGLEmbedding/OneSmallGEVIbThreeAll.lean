module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltAll
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbU33Main
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaFrame
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarRes
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVEven
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorusFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_ib_three_u33 (hUP : KFactUPrimeSmall)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hShp : KFactSmallSylowShape)
    (hO : KFactSmallThreeOrders) (hKU2 : KFactUnitarySylowStructure)
    (hInvU : KFactU33SylowInvert) (hOrb3 : KFactSmallOrbitsCube) (hK : CitedBlockToralThreeIb)
    (hKA : CitedBlockThreeAutCenterIb) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hnIa : ¬ D1SmallIa p H K) (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hU : IsSmallUnitary 3 K)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) : False := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hL34 : ¬ IsLinThreeFour K := (not_l34_and_not_a6_of_u33 hO hU).1
  have hL : ¬ (3 = 3 ∧ IsLinThreeFour K) := fun h => hL34 h.2
  have hF : ¬ (3 = 5 ∧ IsFi22 K) := fun h => absurd h.1 (by norm_num)
  have h3 := hd.toPhaseThree hUP hL hF
  obtain ⟨T₁, hT₁, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hUPK := hUP K hs hn hc 3 hp (by norm_num) T₁ hTnc hΓT hd.small hL hF
  have hsolv := hΓ3 K hs hn hc T₁ hTnc hΓT hd.small (Or.inr (Or.inl hU))
  obtain ⟨hRle, hdec⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (d1SmallLa_of_not hL)
  have hexpR := hd.pow_eq_one_of_d1LiftX_decomp hExp hz hdec
  set T := d1LiftX 3 H R K with hT
  have hTR : T ≤ R := d1LiftX_le 3 H R K
  have hzR : z ∈ R := hz.1
  have hzp : orderOf z = 3 := hz.2.1
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  have hUg : IsUnitaryGroup 3 K := by
    obtain ⟨d, ⟨q, hq, -, hd1⟩, he⟩ := hU
    exact ⟨d, ⟨q, hq, hd1⟩, he⟩
  have hnab := center_ne_of_unitary_of_kFact hKU2 (by norm_num) T₁ hUg
  have hT27 : Nat.card (T₁ : Subgroup K) = 27 ∧
      Nat.card (Subgroup.center (T₁ : Subgroup K)) = 3 := by
    rcases hShp K hs hn hc 3 hp (by norm_num) T₁ hTnc hΓT hd.small with h9 | ⟨h27, hZ⟩
    · exfalso
      apply hnab
      refine le_antisymm inf_le_left fun x hx => ⟨hx, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) h9
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
    · exact ⟨by rw [h27]; norm_num, hZ⟩
  obtain ⟨hzT, hTc⟩ := hd.d1LiftX_facts hz
  have hTcard : Nat.card T = 27 := by
    rw [hTc, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective, hT27.1]
  have hR81 : Nat.card R = 3 ^ 4 := by
    refine le_antisymm ?_ ?_
    · have := hRle
      rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective, hT27.1] at this
      omega
    · have hinf : T ⊓ Subgroup.zpowers z = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxT, hxz⟩
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
        by_contra hne
        exact hzT ((Subgroup.zpowers_le.mpr hxT)
          (mem_zpowers_of_mem_zpowers_of_prime hp hzp (Subgroup.zpow_mem_zpowers z j) hne))
      have h1 := mul_card_le_of_inf_eq_bot hTR (Subgroup.zpowers_le.mpr hzR) hinf
      rw [hTcard, Nat.card_zpowers, hzp] at h1
      omega
  have hinvN := hd.exists_conj_eq_inv_u33 hInvU hz hdec rfl hU
  have hinv : ∀ t ∈ T, t ≠ 1 → ∃ n ∈ M, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = t⁻¹ := by
    intro t ht ht1
    obtain ⟨n, hn, hnz, -, hnt⟩ := hinvN t ht ht1
    exact ⟨n, hd.cfg.ext.normalizer_le hn, hnz, hnt⟩
  obtain ⟨hfusZ, hZ9⟩ := hd.fusZ_u33 hz hB0 rfl hdec hexpR hT₁ hT27.2 hinvN
  have hPz : ∀ g ∈ (P : Subgroup G), g * z = z * g → g ∈ R := fun g hg hgz =>
    hd.inf_centralizer_le_of_b0 hB0 ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgz⟩
  have h4 := betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta P
  have hP6 := le_card_of_frame_81 P.isPGroup' hd.cfg.ext.le_P (by rw [hR81]; norm_num) hzR hzp
    hRz hPz hZ9 hd.pRank_R.le h4
  have hsyl := exists_sylow_inf_of_sylow hB0 h3.le_M
  have hperf := hd.perf_barM h3 hT₁ hUPK (hSch K hs hn hc) hsolv hRle
  have hcent : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) 3), W ≤ d1X0 3 M H →
      ⁅W, W⁆ = W → W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) :=
    fun W hW hWp => hd.le_centralizer_of_perfect hT₁ hUPK (hSch K hs hn hc) hsolv hW hWp
  have hcov := hd.cover_ib_three rfl hz hnIa h3 h84 h86 hD2 hCz hRle
  have hmove := hd.exists_moving_elt hz hB0
  have hcT : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = 3 ^ 3 := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective, hT27.1]
    norm_num
  have hcd : D1IbCubeThreeData 3 P M H R Rbar K z := ⟨hd, hz, hdec, hexpR, hcT⟩
  exact h3.false_of_u33_three_ib rfl hcd h84 h85 h93 hD2 hSch hShp hOrb3 hK hKA hperf hcent hcov
    hCz hsyl hfusZ hinv hPz hP6 hmove

theorem d1SmallGEVIbNormalAllRest4_of_rest6 (hUP : KFactUPrimeSmall) (hUE : KFactUPrimeExc)
    (hSch : KFactCatalogSchreier) (hΓs : KFactSmallGammaSolvableSpor)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hShp : KFactSmallSylowShape) (hO : KFactSmallThreeOrders)
    (hInvK : KFactAltSixSylowInvert) (hKU2 : KFactUnitarySylowStructure)
    (hInvU : KFactU33SylowInvert) (hOrb3 : KFactSmallOrbitsCube) (hK : CitedBlockToralThreeIb)
    (hKA : CitedBlockThreeAutCenterIb) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (h6 : D1SmallGEVIbNormalAllRest6) : D1SmallGEVIbNormalAllRest4 := by
  intro G _ _ p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
    hp3
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := centralizer_le_of_normalizer_vz_le hV
  by_cases hU3 : IsSmallUnitary 3 K
  · exact hd.false_of_ib_three_u33 hUP hSch hΓ3 hOut hExp hShp hO hKU2 hInvU hOrb3 hK hKA h84
      h85 h86 h93 hD2 hz hnIa hB0 hp3 hU3 hCz
  by_cases hL34 : IsLinThreeFour K
  · by_cases hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H
    · have h3 : D1PhaseThree p P M H R :=
        { hd.cfg.ext.toD1Escape with glob := hd.cfg.glob.toAGLGlobal, twoCore_inf := hS }
      exact hd.false_of_ib_three_l34 hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hK h84 h85 h86 h93 hD2
        hz hnIa hB0 hp3 hL34 hOR h3 hCz
    by_cases hU2 : D1SmallU2Fails p M H K
    · by_cases hcore : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H
      · exact hd.false_of_ib_three_l34 hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hK h84 h85 h86 h93
          hD2 hz hnIa hB0 hp3 hL34 hOR (hd.cfg.ext.toPhaseThree hd.cfg.glob hcore) hCz
      · exact h6 G p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar
          hns hp3 hL34 hU2 hcore hS
    · exact hd.false_of_ib_three_l34 hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hK h84 h85 h86 h93 hD2
        hz hnIa hB0 hp3 hL34 hOR (hd.toPhaseThree_of_exc hUE (Or.inl ⟨hp3, hL34⟩) hU2) hCz
  by_cases hA6 : IsAltTwoP 3 K
  · exact hd.false_of_ib_three_a6 hUP hSch hΓ3 hOut hExp hOrb hSh3 hO hInvK hK h84 h85 h86 h93
      hD2 hz hnIa hB0 hp3 hA6 hCz
  · exact hd.false_of_ib_three_m11 hUP hSch hΓs hOut hExp hOrb hSh3 hK h84 h85 h86 h93 hD2 hz
      hnIa hB0 hOR hCz hp3 hA6 hU3 hL34

end CFSG.AGLEmbedding
