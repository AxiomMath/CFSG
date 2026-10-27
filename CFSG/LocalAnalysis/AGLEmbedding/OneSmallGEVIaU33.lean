module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorusFamilies
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVEven
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaFrame
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaMSide
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_u33_ia (hUP : KFactUPrimeSmall) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hShp : KFactSmallSylowShape) (hO : KFactSmallThreeOrders)
    (hKU2 : KFactUnitarySylowStructure) (hInvU : KFactU33SylowInvert)
    (hK : CitedBlockToralThree) (hK9 : CitedBlockThreeAutNine)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hI : D1SmallIa p H K) (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hU : IsSmallUnitary 3 K)
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
  have hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y) :=
    fun Y hY hYp => hd.coprime_card_of_perfect hI hT₁ hUPK (hSch K hs hn hc) hsolv hY hYp
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
  exact h3.false_of_u33_three rfl h84 h85 h86 h93 hD2 hK hK9 hperf hzR hzp hCz hsyl
    (fun r hr => (hRz r hr).symm) hexpR hdec hfusZ hinv hPz hR81 hP6

theorem d1SmallGEVNormalU33_of (hUP : KFactUPrimeSmall) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hShp : KFactSmallSylowShape) (hO : KFactSmallThreeOrders)
    (hKU2 : KFactUnitarySylowStructure) (hInvU : KFactU33SylowInvert)
    (hK : CitedBlockToralThree) (hK9 : CitedBlockThreeAutNine)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) : D1SmallGEVNormalU33 := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 _ _ hp3 hU _ _ _ hCz _ _
  exact hd.false_of_u33_ia hUP hSch hΓ3 hOut hExp hShp hO hKU2 hInvU hK hK9 h84 h85 h86 h93 hD2
    hz hI hB0 hp3 hU hCz

end CFSG.AGLEmbedding
