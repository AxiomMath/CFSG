module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreAltSixSylow
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreFrame
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVEven
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeMain
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPFrame
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem kFactAltSixSylowInvert : KFactAltSixSylowInvert := by
  intro K _ _ hA T
  obtain ⟨e⟩ := hA
  exact exists_inv_of_sylow_altSix e T

theorem a6_count_cases {c₁ c₂ : ℕ}
    (h₁ : c₁ = 0 ∨ c₁ = 3 ^ 2 - 1 ∨ c₁ = 2 * (3 - 1) ∨ c₁ = (3 - 1) ^ 2)
    (h₂ : c₂ = 0 ∨ c₂ = 3 ^ 2 - 1 ∨ c₂ = 2 * (3 - 1) ∨ c₂ = (3 - 1) ^ 2)
    (h : 3 ∣ c₁ + (3 - 1) * (1 + c₂)) :
    (c₁ = 0 ∧ c₂ = 8) ∨ (c₁ = 4 ∧ c₂ = 0) ∨ (c₁ = 8 ∧ c₂ = 4) := by
  rcases h₁ with rfl | rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl | rfl <;> omega

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.exists_conj_eq_inv_a6 (hInvK : KFactAltSixSylowInvert)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i) (hp3 : p = 3)
    (hA : IsAltTwoP 3 K) :
    ∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∃ n ∈ M, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = t⁻¹ := by
  subst hp3
  have hp := hd.cfg.red.prime
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨T₁, hT₁, -⟩ := hd.exists_sylow
  obtain ⟨nb, hnb, hinvb⟩ := hInvK K hA T₁
  obtain ⟨n, hnN, hnz, hnπ⟩ := hd.exists_lift_of_mem_normalizer hz hdec hT₁ hnb
  intro t ht _
  refine ⟨n, hd.cfg.ext.normalizer_le hnN, hnz, ?_⟩
  obtain ⟨t', ⟨ht'R, ht'K⟩, rfl⟩ := ht
  have hO := primeComplementCore_coprime (G := H) 3
  have hRHp : IsPGroup 3 (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  have h1 : QuotientGroup.mk' (primeComplementCore (G := H) 3) t' ∈
      (T₁ : Subgroup K).map K.subtype := by
    rw [hT₁]
    exact ⟨by rw [hd.cfg.rbar]; exact ⟨t', ht'R, rfl⟩, ht'K⟩
  obtain ⟨s, hs, hseq⟩ := h1
  have h2 : QuotientGroup.mk' (primeComplementCore (G := H) 3) (n * t' * n⁻¹) =
      QuotientGroup.mk' (primeComplementCore (G := H) 3) t'⁻¹ := by
    rw [map_mul, map_mul, map_inv, hnπ, map_inv, ← hseq]
    have h3 := congrArg (fun k : K => (k : H ⧸ primeComplementCore (G := H) 3)) (hinvb s hs)
    simpa using h3
  have hmem1 : n * t' * n⁻¹ ∈ R.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    have h4 := (Subgroup.mem_normalizer_iff.mp hnN (t' : G)).mp (Subgroup.mem_subgroupOf.mp ht'R)
    simpa using h4
  have h5 := CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup hp _ hO hRHp hmem1
    ((R.subgroupOf H).inv_mem ht'R) h2
  have h6 := congrArg Subtype.val h5
  simpa using h6

theorem D1OneSmallData.comm_card_of_dec (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hp3 : p = 3)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hTcard : Nat.card (d1LiftX p H R K) = 3 ^ 2) :
    (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧ Nat.card R = 27 := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set T := d1LiftX 3 H R K with hT
  have hTR : T ≤ R := d1LiftX_le 3 H R K
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzR : z ∈ R := hz.1
  have hzp : orderOf z = 3 := hz.2.1
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  obtain ⟨hzT, -⟩ := hd.d1LiftX_facts hz
  have hTab : ∀ a b : T, a * b = b * a :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hTcard).is_comm.comm
  refine ⟨fun a ha b hb => ?_, ?_⟩
  · obtain ⟨t, ht, i, rfl⟩ := hdec a ha
    obtain ⟨s, hs, j, rfl⟩ := hdec b hb
    have hts : t * s = s * t := congrArg Subtype.val (hTab ⟨t, ht⟩ ⟨s, hs⟩)
    have hzs : Commute (z ^ i) s := (Commute.pow_left
      (show Commute z s from (hRz s (hTR hs)).symm) i)
    have hzt : Commute (z ^ j) t := (Commute.pow_left
      (show Commute z t from (hRz t (hTR ht)).symm) j)
    calc t * z ^ i * (s * z ^ j) = t * (z ^ i * s) * z ^ j := by group
      _ = t * (s * z ^ i) * z ^ j := by rw [hzs.eq]
      _ = (t * s) * (z ^ i * z ^ j) := by group
      _ = (s * t) * (z ^ j * z ^ i) := by rw [hts, ← pow_add, ← pow_add, add_comm]
      _ = s * (t * z ^ j) * z ^ i := by group
      _ = s * (z ^ j * t) * z ^ i := by rw [hzt.eq]
      _ = s * z ^ j * (t * z ^ i) := by group
  · refine le_antisymm ?_ ?_
    · have h1 := card_le_mul_of_decomp (K := T) (Subgroup.zpowers_le.mpr hzR) fun r hr => by
        obtain ⟨t, ht, i, rfl⟩ := hdec r hr
        exact ⟨t, ⟨hTR ht, ht⟩, z ^ i, Subgroup.npow_mem_zpowers z i, rfl⟩
      have h2 := Subgroup.card_le_of_le (inf_le_right : R ⊓ T ≤ T)
      rw [Nat.card_zpowers, hzp] at h1
      rw [hTcard] at h2
      calc Nat.card R ≤ Nat.card (R ⊓ T : Subgroup G) * 3 := h1
        _ ≤ 3 ^ 2 * 3 := Nat.mul_le_mul_right 3 h2
        _ = 27 := by norm_num
    · have hinf : T ⊓ Subgroup.zpowers z = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
        by_contra hy1
        have := mem_zpowers_of_mem_zpowers_of_prime hp hzp hy.2 hy1
        exact hzT ((Subgroup.zpowers_le.mpr hy.1) this)
      have h1 := mul_card_le_of_inf_eq_bot hTR (Subgroup.zpowers_le.mpr hzR) hinf
      rw [hTcard, Nat.card_zpowers, hzp] at h1
      simpa using h1

theorem D1OneSmallData.forall_mul_mem_fusionSet_of_a6 (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hA : IsAltTwoP 3 K) :
    ∀ t ∈ d1LiftX p H R K, z * t ∈ fusionSet R z := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hL34 : ¬ IsLinThreeFour K := not_l34_of_a6 hO hA
  have hL : ¬ (3 = 3 ∧ IsLinThreeFour K) := fun h => hL34 h.2
  obtain ⟨T₁, hT₁, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hU3 : ¬ IsSmallUnitary 3 K := fun h => (not_l34_and_not_a6_of_u33 hO h).2 hA
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = 3 ^ 2 := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective,
      hSh3 K hs hn hc T₁ hTnc hΓT hd.small hU3]
  obtain ⟨-, hdec⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (d1SmallLa_of_not hL)
  have hexpR := hd.pow_eq_one_of_d1LiftX_decomp hExp hz hdec
  set T := d1LiftX 3 H R K with hT
  have hTR : T ≤ R := d1LiftX_le 3 H R K
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  have hzR : z ∈ R := hz.1
  have hzp : orderOf z = 3 := hz.2.1
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hzp; omega
  obtain ⟨hzT, hTc⟩ := hd.d1LiftX_facts hz
  have hTcard : Nat.card T = 3 ^ 2 := hTc.trans hcard
  obtain ⟨hRcomm, hRcard⟩ := D1OneSmallData.comm_card_of_dec hd hz rfl hdec hTcard
  obtain ⟨hdvd, hinv₁, hinv₂⟩ := D1OneSmallData.fusion_count hd hz hB0 hdec hexpR
  set S₁ : Set G := fusionSet R z ∩ (T : Set G) with hS₁
  set O' : Set G := {t | t ∈ T ∧ z * t ∈ fusionSet R z} with hO'
  set S₂ : Set G := O' \ {1} with hS₂
  have hT1 : ((T : Set G) \ {1}).ncard = 3 ^ 2 - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem T.one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) hTcard
  have h4 := betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta P
  by_contra hne
  have hc₂ : S₂.ncard = 8 → False := by
    intro h8
    have heq := Set.eq_of_subset_of_ncard_le hinv₂.1 (by rw [hT1]; omega)
    refine hne fun t ht => ?_
    by_cases ht1 : t = 1
    · rw [ht1, mul_one]; exact self_mem_fusionSet hz1
    · have : t ∈ S₂ := heq ▸ ⟨ht, ht1⟩
      exact this.1.2
  have hstab : ∀ y ∈ Subgroup.normalizer (R : Set G), y * z = z * y →
      (∃ k : ℕ, y ^ 3 ^ k = 1) → y ∈ R := fun y hy hyz ⟨k, hk⟩ =>
    hd.mem_of_mem_normalizer_of_commute hB0 hy hyz hk
  have hO'card : O'.ncard = 1 + S₂.ncard := by
    have h1O' : (1 : G) ∈ O' := ⟨T.one_mem, by rw [mul_one]; exact self_mem_fusionSet hz1⟩
    rw [add_comm]
    exact (Set.ncard_sdiff_singleton_add_one h1O').symm
  rcases hd.orbit_sizes hOrb hz hdec (fun h => by omega) hcard with h | ⟨-, h5, -⟩ | ⟨-, h⟩
  · exact hc₂ (eq_eight_of_dvd (h _ hinv₁) (h _ hinv₂) hdvd)
  · omega
  rcases a6_count_cases (h _ hinv₁) (h _ hinv₂) hdvd with ⟨-, h8⟩ | ⟨h4', h0⟩ | ⟨h8, -⟩
  · exact hc₂ h8
  ·
    have hO : ∀ t ∈ T, z * t ∈ fusionSet R z → t = 1 := by
      intro t ht hzt
      by_contra ht1
      have : t ∈ S₂ := ⟨⟨ht, hzt⟩, ht1⟩
      have hS₂e : S₂ = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp h0
      rw [hS₂e] at this
      exact this
    have hZT : ∀ w ∈ fusionSet R z, w ∉ T → w ∈ Subgroup.zpowers z := fun w hw hwT =>
      mem_zpowers_of_mem_fusionSet_of_not_mem hp hTR hzR hRz hexpR hdec hO hw hwT
    have hcount := ncard_fusionSet_eq hp hTR hzR hzT hzp hRz hexpR hdec
    have hZ : (fusionSet R z).ncard < 9 := by
      rw [hcount, hO'card, h0]
      have : (fusionSet R z ∩ (T : Set G)).ncard = 4 := h4'
      rw [this]
      norm_num
    have hB0' : ∀ g ∈ (P : Subgroup G), g * z = z * g → g ∈ R := fun g hg hgz =>
      hd.inf_centralizer_le_of_b0 hB0 ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgz⟩
    exact false_of_frame P.isPGroup' hd.cfg.ext.le_P hRcomm hexpR hRcard hTR
      (by simpa using hTcard) hzR hzT hzp hB0' hZ hZT h4
  ·
    have heq := Set.eq_of_subset_of_ncard_le hinv₁.1 (by rw [hT1]; omega)
    have hTZ : ∀ t ∈ T, t ≠ 1 → t ∈ fusionSet R z := fun t ht ht1 => by
      have : t ∈ S₁ := heq ▸ ⟨ht, ht1⟩
      exact this.1
    exact false_of_frame_dual P.isPGroup' hd.cfg.ext.le_P hRcomm hRcard hTR
      (by simpa using hTcard) hzR hzp hstab hTZ h4

theorem D1OneSmallData.false_of_a6_ia (hUP : KFactUPrimeSmall) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hInvK : KFactAltSixSylowInvert) (hK : CitedBlockToralThree)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hI : D1SmallIa p H K) (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hA : IsAltTwoP 3 K)
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
  have hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y) :=
    fun Y hY hYp => hd.coprime_card_of_perfect hI hT₁ hUPK (hSch K hs hn hc) hsolv hY hYp
  obtain ⟨-, hdec⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (d1SmallLa_of_not hL)
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
  exact h3.false_of_toral_three rfl h84 h85 h86 h93 hD2 hK hperf hz.1 hz.2.1 hCz hsyl hzT
    (fun r hr => (hRz r hr).symm) hexpR hfus hinv ⟨E, hER, hEel, hEcard⟩

end CFSG.AGLEmbedding
