module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeLinTwo
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGamma
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.exists_kFacts_three (hUP : KFactUPrimeSmall)
    (hSTO : KFactSmallThreeOrders) (hSch : KFactCatalogSchreier)
    (hd : D1OneSmallData 3 P M H R Rbar K) (hspl : IsSPLFamily 3 K) :
    ∃ T : Sylow 3 K, (T : Subgroup K).map K.subtype =
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K ∧
      D1PhaseThree 3 P M H R ∧ KFactUPrime 3 K ∧ Group.IsSolvable (Outer K) ∧
      Group.IsSolvable (GLBCore 3 1 (T : Subgroup K)) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨T, hT, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hL4' : ¬ (3 = 3 ∧ IsLinThreeFour K) := fun h => not_linThreeFour_of_spl hSTO hspl h.2
  have hF5 : ¬ (3 = 5 ∧ IsFi22 K) := fun h => absurd h.1 (by norm_num)
  have hfam : IsAltTwoP 3 K ∨ IsSmallUnitary 3 K ∨ IsLinThreeFour K := by
    rcases hspl with h | h | ⟨-, h⟩
    · exact Or.inl (isAltTwoP_of_isSmallLinTwo_three h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  exact ⟨T, hT, hd.toPhaseThree hUP hL4' hF5,
    hUP K hs hn hc 3 hp3 (by norm_num) T hTnc hΓT hd.small hL4' hF5, hSch K hs hn hc,
    kFactSmallGammaSolvableThree K hs hn hc T hTnc hΓT hd.small hfam⟩

theorem D1OneSmallData.d1LiftX_three_facts (hSE : KFactSmallSylowExp)
    (hShp : KFactSmallSylowShape) (hd : D1OneSmallData 3 P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt 3 H R K z) :
    (∀ x ∈ d1LiftX 3 H R K, x ^ 3 = 1) ∧ 9 ≤ Nat.card (d1LiftX 3 H R K) ∧
      Nat.card (d1LiftX 3 H R K) ≤ 27 := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨T, hT, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  set X := d1LiftX 3 H R K with hXdef
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  obtain ⟨-, hXcard⟩ := hd.d1LiftX_facts hz
  have hXH : X ≤ H := d1LiftX_le_H 3 H R K
  have hTcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = Nat.card (T : Subgroup K) := by
    rw [← hT, Subgroup.card_map_of_injective K.subtype_injective]
  have hshape := hShp K hs hn hc 3 hp3 (by norm_num) T hTnc hΓT hd.small
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · have hXp : IsPGroup 3 X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le 3 H R K)
    have hxH := hXH hx
    have hxK : π ⟨x, hxH⟩ ∈ K := by
      have h1 : π ⟨x, hxH⟩ ∈ (X.subgroupOf H).map π :=
        ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      rw [hXdef, hd.cfg.map_d1LiftX_eq_inf] at h1
      exact h1.2
    obtain ⟨n, hn'⟩ := hXp ⟨x, hx⟩
    have hxn : x ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn'
    have hxn' : (⟨x, hxH⟩ : H) ^ 3 ^ n = 1 := Subtype.ext (by simpa using hxn)
    have hk : (⟨π ⟨x, hxH⟩, hxK⟩ : K) ^ 3 ^ n = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow]
      change π ⟨x, hxH⟩ ^ 3 ^ n = 1
      rw [← map_pow, hxn', map_one]
    have hk3 := hSE K hs hn hc 3 hp3 (by norm_num) T hTnc hΓT hd.small _ ⟨n, hk⟩
    have hπ1 : π (⟨x, hxH⟩ ^ 3) = 1 := by
      rw [map_pow]
      have := congrArg Subtype.val hk3
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      exact this
    have hxO : x ^ 3 ∈ GLBPrimeCore 3 H := by
      have := (mem_glbPrimeCore_iff_mk_eq_one (p := 3) (⟨x, hxH⟩ ^ 3)).mpr hπ1
      simpa using this
    have hdvd : orderOf (x ^ 3) ∣ Nat.card (GLBPrimeCore 3 H) :=
      Subgroup.orderOf_dvd_natCard _ hxO
    have hdvd2 : orderOf (x ^ 3) ∣ 3 ^ n :=
      orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, hxn, one_pow])
    have hcop : Nat.Coprime (orderOf (x ^ 3)) 3 :=
      Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_comm.mp (glbPrimeCore_coprime 3 H))
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hcop) hdvd2)
  · rw [hXcard, hTcard]
    rcases hshape with h | ⟨h, -⟩ <;> rw [h] <;> norm_num
  · rw [hXcard, hTcard]
    rcases hshape with h | ⟨h, -⟩ <;> rw [h] <;> norm_num

theorem D1OneSmallData.le_normalizer_block_of_three (hUP : KFactUPrimeSmall)
    (hSTO : KFactSmallThreeOrders) (hSE : KFactSmallSylowExp) (hShp : KFactSmallSylowShape)
    (hβ : KFactBeta) (hKO : KFactOneLie) (hΓ : KFactOneLieBorelSolvable)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hd : D1OneSmallData 3 P M H R Rbar K)
    (hspl : IsSPLFamily 3 K) (hnIa : ¬ D1SmallIa 3 H K) {z : G} (hz : D1SmallCZElt 3 H R K z)
    (hSP : D1CzSP 3 z) (hout : D1CzOutside 3 z) (hV : d1MapPCore 3 M H = ⊥) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    d1LiftX 3 H R K ≤ Subgroup.normalizer (L : Set G) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨T, hT, h3, hUPK, houtK, hsT⟩ := hd.exists_kFacts_three hUP hSTO hSch hspl
  have hXz := hd.d1LiftX_le_centralizer hz
  obtain ⟨D, hDp, hDK, -, hzD, -⟩ := hd.exists_perfect_section h3 hT hUPK houtK hsT hz hnIa hXz
  obtain ⟨hzR, hzo, hzH, -⟩ := id hz
  have hzM : z ∈ M := hd.cfg.ext.le_M hzR
  have hzK : z ∈ H ⊓ M := ⟨hzH, hzM⟩
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hzX : z ∉ d1LiftX 3 H R K := (hd.d1LiftX_facts hz).1
  obtain ⟨hXexp, hX9, hX27⟩ := hd.d1LiftX_three_facts hSE hShp hz
  have hr : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3 := hd.pRank_le_three_of_le_H inf_le_left
  have hB : CFSG.Open.pRank 3 (barM M (H ⊓ M)) ≤ 3 :=
    (pRank_barM_le hp3 (by norm_num) M (H ⊓ M) inf_le_right).trans hr
  have hB3 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      BlockHasThree M (pCoreOf 2 H) L' :=
    fun L' hL' => stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3' hK5' h3 hL'
  have hZ : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩} :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) → W = ⊥ :=
    fun W hWp hWz => hd.eq_bot_of_perfect_le_centralizer hβ hKO hΓ hSch hz hSP hout hzM hWp hWz
  exact h3.le_normalizer_block_three h84 h86 hD2 hSch (pCore_eq_bot_of_posZero h3 h84 hD2 hV) hB
    hr hB3 ((d1LiftX_le 3 H R K).trans h3.le_inf) hXexp hX9 hX27 hzK hz3 hzX hXz hDp hDK
    (fun L' hL' => h3.le_normalizer_barM_of_perfect_of_rank hr hB3 hL' hDK hDp) (hzD hzM) hZ hL

@[expose] def D1SmallSPLZeroIbRest4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D1OneSmallData 3 P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX 3 H R K)) → ∀ z : G, D1SmallCZElt 3 H R K z →
    IsSPLFamily 3 K → D1CzSP 3 z → D1CzOutside 3 z → d1MapPCore 3 M H = ⊥ →
    CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ →
    (¬ D1SmallIa 3 H K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      d1LiftX 3 H R K ≤ Subgroup.normalizer (L : Set G)) → False

theorem d1SmallSPLZeroIbRest3_of_rest4 (hUP : KFactUPrimeSmall) (hSTO : KFactSmallThreeOrders)
    (hSE : KFactSmallSylowExp) (hShp : KFactSmallSylowShape) (hβ : KFactBeta)
    (hKO : KFactOneLie) (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3' : CitedBlockThreeTransvection) (hK5' : KFactBlockThreeAltSeven)
    (h : D1SmallSPLZeroIbRest4) : D1SmallSPLZeroIbRest3 := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hspl hSP hout hV hp3
  subst hp3
  have hL4' : ¬ (3 = 3 ∧ IsLinThreeFour K) := fun h' => not_linThreeFour_of_spl hSTO hspl h'.2
  have h3 : D1PhaseThree 3 P M H R :=
    hd.toPhaseThree hUP hL4' (fun h' => absurd h'.1 (by norm_num))
  exact h G P M H R Rbar K hd huniq z hz hspl hSP hout hV (pCore_eq_bot_of_posZero h3 h84 hD2 hV)
    fun hnIa L hL => hd.le_normalizer_block_of_three hUP hSTO hSE hShp hβ hKO hΓ hSch h84 h85
      h86 h93 hD2 hK2 hC3' hK5' hspl hnIa hz hSP hout hV hL

end CFSG.AGLEmbedding
