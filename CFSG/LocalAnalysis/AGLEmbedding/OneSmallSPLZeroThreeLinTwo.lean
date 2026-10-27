module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeScalar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeTorus
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbRest
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreScalar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem barM_le_centralizer_pCore_or_four_le_pRank_of_scalar {X : Subgroup G} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hXM : X ≤ M) (hXel : IsElemAbelian p X) (hXcard : Nat.card X = p ^ 2)
    {t : G} (htM : t ∈ M) (htX : t ∈ Subgroup.normalizer (X : Set G))
    (hirr : ∀ k : ℕ, ¬ (p + 1) / 2 ∣ k → ∀ Y : Subgroup G, Y ≤ X →
      t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X)
    {l : ℕ} (hlcop : Nat.Coprime (l - 1) p)
    (htl : ∀ x ∈ X, t ^ ((p + 1) / 2) * x * (t ^ ((p + 1) / 2))⁻¹ = x ^ l)
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsp : s ≠ p) :
    barM M X ≤ Subgroup.centralizer
        ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
          Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      4 ≤ CFSG.Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) := by
  have hp2 : p ≠ 2 := by omega
  by_cases hns : barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M))
  · exact Or.inl hns
  right
  have := Fact.mk hs
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hcardXb : Nat.card (barM M X) = p ^ 2 := (card_barM_of_elem hp hp2 hXM hXel).trans hXcard
  have hrank : 4 ≤ CFSG.Open.pRank s Sg := by
    refine CFSG.AGLEmbeddingD2.stmtOddCoreRankScalar hs hs2 hp hp5 hsp Sg (barM M X)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩) l CFSG.pCore_isPGroup (le_top.trans hSgN)
      (isElemAbelian_barM_of hXel) hcardXb (hSgN (Subgroup.mem_top _))
      (mem_normalizer_barM htM htX) ?_ ?_ ?_ hns
    · intro hdvd
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hlcop) hdvd
    · rintro _ ⟨⟨x, hxM⟩, hxX, rfl⟩
      rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, ← map_pow]
      congr 1
      exact Subtype.ext (by simpa using htl x (Subgroup.mem_subgroupOf.mp hxX))
    · intro k hk0 hkr Y₀ hY₀ hY₀c hkY₀
      have htk : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ^ k =
          QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t ^ k, M.pow_mem htM k⟩ := by
        rw [← map_pow]
        rfl
      rw [htk] at hkY₀
      rcases eq_bot_or_eq_barM_of_mem_normalizer hXM (M.pow_mem htM k)
          (Subgroup.pow_mem _ htX k) (hirr k (Nat.not_dvd_of_pos_of_lt hk0 hkr)) hY₀ hkY₀ with
        h | h
      · rw [h, Subgroup.card_bot] at hY₀c
        exact hp.one_lt.ne hY₀c
      · rw [h, hcardXb] at hY₀c
        have : p < p ^ 2 := by nlinarith [hp.two_le]
        omega
  have h1 := pRank_barM_le hs hs2 M
    ((Sg.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) (Subgroup.map_subtype_le _)
  rw [barM_preimage] at h1
  omega

theorem D1OneSmallData.false_of_posZero_ib_linTwo_five [Fact p.Prime]
    (hK7 : KFactOneLieSmallLie) (hK8 : KFactSmallBorelSolvable) (hβ : KFactBeta)
    (hKO : KFactOneLie) (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier)
    (hα : KFactThreeOrFiveDvd) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hKF : KFactBlockCentRankIb)
    (hK2s : KFactAltSixSevenAutFive) (hK3 : CitedBlockTransvectionCyclic)
    (hK4 : CitedBlockAltNormalizerSq) (hd : D1OneSmallData p P M H R Rbar K)
    (hnIa : ¬ D1SmallIa p H K) (hp5 : 5 ≤ p) (hL : IsSmallLinTwo p K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hSP : D1CzSP p z) (hout : D1CzOutside p z)
    (hV : d1MapPCore p M H = ⊥) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hd.cfg.red.ne_two
  obtain ⟨T₁, hT₁, hF, hs, h3⟩ := hd.exists_oneLieFacts hK7 hK8 hp5 (Or.inl hL)
  obtain ⟨t, htK, htz, htX, hirr, l, hl0, hlcop, htl⟩ :=
    hd.exists_irr_linTwo_period_cz h3 hL hp5 hz
  obtain ⟨hzR, hzp, hzH, -⟩ := id hz
  have hzM : z ∈ M := hd.cfg.ext.le_M hzR
  have hzK : z ∈ H ⊓ M := ⟨hzH, hzM⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmkM
  set zb := mkM ⟨z, hzM⟩ with hzb
  set X := d1LiftX p H R K with hXdef
  set S := pCoreOf 2 H with hS
  have hZ : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → W = ⊥ :=
    fun W hWp hWz => hd.eq_bot_of_perfect_le_centralizer hβ hKO hΓ hSch hz hSP hout hzM hWp hWz
  have hB3 : ∀ L : Subgroup G, IsWeakSBlock M S L → BlockHasThree M S L :=
    fun L hL' => stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3' hK5' h3 hL'
  have hXz := hd.d1LiftX_le_centralizer hz
  obtain ⟨D, hDp, hDK, hXD, hzD, hDpart⟩ :=
    hd.exists_perfect_section h3 hT₁ hF.uPrime hF.outer_solvable hs hz hnIa hXz
  have hzbD : zb ∈ D := hzD hzM
  have hzp' : z ^ p = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzbp : zb ^ p = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hzM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hzp')
    rw [this, map_one]
  obtain ⟨hXel, hXcard⟩ := hd.isElemAbelian_d1LiftX_linTwo h3 hL
  have hXK : X ≤ H ⊓ M := (d1LiftX_le p H R K).trans h3.le_inf
  have hzX : z ∉ X := (hd.d1LiftX_facts hz).1
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨T, hT, -, -, -, -, -, -⟩ := hd.exists_sylow
  have hcoat : IsCoatom (Subgroup.normalizer ((T : Subgroup K) : Set K)) :=
    (smallRankOneData_of_small hp hp5 (Or.inl hL) T).maximal
  have hY₀T := hd.cfg.red.le_normalizer_of_borel_coatom hd.comp hd.noncyclic hd.z T hT hcoat
  have hperf : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ d1PlusCore p H K := by
    intro L hL' hLL
    exact le_d1PlusCore_of_map_le (hL'.trans inf_le_left)
      (le_centralizer_of_perfect_of_solvable T hT
        (solvable_automizer_of_isSmallLinTwo hp2 hL T) hY₀T
        (Subgroup.map_mono (Subgroup.subgroupOf_mono H hL'))
        (commutator_map_eq_self (hL'.trans inf_le_left) hLL))
  have hcyc : ∀ Y' : Subgroup G, Y' ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y', Y'⁆ = Y' →
      ∀ A : Subgroup G, A ≤ Y' → IsPGroup p A → IsCyclic A := fun Y' hY hperf' A hAY hA =>
    hd.isCyclic_of_le_d1PlusCore (hAY.trans
      (hperf Y' (h3.inf_eq_inf_normalizer_twoCore ▸ hY) hperf')) hA
  have hOp := pCore_eq_bot_of_posZero h3 h84 hD2 hV
  have hBr : CFSG.Open.pRank p (barM M (H ⊓ M)) ≤ 3 :=
    (pRank_barM_le hp hp2 M (H ⊓ M) inf_le_right).trans (hd.pRank_le_three_of_le_H inf_le_left)
  have hNSH : Subgroup.normalizer (S : Set G) = H := h3.normalizer_twoCore_H
  have hDS : D ≤ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hDK.trans (barM_le_normalizer_barM (inf_le_left.trans hNSH.ge))
  have hJM := perfectCyclicSylow_barM (S := S) (L := M) le_rfl hp hcyc
  have hNSM : Subgroup.normalizer (S : Set G) ⊓ M = H ⊓ M := by rw [hNSH]
  have hDcyc : ∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ D → IsPGroup p A → IsCyclic A :=
    fun A hAD hA => hJM D (hNSM ▸ hDK) hDp A hAD hA
  have hXL : ∀ L' : Subgroup G, IsWeakSBlock M S L' → X ≤ Subgroup.normalizer (L' : Set G) := by
    intro L' hL' x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    have hxp : orderOf x = p := orderOf_eq_prime (hXel.2 x hx) hx1
    exact h3.mem_normalizer_block_of_five hd.cfg.ind h85 h86 h93 hD2 hK2 hC3' hK5' hp5
      (hXK hx) hxp hL'
  have hzN : ∀ L' : Subgroup G, IsWeakSBlock M S L' → z ∈ Subgroup.normalizer (L' : Set G) :=
    fun L' hL' => h3.mem_normalizer_block_of_five hd.cfg.ind h85 h86 h93 hD2 hK2 hC3' hK5' hp5
      hzK hzp hL'
  have hDL : ∀ L' : Subgroup G, IsWeakSBlock M S L' →
      D ≤ Subgroup.normalizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L' hL' =>
    h3.le_normalizer_barM_of_perfect hd.cfg.ind hp5 hB3 hL' hDK hDp
  have hblocks : ∀ L : Subgroup G, IsWeakSBlock M S L →
      barM M X ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro L hL'
    have hzC := not_mem_centralizer_of_perfect hZ hL'.component
    have hPLK : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M (H ⊓ M) :=
      barM_mono (by rw [hNSH]; exact inf_le_inf_left H hL'.le)
    have hirrm : ∀ m : ℕ, ¬ (p + 1) / 2 ∣ m → t ^ m ∈ Subgroup.normalizer (L : Set G) →
        barM M X ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      fun m hm htm => h3.barM_le_centralizer_of_irr h84 h85 h86 h93 hD2 hSch hKF hK2s hK3 hK4
        hp5 hcyc hL' hXK (hXL L hL') hXel hXcard ((H ⊓ M).pow_mem htK m) htm
        (Subgroup.pow_mem _ htX m) (hirr m hm) hDp (hDL L hL') hDS hDcyc
        (fun V hVP hVp k hk => hDpart V (hVP.trans hPLK) hVp k hk) hzbD hzbp hzC hZ hXD
    obtain ⟨m, hm1, hm3, htm⟩ := h3.exists_pow_mem_normalizer_block hd.cfg.ind hp5 hB3 hL' htK
    by_cases hmr : (p + 1) / 2 ∣ m
    · have hle := Nat.le_of_dvd (by omega) hmr
      have hr3 : (p + 1) / 2 = 3 := by omega
      have hm : m = 3 := by
        obtain ⟨c, hc⟩ := hmr
        rw [hr3] at hc
        omega
      subst hm
      by_cases ht1 : t ∈ Subgroup.normalizer (L : Set G)
      · exact hirrm 1 (by rw [hr3]; decide) (by simpa using ht1)
      by_cases ht2 : t ^ 2 ∈ Subgroup.normalizer (L : Set G)
      · exact hirrm 2 (by rw [hr3]; decide) ht2
      exact (h3.false_of_three_blocks_scalar h84 h86 hD2 hSch hOp hBr hL' htK ht1 ht2 htm hXK
        hXel hXcard hXL hzK hzp' hzX hXz hzN htz hlcop hl0 (by rw [← hr3]; exact htl) hDp hDK
        hDL hzbD hZ).elim
    · exact hirrm m hmr htm
  have hcompall : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      barM M X ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro Lb hLb
    obtain ⟨L, hL2, rfl, hw | hle⟩ := h3.exists_weakSBlock_or_le_inf hLb
    · exact hblocks L hw
    · by_cases hLN : L ≤ GLBPrimeCore p H
      · exact (h3.false_of_component_le_primeCore hd.cfg.ind hp5 hα hSch hL2 hLN hDp hDK hzbD
          hzbp hZ).elim
      · exact barM_le_centralizer_of_commutator_mem h3 hL2 (hle.trans inf_le_left) hLN
          (hXK.trans inf_le_right) (hXK.trans inf_le_left)
          (fun x hx l hl => hd.commutator_mem_primeCore_of_mem_d1PlusCore hx
            (hperf L hle hL2.perfect hl))
  have hodd := fun s (hs : s.Prime) (hs2 : s ≠ 2) (hsp : s ≠ p) =>
    barM_le_centralizer_pCore_or_four_le_pRank_of_scalar hp hp5 (hXK.trans inf_le_right) hXel
      hXcard htK.2 htX hirr hlcop htl hs hs2 hsp
  have hY := hd.pCorePreimage_inf_ne_bot_of_core h3 hF.uPrime h84 hD2 le_rfl hd.d1LiftX_ne_bot
    hcompall hodd
  obtain ⟨-, -, -, -, hWiff⟩ := hd.d1MapPCore_facts h3 h84 hD2
  apply hWiff.mp hY
  rw [hV, bot_inf_eq]

@[expose] def D1SmallSPLZeroIbRest3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    IsSPLFamily p K → D1CzSP p z → D1CzOutside p z → d1MapPCore p M H = ⊥ → p = 3 → False

theorem d1SmallSPLZeroIbRest2_of_rest3 (hK7 : KFactOneLieSmallLie)
    (hK8 : KFactSmallBorelSolvable) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3' : CitedBlockThreeTransvection) (hK5' : KFactBlockThreeAltSeven)
    (hKF : KFactBlockCentRankIb) (hK2s : KFactAltSixSevenAutFive)
    (hK3 : CitedBlockTransvectionCyclic) (hK4 : CitedBlockAltNormalizerSq)
    (h : D1SmallSPLZeroIbRest3) : D1SmallSPLZeroIbRest2 := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hspl hSP hout hV h3I hcase
  rcases hcase with h3 | ⟨h5, hU⟩
  · exact h G p P M H R Rbar K hd huniq z hz hspl hSP hout hV h3
  · have : Fact p.Prime := ⟨hd.cfg.red.prime⟩
    have hnIa : ¬ D1SmallIa p H K := h3I.resolve_left (by omega)
    have hL : IsSmallLinTwo p K := by
      rcases hspl with hl | hu | ⟨h3', -⟩
      · exact hl
      · exact absurd hu hU
      · omega
    exact hd.false_of_posZero_ib_linTwo_five hK7 hK8 hβ hKO hΓ hSch hα h84 h85 h86 h93 hD2 hK2
      hC3' hK5' hKF hK2s hK3 hK4 hnIa (by omega) hL hz hSP hout hV

theorem d1SmallSPLZeroIbRest2_of_rest3'
    (hK7 : KFactOneLieSmallLie)
    (hK8 : KFactSmallBorelSolvable) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3' : CitedBlockThreeTransvection) (hK5' : KFactBlockThreeAltSeven)
    (hKF : KFactBlockCentCycIb) (hK3 : CitedBlockTransvectionCyclic)
    (hK4 : CitedBlockAltNormalizerSq) (h : D1SmallSPLZeroIbRest3) : D1SmallSPLZeroIbRest2 :=
  d1SmallSPLZeroIbRest2_of_rest3 hK7 hK8 hβ hKO hΓ hSch hα h84 h85 h86 h93 hD2
    hK2 hC3' hK5' (kFactBlockCentRankIb_of_cyc hKF) kFactAltSixSevenAutFive hK3 hK4 h

end CFSG.AGLEmbedding
