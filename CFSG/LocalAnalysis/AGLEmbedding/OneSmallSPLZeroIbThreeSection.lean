module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeWrap

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.exists_blockThreeIb (hUP : KFactUPrimeSmall)
    (hSTO : KFactSmallThreeOrders) (hSch : KFactCatalogSchreier) (hβ : KFactBeta)
    (hKO : KFactOneLie) (hΓ : KFactOneLieBorelSolvable) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven)
    (hd : D1OneSmallData 3 P M H R Rbar K) (hspl : IsSPLFamily 3 K) (hnIa : ¬ D1SmallIa 3 H K)
    {z : G} (hz : D1SmallCZElt 3 H R K z) (hSP : D1CzSP 3 z) (hout : D1CzOutside 3 z)
    (hOp : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) (hzM : z ∈ M) :
    ∃ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅D, D⁆ = D ∧ D ≤ barM M (H ⊓ M) ∧
      barM M (d1LiftX 3 H R K) ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ D ∧
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        D ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        BlockThreeIbHyp M (pCoreOf 2 H) L D (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨T, hT, h3, hUPK, houtK, hsT⟩ := hd.exists_kFacts_three hUP hSTO hSch hspl
  have hXz := hd.d1LiftX_le_centralizer hz
  obtain ⟨D, hDp, hDK, hXD, hzD, hDpart⟩ :=
    hd.exists_perfect_section h3 hT hUPK houtK hsT hz hnIa hXz
  set S := pCoreOf 2 H with hS
  set zb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ with hzb
  obtain ⟨hzR, hzo, hzH, -⟩ := id hz
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hzb3 : zb ^ 3 = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  have hr : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3 := hd.pRank_le_three_of_le_H inf_le_left
  have hB : CFSG.Open.pRank 3 (barM M (H ⊓ M)) ≤ 3 :=
    (pRank_barM_le hp3 (by norm_num) M (H ⊓ M) inf_le_right).trans hr
  have hZ : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → W = ⊥ :=
    fun W hWp hWz => hd.eq_bot_of_perfect_le_centralizer hβ hKO hΓ hSch hz hSP hout hzM hWp hWz
  have hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Y ≤ d1PlusCore 3 H K := by
    intro Y hY' hYY
    exact le_d1PlusCore_of_map_le (hY'.trans inf_le_left)
      (hd.le_centralizer_of_perfect hT hUPK houtK hsT
        (Subgroup.map_mono (Subgroup.subgroupOf_mono H hY'))
        (commutator_map_eq_self (hY'.trans inf_le_left) hYY))
  have hNSH : Subgroup.normalizer (S : Set G) = H := h3.normalizer_twoCore_H
  have hcyc : ∀ Y' : Subgroup G, Y' ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y', Y'⁆ = Y' →
      ∀ A : Subgroup G, A ≤ Y' → IsPGroup 3 A → IsCyclic A := fun Y' hY hperf' A hAY hA =>
    hd.isCyclic_of_le_d1PlusCore (hAY.trans
      (hperf Y' (h3.inf_eq_inf_normalizer_twoCore ▸ hY) hperf')) hA
  have hNSM : Subgroup.normalizer (S : Set G) ⊓ M = H ⊓ M := by rw [hNSH]
  have hJM := perfectCyclicSylow_barM (S := S) (L := M) le_rfl hp3 hcyc
  have hDcyc : ∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ D → IsPGroup 3 A → IsCyclic A :=
    fun A hAD hA => hJM D (hNSM ▸ hDK) hDp A hAD hA
  have hB3 : ∀ L' : Subgroup G, IsWeakSBlock M S L' → BlockHasThree M S L' :=
    fun L' hL' => stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3' hK5' h3 hL'
  have hDL : ∀ L' : Subgroup G, IsWeakSBlock M S L' →
      D ≤ Subgroup.normalizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L' hL' =>
    h3.le_normalizer_barM_of_perfect_of_rank hr hB3 hL' hDK hDp
  have hMtop : M ≠ ⊤ := fun hM => h3.not_le (hM ▸ le_top)
  have hcatM : CatalogSimpleSections ↥M :=
    catalogSimpleSections_of_isKProper h3.glob.kProper M hMtop
  have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) := hcatM.quotient _
  have hDS : D ≤ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hDK.trans (barM_le_normalizer_barM (inf_le_left.trans hNSH.ge))
  refine ⟨D, hDp, hDK, hXD, hzD hzM, fun L hL => ⟨hDL L hL, ?_⟩⟩
  have hLbC : IsComponentOf (barM M L) ⊤ := hL.component
  have hOut := isSolvable_outer_of_component hSch hLbC (hcat.isCatalogGroup_center_quotient hLbC)
  have hPLK : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M (H ⊓ M) :=
    barM_mono (by rw [hNSH]; exact inf_le_inf_left H hL.le)
  refine ⟨isKGroup_of_catalogSimpleSections hcatM, h3.asc81bHyp, hL,
    h93 G M S L (isKGroup_of_catalogSimpleSections hcatM) h3.asc81bHyp hL,
    fun hX => hD2 G h3.glob M L h3.maxTwoLocal_M hL.le hL.subnormal hX, ?_,
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hp3 hPLK).trans hB,
    perfectCyclicSylow_barM hL.le hp3 hcyc, hDp, fun d hd' =>
      h3.mem_sup_barM_of_mem_sup h84 h86 hD2 hL
        (perfect_le_sup_centralizer_of_outer hOut hDp (hDL L hL) hd') (hDS hd'),
    hDcyc, fun V hV hVp k hk => hDpart V (hV.trans hPLK) hVp k hk, hzD hzM, hzb3,
    not_mem_centralizer_of_perfect hZ hLbC, fun W _ hWp hWz => hZ W hWp hWz⟩
  refine (Nat.Prime.coprime_iff_not_dvd hp3).mpr fun h => ?_
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h
  have hw1 : ((w : barM M L) : ↥M ⧸ CFSG.pCore 2 ↥M) = 1 := by
    refine eq_one_of_mem_center_component_of_pCore hOp hLbC (w : barM M L).2 ?_ ?_
    · refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      have := Subgroup.mem_center_iff.mp w.2 ⟨l, hl⟩
      exact (congrArg Subtype.val this)
    · rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← hw, pow_orderOf_eq_one]
      rfl
  have : w = 1 := Subtype.ext (Subtype.ext hw1)
  rw [this, orderOf_one] at hw
  norm_num at hw

theorem D1PhaseThree.sq_mem_normalizer_of_coprime (h3 : D1PhaseThree 3 P M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hr : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {t : G} (ht : t ∈ H ⊓ M)
    (hcop : Nat.Coprime 3 (orderOf t)) : t ^ 2 ∈ Subgroup.normalizer (L : Set G) := by
  have hmm : ∀ (a b : G) (Q : Subgroup G), Q.map (MulAut.conj (a * b)).toMonoidHom =
      (Q.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b Q
    rw [Subgroup.map_map]
    congr 1
    ext g
    simp [MulAut.conj_apply, mul_assoc]
  have hnorm : ∀ a b : G, L.map (MulAut.conj a).toMonoidHom = L.map (MulAut.conj b).toMonoidHom →
      a⁻¹ * b ∈ Subgroup.normalizer (L : Set G) := by
    intro a b hab
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change L.map (MulAut.conj (a⁻¹ * b)).toMonoidHom = L
    rw [hmm, ← hab, ← hmm, inv_mul_cancel]
    ext g
    simp
  by_contra h2
  have h1 : t ∉ Subgroup.normalizer (L : Set G) := fun h => h2 (Subgroup.pow_mem _ h 2)
  have h3' : t ^ 3 ∉ Subgroup.normalizer (L : Set G) := by
    intro h
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by
      rcases Nat.lt_or_ge 1 (orderOf t) with h' | h'
      · exact h'
      · exfalso
        have : orderOf t = 1 := le_antisymm h' (orderOf_pos t)
        exact h1 (by rw [orderOf_eq_one_iff.mp this]; exact Subgroup.one_mem _))
    apply h1
    have : t = (t ^ 3) ^ u := by
      rw [← pow_mul, ← pow_mod_orderOf, hu, pow_one]
    rw [this]
    exact Subgroup.pow_mem _ h u
  set g : Fin 4 → G := ![1, t, t ^ 2, t ^ 3] with hg
  have hgK : ∀ j, g j ∈ H ⊓ M := by
    intro j
    fin_cases j
    · exact Subgroup.one_mem _
    · exact ht
    · exact (H ⊓ M).pow_mem ht 2
    · exact (H ⊓ M).pow_mem ht 3
  apply absurd (h3.le_pRank_three_of_injective_conj hB3 hL g hgK ?_) (by omega)
  intro i j hij
  have hn := hnorm _ _ hij
  have hinvN : ∀ k : ℕ, (t ^ k)⁻¹ ∈ Subgroup.normalizer (L : Set G) →
      t ^ k ∈ Subgroup.normalizer (L : Set G) := fun k hk => by
    simpa using Subgroup.inv_mem _ hk
  fin_cases i <;> fin_cases j <;> simp [hg] at hn ⊢
  all_goals first
    | exact h1 hn
    | exact h2 hn
    | exact h3' hn
    | exact h2 (hinvN 2 (by simpa using hn))
    | exact h3' (hinvN 3 (by simpa using hn))
    | exact h1 (by simpa [pow_succ, mul_assoc] using hn)
    | exact h2 (by simpa [pow_succ, mul_assoc] using hn)
    | exact h2 (hinvN 2 (by rwa [show (t ^ 3)⁻¹ * t = (t ^ 2)⁻¹ by group] at hn))

end CFSG.AGLEmbedding
