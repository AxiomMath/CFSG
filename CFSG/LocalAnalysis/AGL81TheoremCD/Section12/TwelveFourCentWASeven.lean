module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOuterAut
public import CFSG.GroupTheory.CoprimeCentralizerRank
public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveCtxOrbit
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Conj
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransfer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_orderOf_three_not_mem_centralizer_of_alternating_seven {M L : Subgroup G}
    (hA7 : Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7))) :
    ∃ t ∈ barM M L, orderOf t = 3 ∧
      t ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨e⟩ := hA7
  let t₀ : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2,
      Equiv.Perm.IsThreeCycle.mem_alternatingGroup
        (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide))⟩
  let u₀ : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap 1 2,
      Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))⟩
  have ht₀ : orderOf t₀ = 3 := by
    rw [Subgroup.orderOf_mk]
    exact Equiv.Perm.IsThreeCycle.orderOf
      (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide))
  have hu₀ : u₀ * t₀ ≠ t₀ * u₀ := by
    decide
  refine ⟨(e.symm t₀ : ↥(barM M L)), (e.symm t₀).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e (e.symm t₀),
      e.apply_symm_apply, ht₀]
  · intro hmem
    have hUT : (e.symm u₀ : ↥(barM M L)) * (e.symm t₀ : ↥(barM M L)) =
        (e.symm t₀ : ↥(barM M L)) * (e.symm u₀ : ↥(barM M L)) := by
      apply Subtype.ext
      have h := (Subgroup.mem_centralizer_iff.mp hmem)
        ((e.symm u₀ : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M) (e.symm u₀).2
      simpa using h
    have hcontra : u₀ * t₀ = t₀ * u₀ := by
      have := congrArg e hUT
      simpa using this
    exact hu₀ hcontra

private theorem not_dvd_card_pCoreOf_two {M : Subgroup G} {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) :
    ¬ d ∣ Nat.card (pCoreOf 2 M) := by
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M).exists_card_eq
  rw [hk]
  intro hdiv
  have hdvd2 : d ∣ 2 := hd.dvd_of_dvd_pow hdiv
  exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp hdvd2)

omit [Finite G] in
private theorem commutator_le_pCoreOf_two_of_barM_le_centralizer
    {M L B W : Subgroup G} (hL : IsTwoPrimeComponent M L) (hBM : B ≤ M) (hWL : W ≤ L)
    (hBL : barM M B ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    Bracket.bracket B W ≤ pCoreOf 2 M := by
  rw [Subgroup.commutator_le]
  intro b hb w hw
  change b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 M
  have hbM : b ∈ M := hBM hb
  have hwM : w ∈ M := hL.le (hWL hw)
  have hb_bar : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ ∈ barM M B :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
  have hw_bar : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hwM⟩ ∈ barM M L :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hWL hw))
  have hcomm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hwM⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hwM⟩ :=
    Subgroup.mem_centralizer_iff.mp (hBL hb_bar) _ hw_bar
  have hmemM : b * w * b⁻¹ * w⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hbM hwM) (M.inv_mem hbM)) (M.inv_mem hwM)
  change M.subtype ⟨b * w * b⁻¹ * w⁻¹, hmemM⟩ ∈ (CFSG.pCore 2 ↥M).map M.subtype
  rw [Subgroup.mem_map_iff_mem M.subtype_injective, ← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hwM⟩ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩)⁻¹ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hwM⟩)⁻¹ = 1
  rw [← hcomm]
  group

theorem exists_map_conj_le_centralizer_of_barM_le_centralizer {M L B W : Subgroup G}
    (hL : IsTwoPrimeComponent M L) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) (hB : IsPGroup d B)
    (hBM : B ≤ M)
    (hBL : barM M B ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hW : IsPGroup 3 W) (hWL : W ≤ L) :
    ∃ u ∈ M, B.map (MulAut.conj u).toMonoidHom ≤ Subgroup.centralizer (W : Set G) := by
  have hWM : W ≤ M := hWL.trans hL.le
  have hSN : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) M
  obtain ⟨u, huS, hu⟩ :=
    @CFSG.GroupTheory.exists_map_conj_le_centralizer_of_commutator_le G _ _ d 3
      ⟨hd⟩ ⟨by norm_num⟩ (pCoreOf 2 M) B W
      (hBM.trans hSN) (hWM.trans hSN) hB hW
      (not_dvd_card_pCoreOf_two hd (by omega))
      (not_dvd_card_pCoreOf_two (by norm_num) (by norm_num))
      (commutator_le_pCoreOf_two_of_barM_le_centralizer hL hBM hWL hBL)
  exact ⟨u, CFSG.LieType.BorelTits.pCoreOf_le (r := 2) M huS, hu⟩

private theorem range_le_inner_of_elemAbelian_alternating_seven
    {M L E : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hA7 : Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hE : CFSG.Open.IsElemAbelian d E) (ψ : E →* MulAut ↥(barM M L)) :
    ψ.range ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(barM M L) := by
  obtain ⟨e⟩ := hA7
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  obtain ⟨-, -, hA⟩ := quot_center_alternating_of_mulEquiv hq e
  rintro α ⟨x, rfl⟩
  apply mem_inner_of_quot_center_alternating hq (by norm_num : 5 ≤ 7) hA
  have hxd : x ^ d = 1 := by
    apply Subtype.ext
    exact hE.2 (x : G) x.2
  have hψd : ψ x ^ d = 1 := by rw [← map_pow, hxd, map_one]
  exact Odd.of_dvd_nat (hd.odd_of_ne_two (by omega)) (orderOf_dvd_of_pow_eq_one hψd)

private theorem sq_le_card_ker_of_elemAbelian_alternating_seven
    {M L E : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hA7 : Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hE : CFSG.Open.IsElemAbelian d E) (hcard : Nat.card E = d ^ 3)
    (ψ : E →* MulAut ↥(barM M L)) :
    d ^ 2 ≤ Nat.card ψ.ker := by
  obtain ⟨e⟩ := hA7
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  obtain ⟨-, -, hA⟩ := quot_center_alternating_of_mulEquiv hq e
  have hrank : CFSG.Open.pRank d (⊤ : Subgroup ↥(barM M L)) ≤ 1 := by
    rw [CFSG.LocalAnalysis.RankThreeUC.S15.lieOddRankAlt_holds (K := ↥(barM M L)) hq 7
      (by norm_num) hA d hd (by omega)]
    have h : 7 / d ≤ 7 / 5 := Nat.div_le_div_left hd5 (by norm_num)
    omega
  have hZ : ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L)) :=
    (pRank_add_one_le_of_quot_center_alternating hq (by norm_num) hA hd hd5).2
  have hEtop : CFSG.Open.IsElemAbelian d (⊤ : Subgroup ↥E) :=
    @CFSG.Open.isElemAbelian_of_isElementaryAbelian (↥E) _ d (⊤ : Subgroup ↥E)
      (CFSG.IsElementaryAbelian.of_mulEquiv (Subgroup.topEquiv).symm hE.isElementaryAbelian)
  have hErange : CFSG.Open.IsElemAbelian d ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact CFSG.SectionRank.isElemAbelian_map hEtop ψ
  have hrange : Nat.card ψ.range ≤ d :=
    card_le_of_isElemAbelian_le_inner hd hZ hrank hErange
      (range_le_inner_of_elemAbelian_alternating_seven hL ⟨e⟩ hd hd5 hE ψ)
  have hprod := Subgroup.card_ker_mul_card_range ψ
  have hle : d ^ 2 * Nat.card ψ.range ≤ Nat.card ψ.ker * Nat.card ψ.range := by
    calc d ^ 2 * Nat.card ψ.range ≤ d ^ 2 * d := Nat.mul_le_mul_left _ hrange
      _ = d ^ 3 := by ring
      _ = Nat.card E := hcard.symm
      _ = Nat.card ψ.ker * Nat.card ψ.range := hprod.symm
  exact Nat.le_of_mul_le_mul_right hle Nat.card_pos

private theorem exists_mulAut_hom_and_barM_ker_le_centralizer
    {M L E : Subgroup G} (hEM : E ≤ M)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) :
    ∃ ψ : E →* MulAut ↥(barM M L),
      barM M (ψ.ker.map E.subtype) ≤
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  let ψ₀ : E →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hEM)
  let φ : E →* Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    MonoidHom.codRestrict ψ₀
      (Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
      (fun x => CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.mem_normalizer_barM
        (hEM x.2) (hEL x.2))
  let ψ : E →* MulAut ↥(barM M L) :=
    (Subgroup.normalizerMonoidHom (H := barM M L)).comp φ
  refine ⟨ψ, ?_⟩
  have hbarE₀ : barM M (ψ.ker.map E.subtype) = ψ.ker.map ψ₀ := by
    ext x
    constructor
    · rintro ⟨m, hmE₀, rfl⟩
      obtain ⟨y, hy, hyG⟩ := Subgroup.mem_map.mp hmE₀
      refine ⟨y, hy, ?_⟩
      apply congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
      exact Subtype.ext hyG
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨(y : G), hEM y.2⟩, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem E.subtype hy)
  rw [hbarE₀]
  rintro x ⟨y, hy, rfl⟩
  have hψy : ψ y = 1 := by simpa using hy
  have hφy : φ y ∈ (Subgroup.normalizerMonoidHom (H := barM M L)).ker := by
    show (Subgroup.normalizerMonoidHom (H := barM M L)) (φ y) = 1
    exact hψy
  rw [Subgroup.normalizerMonoidHom_ker] at hφy
  exact Subgroup.mem_subgroupOf.mp hφy

theorem exists_le_centralizer_of_alternating_seven {M L E : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (hA7 : Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) (hE : CFSG.Open.IsElemAbelian d E)
    (hcard : Nat.card E = d ^ 3) (hEM : E ≤ M) (hEL : E ≤ Subgroup.normalizer (L : Set G)) :
    ∃ E₀ : Subgroup G, E₀ ≤ E ∧ 2 ≤ CFSG.Open.pRank d E₀ ∧
      barM M E₀ ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨ψ, hcent⟩ := exists_mulAut_hom_and_barM_ker_le_centralizer hEM hEL
  have hker := sq_le_card_ker_of_elemAbelian_alternating_seven hL hA7 hd hd5 hE hcard ψ
  let E₀ : Subgroup G := ψ.ker.map E.subtype
  have hE₀pg : IsPGroup d E₀ := hE.isPGroup.to_le (Subgroup.map_subtype_le _)
  have hE₀elem : CFSG.Open.IsElemAbelian d E₀ := hE.mono (Subgroup.map_subtype_le _)
  have hd2le : d ^ 2 ≤ Nat.card E₀ := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact hker
  obtain ⟨k, hk⟩ := @IsPGroup.exists_card_eq d ↥E₀ _ ⟨hd⟩ _ hE₀pg
  have hk2 : 2 ≤ k := by
    apply (Nat.pow_le_pow_iff_right hd.one_lt).mp
    rwa [← hk]
  refine ⟨E₀, Subgroup.map_subtype_le _, ?_, hcent⟩
  have hkrank : k ≤ CFSG.Open.pRank d E₀ :=
    CFSG.SectionRank.le_pRank hd.one_lt le_rfl hE₀elem hk
  omega

theorem two_le_pRank_inf_centralizer_of_nineThreeFive {M Q H : Subgroup G} {p : ℕ}
    (h : TwelveCtx G M p Q H) (hM3 : CFSG.Open.pRank 3 M ≤ 3) {d : ℕ}
    (hd : d ∈ sigmaSet G M) (hd5 : 5 ≤ d) {L : Subgroup G} (hL : L ∈ weakBlockSet M H)
    (h5 : NineThreeFive M L) {W : Subgroup G}
    (hW : CFSG.ABGLocalTools.IsSylowOf 3 W (H ⊓ L)) :
    2 ≤ CFSG.Open.pRank d (M ⊓ Subgroup.centralizer (W : Set G)) := by
  have hdprime : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hL' : IsTwoPrimeComponent M L := hL.toIsTwoPrimeComponent
  have hA7 : Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)) := h5.2.1
  have hWL : W ≤ L := hW.le.trans inf_le_right
  have hW3 : IsPGroup 3 W := hW.isPGroup
  have hm3 : 3 ≤ CFSG.Open.pRank d M :=
    CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen.three_le_pRank_of_mem_sigmaSet
      h.cstar h.maxLocal hd
  obtain ⟨E, hEM, hEelem, hEcard⟩ :=
    @CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank G _ _ d ⟨hdprime⟩ M 3 hm3
  have hEpg : IsPGroup d E := hEelem.isPGroup
  have ht := exists_orderOf_three_not_mem_centralizer_of_alternating_seven hA7
  have hEL : E ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_isTwoPrimeComponent_of_isPGroup hL' hM3 ht hdprime hd5 hEpg hEM
  obtain ⟨E₀, hE₀E, hE₀rank, hE₀cent⟩ :=
    exists_le_centralizer_of_alternating_seven hL' hA7 hdprime hd5 hEelem hEcard hEM hEL
  obtain ⟨u, huM, hu⟩ :=
    exists_map_conj_le_centralizer_of_barM_le_centralizer hL' hdprime hd5
      (hEpg.to_le hE₀E) (hE₀E.trans hEM) hE₀cent hW3 hWL
  have hle : E₀.map (MulAut.conj u).toMonoidHom ≤
      M ⊓ Subgroup.centralizer (W : Set G) := by
    refine le_inf ?_ hu
    rintro _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem huM (hE₀E.trans hEM hy)) (M.inv_mem huM)
  calc 2 ≤ CFSG.Open.pRank d E₀ := hE₀rank
    _ = CFSG.Open.pRank d (E₀.map (MulAut.conj u).toMonoidHom) :=
        (CFSG.LocalAnalysis.RankThreeUC.pRank_cj d u E₀).symm
    _ ≤ CFSG.Open.pRank d (M ⊓ Subgroup.centralizer (W : Set G)) :=
        CFSG.SectionRank.pRank_mono hdprime.one_lt hle

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
