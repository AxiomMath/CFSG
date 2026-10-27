module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props316
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Proof
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm29
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Residual

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {𝒜 : Thm13Ambient}

theorem isQuasisimple_of_oddCoreIn_le_centralizer {K C : Subgroup G} (hK : IsTwoComponentIn K C)
    (h : oddCoreIn K ≤ centralizer (K : Set G)) : IsQuasisimple ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥K :=
    Subgroup.isPerfect_iff.mpr (UnbalancedCorr.commutator_eq_of_isPComponent hK.1 hK.2)
  have hq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K C hK.1).mp hK.2).2.2
  refine (LocalCores.isQuasisimple_iff_of_surjective hperf (QuotientGroup.mk' (pPrimeCore 2 ↥K))
    (QuotientGroup.mk'_surjective _) ?_).mpr hq
  rw [QuotientGroup.ker_mk']
  intro x hx
  rw [mem_center_iff]
  intro y
  have h1 : (x : G) ∈ centralizer (K : Set G) := h ⟨x, hx, rfl⟩
  exact Subtype.ext ((mem_centralizer_iff.mp h1) y y.2)

omit [Finite G] in
theorem solomonKStarOf_eq_sSup (N : Subgroup G) : solomonKStarOf N = sSup (kStarComponents N) := by
  rw [sSup_eq_iSup]
  rfl

omit [Finite G] in
theorem solomonKStarOf_le (N : Subgroup G) : solomonKStarOf N ≤ N :=
  iSup₂_le fun _ hK => hK.1.1

omit [Finite G] in
theorem solomonKStarOf_le_twoLayerIn (N : Subgroup G) : solomonKStarOf N ≤ twoLayerIn N :=
  iSup₂_le fun _ hK => le_twoLayerIn_of_isTwoComponentIn hK.1

theorem commutator_eq_bot_of_mem_kStarComponents (h315a : Lemma315aInputFor 𝒜) (hG : 𝒜 G)
    {N : Subgroup G} (hN : IsSolomonChoice N) {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') : ⁅K, K'⁆ = ⊥ := by
  set D := solomonKStarOf N with hD
  have hKD : K ≤ D := le_iSup₂_of_le K hK le_rfl
  have hK'D : K' ≤ D := le_iSup₂_of_le K' hK' le_rfl
  have hDN : D ≤ N := solomonKStarOf_le N
  have h1 : ⁅K, K'⁆ ≤ oddCoreIn D := FooteLit.commutator_le_oddCoreIn_of_ne
    (isTwoComponentIn_of_le hK.1 hKD hDN) (isTwoComponentIn_of_le hK'.1 hK'D hDN) hne
  have h2 : ⁅K, K'⁆ ≤ centralizer (K : Set G) :=
    (h1.trans (h315a G hG N hN)).trans (centralizer_le hKD)
  have hperf : Group.IsPerfect ↥K :=
    Subgroup.isPerfect_iff.mpr (UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2)
  exact LocalCores.perfect_double_commutator hperf (commutator_eq_bot_iff_le_centralizer.mpr h2)

theorem isQuasisimple_of_mem_kStarComponents (h315a : Lemma315aInputFor 𝒜) (hG : 𝒜 G)
    {N : Subgroup G} (hN : IsSolomonChoice N) {K : Subgroup G} (hK : K ∈ kStarComponents N) :
    IsQuasisimple ↥K := by
  have hKD : K ≤ solomonKStarOf N := le_iSup₂_of_le K hK le_rfl
  have hKc := isTwoComponentIn_of_le hK.1 hKD (solomonKStarOf_le N)
  exact isQuasisimple_of_oddCoreIn_le_centralizer hK.1
    (((oddCoreIn_le_of_isTwoComponentIn hKc).trans (h315a G hG N hN)).trans (centralizer_le hKD))

theorem exists_orderOf_eq_two_of_mem_solomonKStar {K : Subgroup G} (hK : K ∈ solomonKStar G) :
    ∃ b ∈ K, orderOf b = 2 :=
  exists_orderOf_eq_two_of_pRank (le_trans (by norm_num) (two_le_pRank_of_mem_solomonKStar hK))

theorem oddCoreIn_twoLayerIn_le (C : Subgroup G) : oddCoreIn (twoLayerIn C) ≤ oddCoreIn C := by
  have hle : oddCoreIn (twoLayerIn C) ≤ C := (map_subtype_le _).trans (map_subtype_le _)
  have hn : C ≤ normalizer (oddCoreIn (twoLayerIn C) : Set G) := fun c hc =>
    mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (le_normalizer_twoLayerIn C hc))
  have h := inf_le_oddCoreIn (coprime_card_oddCoreIn (twoLayerIn C)) hn
  rwa [inf_eq_left.mpr hle] at h

theorem isTwoComponentIn_centralizer_of_ne (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜)
    (h315c : Lemma315cInputFor 𝒜) (hG : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N)
    {K K' : Subgroup G} (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {b : G} (hb : b ∈ K) (hb2 : orderOf b = 2) :
    IsTwoComponentIn K' (centralizer ({b} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({b} : Set G) with hC
  set U := zpowers b with hU
  have hCU : centralizer (U : Set G) = C := by rw [hU, zpowers_eq_closure, centralizer_closure]
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hUne : U ≠ ⊥ := fun h => by
    rw [hU, zpowers_eq_bot] at h
    rw [h, orderOf_one] at hb2
    norm_num at hb2
  have hcomm := commutator_eq_bot_of_mem_kStarComponents h315a hG hN hK hK' hne
  have hbK' : b ∈ centralizer (K' : Set G) := commutator_eq_bot_iff_le_centralizer.mp hcomm hb
  have hK'C : K' ≤ C := fun y hy => by
    rw [hC, mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp hbK') y hy
  have hK'U : K' ⊓ centralizer (U : Set G) = K' := by rw [hCU]; exact inf_eq_left.mpr hK'C
  have hK'tl : twoLayerIn K' = K' := twoLayerIn_eq_self_of_isTwoComponentIn hK'.1
  have hUQ : U ≤ coreActionKernel K' := by
    rw [hU, zpowers_le]
    exact Sol78.mem_coreActionKernel_of_commute fun k hk =>
      mem_centralizer_singleton_iff.mp (hK'C hk)
  have h212 := lemma212Input G K' U hK'.2 hUne hU2 hUQ
  rw [hK'U, hK'tl, hCU] at h212
  have h32' := h32 G hG N hN K hK K' hK' hne b hb hb2 hK'C
  rw [← hC, inf_eq_left.mpr hK'C, hK'tl] at h32'
  have hK'L : K' ≤ twoLayerIn C := h212.trans (solomonKStarOf_le_twoLayerIn C)
  have hinv := exists_orderOf_eq_two_of_mem_solomonKStar hK'.2
  obtain ⟨M, ⟨hMC, hMs⟩, hmove⟩ := exists_not_le_coreActionKernel hK'.1 h212 hinv
  have hMle : M ≤ oddCoreIn C ⊔ K' :=
    ((le_conjClosure_of_not_le_coreActionKernel hMC hK'L hmove).trans h32').trans
      (sup_le_sup_right (oddCoreIn_twoLayerIn_le C) _)
  have hK'M : K' ≤ M := by
    set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
    obtain ⟨Mb, hMb, -, hMmap, -⟩ := hMC.2
    set K'' := K'.subgroupOf C with hK''
    set Kb := K''.map π with hKb
    have e0 : (oddCoreIn C).subgroupOf C = pPrimeCore 2 ↥C := by
      rw [oddCoreIn, ← comap_subtype, comap_map_eq_self_of_injective C.subtype_injective]
    have h1 : M.subgroupOf C ≤ pPrimeCore 2 ↥C ⊔ K'' := by
      have h := comap_mono (f := C.subtype) hMle
      rw [comap_subtype, comap_subtype,
        subgroupOf_sup (show oddCoreIn C ≤ C from map_subtype_le _) hK'C, e0] at h
      exact h
    have h2 : Mb ≤ Kb := by
      rw [← hMmap]
      calc (M.subgroupOf C).map π ≤ (pPrimeCore 2 ↥C ⊔ K'').map π := map_mono h1
        _ = Kb := by
          rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' _).ge,
            bot_sup_eq]
    have hKq : IsQuasisimple ↥Kb := by
      have hK'q := isQuasisimple_of_mem_kStarComponents h315a hG hN hK'
      have hK''q : IsQuasisimple ↥K'' :=
        LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hK'C).symm hK'q
      refine LocalCores.isQuasisimple_map hK''q π fun hle => ?_
      obtain ⟨x, hx, hx2⟩ := hinv
      have hxO : (⟨x, hK'C hx⟩ : ↥C) ∈ pPrimeCore 2 ↥C := by
        rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥C)]
        exact hle (mem_subgroupOf.mpr hx)
      have h3 := orderOf_dvd_natCard (⟨⟨x, hK'C hx⟩, hxO⟩ : pPrimeCore 2 ↥C)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hx2] at h3
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (pPrimeCore_coprime_card (p := 2) (G := ↥C)) h3
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hKq
        (hMb.2.subgroupOf (K := Kb)) with htop | hcen
    · have h4 : Kb ≤ Mb := fun x hx => by
        have : (⟨x, hx⟩ : ↥Kb) ∈ Mb.subgroupOf Kb := htop ▸ mem_top _
        exact mem_subgroupOf.mp this
      have h5 : K'' ≤ M.subgroupOf C ⊔ pPrimeCore 2 ↥C := by
        have h6 : K'' ≤ ((M.subgroupOf C).map π).comap π := by
          rw [← map_le_iff_le_comap, hMmap]
          exact h4
        rwa [comap_map_eq, QuotientGroup.ker_mk'] at h6
      have h7 : K' ≤ oddCoreIn C ⊔ M := by
        intro x hx
        have hx' : (⟨x, hK'C hx⟩ : ↥C) ∈ M.subgroupOf C ⊔ pPrimeCore 2 ↥C :=
          h5 (mem_subgroupOf.mpr hx)
        have := mem_map_of_mem C.subtype hx'
        rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hMC.1, sup_comm] at this
        exact this
      have hres : CatalogueBPrimeJoin.primeResidual 2 ↥K' = ⊤ :=
        ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K' N hK'.1.1).mp hK'.1.2).2.1
      have h8 := Sol78.le_oPrimeResidualOf h7 hres
      rwa [show oddCoreIn C = GH74.GLS.pPrimeCoreOf 2 C from rfl,
        Sol78.oPrimeResidualOf_core_sup_eq hMC.1 hMC.2] at h8
    · exfalso
      obtain ⟨a, c, hac⟩ := hMb.1.2.2
      induction a using QuotientGroup.induction_on with
      | H a =>
      induction c using QuotientGroup.induction_on with
      | H c =>
      apply hac
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      have ha : (⟨a, h2 a.2⟩ : ↥Kb) ∈ Mb.subgroupOf Kb := mem_subgroupOf.mpr a.2
      have h3 := congrArg Subtype.val (mem_center_iff.mp (hcen ha) ⟨c, h2 c.2⟩)
      exact h3.symm
  have hMK' : M = K' := by
    refine le_antisymm ?_ hK'M
    have hMKb : M ≤ solomonKStarOf C := le_iSup₂_of_le M ⟨hMC, hMs⟩ le_rfl
    have hMKbc : IsTwoComponentIn M (solomonKStarOf C) :=
      isTwoComponentIn_of_le hMC hMKb (solomonKStarOf_le C)
    have hOM : oddCoreIn M ≤ centralizer (M : Set G) :=
      ((oddCoreIn_le_of_isTwoComponentIn hMKbc).trans (h315c G hG N hN K hK b hb hb2)).trans
        (centralizer_le hMKb)
    have hdec : ∀ m ∈ M, ∃ o ∈ oddCoreIn M, ∃ k ∈ K', m = o * k := by
      intro m hm
      have hK'n : K' ≤ normalizer (oddCoreIn C : Set G) :=
        hK'C.trans (le_normalizer_oddCoreIn C)
      obtain ⟨o, ho, k, hk, rfl⟩ := exists_mul_of_mem_sup_normalizer hK'n (hMle hm)
      refine ⟨o, ?_, k, hk, rfl⟩
      have hoM : o ∈ M := by
        have : o = o * k * k⁻¹ := by group
        rw [this]
        exact mul_mem hm (inv_mem (hK'M hk))
      exact inf_le_oddCoreIn (coprime_card_oddCoreIn C) (hMC.1.trans (le_normalizer_oddCoreIn C))
        ⟨ho, hoM⟩
    have hMp : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hMC.1 hMC.2
    rw [← hMp]
    refine commutator_le.mpr fun x hx y hy => ?_
    obtain ⟨o, ho, k, hk, rfl⟩ := hdec x hx
    obtain ⟨o', ho', k', hk', rfl⟩ := hdec y hy
    have hkM := hK'M hk
    have hk'M := hK'M hk'
    have ho'M : o' ∈ M := (map_subtype_le _) ho'
    have h1 : o * (k * o' * k' * k⁻¹) = (k * o' * k' * k⁻¹) * o :=
      ((mem_centralizer_iff.mp (hOM ho)) _
        (mul_mem (mul_mem (mul_mem hkM ho'M) hk'M) (inv_mem hkM))).symm
    have h2 : o' * (k' * k⁻¹ * k'⁻¹) = (k' * k⁻¹ * k'⁻¹) * o' :=
      ((mem_centralizer_iff.mp (hOM ho')) _
        (mul_mem (mul_mem hk'M (inv_mem hkM)) (inv_mem hk'M))).symm
    have e : ⁅o * k, o' * k'⁆ = ⁅k, k'⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc o * k * (o' * k') * (o * k)⁻¹ * (o' * k')⁻¹
          = o * (k * o' * k' * k⁻¹) * o⁻¹ * k'⁻¹ * o'⁻¹ := by group
        _ = (k * o' * k' * k⁻¹) * o * o⁻¹ * k'⁻¹ * o'⁻¹ := by rw [h1]
        _ = k * (o' * (k' * k⁻¹ * k'⁻¹)) * o'⁻¹ := by group
        _ = k * ((k' * k⁻¹ * k'⁻¹) * o') * o'⁻¹ := by rw [h2]
        _ = k * k' * k⁻¹ * k'⁻¹ := by group
    rw [e, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hk hk') (inv_mem hk)) (inv_mem hk')
  rw [← hMK']
  exact hMC

omit [Finite G] in
theorem mem_normalizer_sSup {𝒮 : Set (Subgroup G)} {x : G}
    (h : ∀ K ∈ 𝒮, x ∈ normalizer (K : Set G)) : x ∈ normalizer ((sSup 𝒮 : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hφ := fun K (hK : K ∈ 𝒮) => mem_normalizer_iff_map_conj_eq.mp (h K hK)
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← map_le_iff_le_comap, hφ K hK]
    exact le_sSup hK
  · refine sSup_le fun K hK => ?_
    rw [← hφ K hK]
    exact map_mono (le_sSup hK)

theorem kStarComponents_subset_normalizer (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜)
    (h315c : Lemma315cInputFor 𝒜) (hG : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N)
    {𝒮 : Set (Subgroup G)} (h𝒮 : 𝒮 ⊆ kStarComponents N) (hne : 𝒮.Nonempty) :
    kStarComponents N ⊆ kStarComponents (normalizer ((sSup 𝒮 : Subgroup G) : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro K' hK'
  refine ⟨?_, hK'.2⟩
  set D₀ := sSup 𝒮 with hD₀
  set N' := normalizer (D₀ : Set G) with hN'
  have hprops := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K' N hK'.1.1).mp hK'.1.2
  by_cases hin : K' ∈ 𝒮
  · have hK'D₀ : K' ≤ D₀ := le_sSup hin
    have hD₀n : D₀ ≤ normalizer (K' : Set G) := sSup_le fun K hK => by
      by_cases h : K = K'
      · rw [h]; exact le_normalizer
      · exact (commutator_eq_bot_iff_le_centralizer.mp
          (commutator_eq_bot_of_mem_kStarComponents h315a hG hN (h𝒮 hK) hK' h)).trans
          (centralizer_le_normalizer _)
    have hsub : (K'.subgroupOf N').IsSubnormal :=
      isSubnormal_subgroupOf_of_le_normalizer hK'D₀ le_normalizer hD₀n le_rfl
    exact ⟨hK'D₀.trans le_normalizer, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K' N'
      (hK'D₀.trans le_normalizer)).mpr ⟨hsub, hprops.2⟩⟩
  · obtain ⟨K, hK𝒮⟩ := hne
    have hKK' : K ≠ K' := fun h => hin (h ▸ hK𝒮)
    obtain ⟨b, hbK, hb2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar (h𝒮 hK𝒮).2
    have hA := isTwoComponentIn_centralizer_of_ne h32 h315a h315c hG hN (h𝒮 hK𝒮) hK' hKK' hbK hb2
    set CD := centralizer (D₀ : Set G) with hCD
    have hCDb : CD ≤ centralizer ({b} : Set G) :=
      centralizer_le (Set.singleton_subset_iff.mpr (le_sSup hK𝒮 hbK))
    have hD₀C : D₀ ≤ centralizer (K' : Set G) := sSup_le fun J hJ =>
      commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_mem_kStarComponents h315a hG hN
        (h𝒮 hJ) hK' fun h => hin (h ▸ hJ))
    have hK'CD : K' ≤ CD := by
      intro k hk
      rw [hCD, mem_centralizer_iff]
      intro x hx
      exact ((mem_centralizer_iff.mp (hD₀C hx)) k hk).symm
    have hK'c : IsTwoComponentIn K' CD :=
      ⟨hK'CD, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hK'CD hCDb hA.2⟩
    have hCDN : CD ≤ N' := centralizer_le_normalizer _
    have hCDn : (CD.subgroupOf N').IsSubnormal := Normal.isSubnormal
      ((normal_subgroupOf_iff_le_normalizer hCDN).mpr (le_normalizer_centralizer le_rfl))
    exact ⟨hK'CD.trans hCDN, GrSLit.isPComponent_subgroupOf_of_isSubnormal hK'CD hCDN hCDn hK'c.2⟩

theorem kStarComponents_eq_of_isKBalanced {N N' : Subgroup G} (hN : IsSolomonChoice N)
    (hN' : IsKBalanced N') (hsub : kStarComponents N ⊆ kStarComponents N') :
    kStarComponents N' = kStarComponents N := by
  have hle : solomonKStarOf N ≤ solomonKStarOf N' := by
    rw [solomonKStarOf_eq_sSup, solomonKStarOf_eq_sSup]
    exact sSup_le_sSup hsub
  have hviol : ¬ solomonKStarOf N' ≤ solomonKStarOf (⊤ : Subgroup G) := fun h =>
    hN.2.1 (hle.trans h)
  have hmeas := hN.2.2 N' hN' hviol
  have hcard' : (kStarComponents N').ncard ≤ (kStarComponents N).ncard := by
    by_contra hlt
    push Not at hlt
    apply absurd hmeas
    rw [not_le]
    unfold kStarMeasure
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
  exact (Set.eq_of_subset_of_ncard_le hsub hcard').symm

theorem normalizer_sSup_le (hbal : Lemma316BalancedInputFor 𝒜) (hG : 𝒜 G)
    {N : Subgroup G} (hN : IsSolomonChoice N)
    {𝒮 : Set (Subgroup G)} (h𝒮 : 𝒮 ⊆ kStarComponents N) (hne : 𝒮.Nonempty) :
    normalizer ((sSup 𝒮 : Subgroup G) : Set G) ≤ normalizer (solomonKStarOf N : Set G) := by
  have heq := hbal G hG N hN 𝒮 h𝒮 hne
  have hK : solomonKStarOf (normalizer ((sSup 𝒮 : Subgroup G) : Set G)) = solomonKStarOf N := by
    rw [solomonKStarOf_eq_sSup, heq, ← solomonKStarOf_eq_sSup]
  have h1 := le_normalizer_solomonKStarOf (normalizer ((sSup 𝒮 : Subgroup G) : Set G))
  rwa [hK] at h1

theorem exists_mem_kStarComponents_ne {N : Subgroup G} (hN : IsSolomonChoice N) (K : Subgroup G) :
    ∃ K' ∈ kStarComponents N, K' ≠ K := by
  obtain ⟨r, Kf, hinj, hiff, h2r, -⟩ := hN.1
  have hmem : ∀ i, Kf i ∈ kStarComponents N := fun i => (hiff (Kf i)).mpr ⟨i, rfl⟩
  have hne01 : Kf ⟨0, by omega⟩ ≠ Kf ⟨1, h2r⟩ := fun h => by
    have := hinj h
    simp at this
  by_cases h : Kf ⟨0, by omega⟩ = K
  · exact ⟨Kf ⟨1, h2r⟩, hmem _, fun h' => hne01 (h.trans h'.symm)⟩
  · exact ⟨Kf ⟨0, by omega⟩, hmem _, h⟩

theorem twoLayerIn_centralizer_le_twoLayerIn_normalizer (h32 : Lemma32InputFor 𝒜)
    (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜)
    (hG : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N) {K : Subgroup G}
    (hK : K ∈ kStarComponents N) {b : G} (hb : b ∈ K) (hb2 : orderOf b = 2) :
    twoLayerIn (centralizer ({b} : Set G)) ≤
      twoLayerIn (normalizer (solomonKStarOf N : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({b} : Set G) with hC
  set H := normalizer (solomonKStarOf N : Set G) with hH
  set 𝒮₀ := kStarComponents N \ {K} with h𝒮₀def
  have h𝒮₀ : 𝒮₀ ⊆ kStarComponents N := Set.sdiff_subset
  have hne₀ : 𝒮₀.Nonempty := by
    obtain ⟨K', hK', hne⟩ := exists_mem_kStarComponents_ne hN K
    exact ⟨K', hK', fun h => hne (Set.mem_singleton_iff.mp h)⟩
  have hA : ∀ K' ∈ 𝒮₀, IsTwoComponentIn K' C := fun K' hK' =>
    isTwoComponentIn_centralizer_of_ne h32 h315a h315c hG hN hK hK'.1
      (fun h => hK'.2 (Set.mem_singleton_iff.mpr h.symm)) hb hb2
  have hLC : twoLayerIn C ≤ H := by
    refine le_trans ?_ (normalizer_sSup_le hbal hG hN h𝒮₀ hne₀)
    intro x hx
    exact mem_normalizer_sSup fun K' hK' =>
      twoLayerIn_le_normalizer (hA K' hK').1 (hA K' hK').2 hx
  have hKD : K ≤ solomonKStarOf N := le_iSup₂_of_le K hK le_rfl
  have hbH : b ∈ H := le_normalizer (hKD hb)
  have hU2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have h1 := GrSLit.pLayer_inf_centralizer_le (Y := H) (A := zpowers b) (zpowers_le.mpr hbH) hU2
  have hCz : centralizer ((zpowers b : Subgroup G) : Set G) = C := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hCz] at h1
  refine le_trans ?_ h1
  rw [twoLayerIn, map_le_iff_le_comap]
  refine sSup_le fun M hM => ?_
  rw [← map_le_iff_le_comap]
  have hM'C : IsTwoComponentIn (M.map C.subtype) C := ⟨map_subtype_le _, by
    rw [← comap_subtype, comap_map_eq_self_of_injective C.subtype_injective]; exact hM⟩
  have hM'H : M.map C.subtype ≤ H ⊓ C :=
    le_inf ((le_twoLayerIn_of_isTwoComponentIn hM'C).trans hLC) hM'C.1
  exact le_twoLayerIn_of_isTwoComponentIn (isTwoComponentIn_of_le hM'C hM'H inf_le_right)

theorem lemma316InputFor_of_inputs (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜)
    (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜)
    (hprod : Lemma316ProductInputFor 𝒜) : Lemma316InputFor 𝒜 := by
  intro G _ _ hG N hN
  classical
  refine ⟨?_, fun K hK b hb hb2 => ?_⟩
  ·
    obtain ⟨K, hK, -⟩ := exists_mem_kStarComponents_ne hN ⊥
    have hne : (kStarComponents N).Nonempty := ⟨K, hK⟩
    have heq := hbal G hG N hN _ le_rfl hne
    rw [← solomonKStarOf_eq_sSup] at heq
    rw [solomonKStarOf_eq_sSup (normalizer (solomonKStarOf N : Set G)), heq,
      ← solomonKStarOf_eq_sSup]
  ·
    set C := centralizer ({b} : Set G) with hC
    have hLCH :=
      twoLayerIn_centralizer_le_twoLayerIn_normalizer h32 h315a h315c hbal hG hN hK hb hb2
    have h𝒥 : kStarComponents C ⊆ kStarComponents N := fun J hJ =>
      hprod G hG N hN K hK b hb hb2 J hJ.1 hJ.2
        ((le_twoLayerIn_of_isTwoComponentIn hJ.1).trans hLCH)
    have hne𝒥 : (kStarComponents C).Nonempty := by
      obtain ⟨K', hK', hne⟩ := exists_mem_kStarComponents_ne hN K
      exact ⟨K', isTwoComponentIn_centralizer_of_ne h32 h315a h315c hG hN hK hK'
        (fun h => hne h.symm) hb hb2, hK'.2⟩
    have h1 := normalizer_sSup_le hbal hG hN h𝒥 hne𝒥
    rw [← solomonKStarOf_eq_sSup] at h1
    exact (le_normalizer_solomonKStarOf C).trans h1

theorem lemma316Input_of_inputs (h32 : Lemma32Input) (h315a : Lemma315aInput)
    (h315c : Lemma315cInput) (hbal : Lemma316BalancedInput) (hprod : Lemma316ProductInput) :
    Lemma316Input :=
  lemma316InputFor_of_inputs h32 h315a h315c hbal hprod

end CFSG.ComponentClassification.Sol76
