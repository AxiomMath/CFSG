module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBlockFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZComp
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockTypes
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBDefs
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutElemRankAut
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace CFSG.AGLEmbedding

section Toral

theorem citedBlockToralThreeAut_of_autNine (h : CitedBlockThreeAutNine) :
    CitedBlockToralThreeAut := by
  intro G _ _ M S L hK hA hL h93 hX hS hperf u hu hu3 huc hfix X hX3 hXN _ hXC
  have h9 := h G M S L hK hA hL h93 hX hS hperf u hu hu3 huc hfix X hXN hX3
  rw [hXC, Subgroup.relIndex_bot_left] at h9
  simpa using h9

theorem blockHasThree_of_inverted {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    (h : ∃ a ∈ Subgroup.normalizer (S : Set G) ⊓ L, ∃ g ∈ Subgroup.normalizer (S : Set G) ⊓ L,
      orderOf a = 3 ∧ g * a * g⁻¹ * a ∈ pCoreOf 2 M) : BlockHasThree M S L := by
  obtain ⟨a, ha, g, hg, ha3, hga⟩ := h
  refine ⟨a, ha, ?_, g, hg.2, fun hc => ?_⟩
  · rw [IsPGroup.iff_card, Nat.card_zpowers, ha3]
    exact ⟨1, by norm_num⟩
  · have h2 : a ^ 2 ∈ pCoreOf 2 M := by
      have e : a * g * a⁻¹ * g⁻¹ * (g * a * g⁻¹ * a) = a ^ 2 := by rw [sq]; group
      rw [← e]
      exact mul_mem hc hga
    have h4 : a ∈ pCoreOf 2 M := by
      have e : (a ^ 2) ^ 2 = a := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, ← ha3, pow_orderOf_eq_one,
          one_mul]
      rw [← e]
      exact pow_mem h2 2
    obtain ⟨k, hk⟩ := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 M ⟨a, h4⟩
    have hk' : a ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hd : 3 ∣ 2 ^ k := ha3 ▸ orderOf_dvd_of_pow_eq_one hk'
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd)
    omega

theorem citedBlockThreeTransvection_of_inverted (h : KFactBlockInvertedThree) :
    CitedBlockThreeTransvection :=
  fun G _ _ M S L hK hA hL hX hS _ => blockHasThree_of_inverted (h G M S L hK hA hL hX hS)

theorem kFactBlockThreeAltSeven_of_inverted (h : KFactBlockInvertedThree) :
    KFactBlockThreeAltSeven :=
  fun G _ _ M S L hK hA hL hX hS _ => blockHasThree_of_inverted (h G M S L hK hA hL hX hS)

end Toral

section Parabolic

theorem coprime_card_blockPL_of (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (h93 : NineThreeConclusion M S L) (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hPq : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → ⁅V, V⁆ = V → q.Coprime (Nat.card V)) :
    q.Coprime (Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L))) := by
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · have hns : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L) := fun hsyl =>
      hS (isSylowTwoOf_inf_of_barM hL.le hA.twoCore_le hA.twoRadical.isPGroup hsyl)
    exact coprime_card_of_nineThreeTwo hKP hL.component h2 hns hq hq5 hPq
  · exact hC3 G M S L q hK hA hL hX hS h3 hq hq5 hPq
  · exact coprime_card_of_nineThreeFour hq hq5 h4
  · exact hK5 G M S L q hK hA hL hX hS h5 hq hq5 hPq
  · exact coprime_card_of_nineThreeSix hq hq5 hPq (Or.inl h6)
  · exact coprime_card_of_nineThreeSix hq hq5 hPq (Or.inr h7)
  · exact coprime_card_of_nineThreeEight hq hq5 hPq h8

theorem kFactBlockFiveParabolic_of (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime) :
    KFactBlockFiveParabolic :=
  fun _ _ _ _ _ _ hK hA hL h93 hX hS _ hW =>
    coprime_card_blockPL_of hKP hC3 hK5 hK hA hL h93 hX hS Nat.prime_five le_rfl hW

end Parabolic

section Inverted

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_mem_pCoreOf_two_of_orderOf_eq_three {M : Subgroup G} {a : G} (ha3 : orderOf a = 3) :
    a ∉ pCoreOf 2 M := by
  intro h4
  obtain ⟨k, hk⟩ := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 M ⟨a, h4⟩
  have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hd : 3 ∣ 2 ^ k := ha3 ▸ orderOf_dvd_of_pow_eq_one hk'
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
  omega

omit [Finite G] in
theorem mk_pCore_two_eq_one_iff {M : Subgroup G} (m : M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) m = 1 ↔ (m : G) ∈ pCoreOf 2 M := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    have : (m : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := ⟨m, h, rfl⟩
    assumption
  · intro h
    have h' : (m : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := by
      exact h
    obtain ⟨m', hm', he⟩ := h'
    rwa [show m' = m from Subtype.ext he] at hm'

end Inverted

section Cyclic

variable {G : Type} [Group G] [Finite G]

theorem exists_isPGroup_le_barM_eq {M X : Subgroup G} {p : ℕ} [Fact p.Prime]
    {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hE : IsPGroup p E) (hEX : E ≤ barM M X) :
    ∃ U : Subgroup G, U ≤ X ∧ IsPGroup p U ∧ barM M U = E := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set ψ := mk.subgroupMap (X.subgroupOf M)
  have hψ : Function.Surjective ψ := mk.subgroupMap_surjective _
  have hE' : IsPGroup p (E.subgroupOf (barM M X)) := hE.comap_subtype
  obtain ⟨P, hP, hPE⟩ := exists_isPGroup_map_eq' hψ hE'
  refine ⟨(P.map (X.subgroupOf M).subtype).map M.subtype, ?_, (hP.map _).map _, ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mp w.2
  · apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨_, ⟨w, hw, rfl⟩, hwm⟩ := Subgroup.mem_subgroupOf.mp hm
      have hwm' : ((w : ↥M)) = m := Subtype.ext hwm
      have : ψ w ∈ E.subgroupOf (barM M X) := hPE ▸ Subgroup.mem_map_of_mem ψ hw
      rw [← hwm']
      exact this
    · intro e he
      have hex : (⟨e, hEX he⟩ : barM M X) ∈ P.map ψ := by
        rw [hPE]; exact Subgroup.mem_subgroupOf.mpr he
      obtain ⟨w, hw, hwe⟩ := hex
      refine ⟨(w : ↥M), Subgroup.mem_subgroupOf.mpr ⟨(w : ↥M), ⟨w, hw, rfl⟩, rfl⟩, ?_⟩
      exact congrArg Subtype.val hwe

theorem citedBlockThreeToralIbSq_of_cyclic (hC : CitedBlockTransvectionCyclic) :
    CitedBlockThreeToralIbSq := by
  intro G _ _ M S L p hK hA hL hX hS h3 hp hp5 hJ E hEP hEel hEcard
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hTM : Subgroup.normalizer (S : Set G) ⊓ L ≤ M := inf_le_right.trans hL.le
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  obtain ⟨U, hUT, hUp, hUE⟩ := exists_isPGroup_le_barM_eq hEp hEP
  have hcyc : PerfectCyclicSylow p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) := by
    intro V hV hVp A hAV hAp
    obtain ⟨k, hk⟩ := hAp.exists_card_eq
    have hk1 : k ≤ 1 := by
      by_contra hk1
      exact hJ V hV hVp (dvd_trans (pow_dvd_pow p (by omega))
        (hk ▸ Subgroup.card_dvd_of_le hAV))
    interval_cases k
    · have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (by simpa using hk)
  obtain ⟨u, huU, hgen⟩ := hC G M S L p hK hA hL hX hS h3 hp hp2 hcyc U
    (le_inf (hUT.trans hTM) (hUT.trans inf_le_left))
    (fun x hx => Subgroup.le_normalizer (Subgroup.mem_inf.mp (hUT hx)).2) hUp
  have hq := hL.component.2.2
  have hnab : ∃ a b : ↥(barM M L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := OutElemRank.exists_noncomm_of_quasisimple hq
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  have hZL := center_eq_bot_of_isOrthogonalTwo ⟨hq.1⟩ hnab h3.2.1
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have huM : u ∈ M := hTM (hUT huU)
  have hpow : ∀ e ∈ E, ∃ k : ℕ, e = mk ⟨u, huM⟩ ^ k := by
    intro e he
    rw [← hUE] at he
    obtain ⟨⟨x, hxM⟩, hx, rfl⟩ := he
    have hxU : x ∈ U := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨k, hk⟩ := hgen x hxU
    obtain ⟨m, hmC, hm⟩ := hk
    refine ⟨k, ?_⟩
    have hmeq : m = ⟨x, hxM⟩ * (⟨u, huM⟩ ^ k)⁻¹ := Subtype.ext (by simpa using hm)
    have hz : mk m ∈ barM M L := by
      rw [hmeq]
      refine ⟨⟨x, hxM⟩ * (⟨u, huM⟩ ^ k)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
      exact L.mul_mem (Subgroup.mem_inf.mp (hUT hxU)).2 (L.inv_mem (L.pow_mem
        (Subgroup.mem_inf.mp (hUT huU)).2 k))
    have hcen : (⟨mk m, hz⟩ : barM M L) ∈ Subgroup.center (barM M L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hmC) y y.2)
    rw [hZL, Subgroup.mem_bot] at hcen
    have h1 : mk m = 1 := congrArg Subtype.val hcen
    rw [hmeq, map_mul, map_inv, mul_inv_eq_one, map_pow] at h1
    exact h1
  have huE : mk ⟨u, huM⟩ ∈ E := by
    rw [← hUE]; exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr huU)
  have hup : mk ⟨u, huM⟩ ^ p = 1 := hEel.2 _ huE
  have hle : E ≤ Subgroup.zpowers (mk ⟨u, huM⟩) := by
    intro e he
    obtain ⟨k, rfl⟩ := hpow e he
    exact Subgroup.npow_mem_zpowers _ k
  have hcard := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hEcard] at hcard
  have hord : orderOf (mk ⟨u, huM⟩) ≤ p :=
    Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hup)
  have : p ^ 2 ≤ p := hcard.trans hord
  nlinarith [hp.two_le]

end Cyclic

end CFSG.AGLEmbedding
