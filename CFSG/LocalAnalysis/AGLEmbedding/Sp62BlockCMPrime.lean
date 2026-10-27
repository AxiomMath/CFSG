module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockCMSmall
import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockCMPrimeTorus
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSP
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockCMAlpha

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactU62OmegaTenThreeCentAut : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex),
    (IsUSixTwoIndex d ∨ IsOmegaMinusTwoIndex 5 d) → Nonempty (L ≃* CatGroup d) →
    ∀ x : L, orderOf x = 3 →
      (∃ D : Subgroup L, D ≤ Subgroup.centralizer ({x} : Set L) ∧ ⁅D, D⁆ = D ∧
        3 ∣ Nat.card D) ∨
      Nat.card (Subgroup.centralizer ({MulAut.conj x} : Set (MulAut L))) ∣ 2 ^ 7 * 3 ^ 7

section Branches

variable {G : Type} [Group G] [Finite G] {M L H : Subgroup G} {x : G}
  {Tb : Sylow 3 (Subgroup.centralizer ({x} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)}
  {KC : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)}

theorem orderOf_barM_mk_eq_three (hx3 : orderOf x = 3) (hxM : x ∈ M)
    (hxbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ barM M L) :
    orderOf (⟨_, hxbL⟩ : barM M L) = 3 := by
  have hO2 : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  rw [Subgroup.orderOf_mk]
  exact orderOf_mk_of_coprime Nat.prime_three _ hO2 (by rw [← Subgroup.orderOf_coe]; exact hx3)

theorem false_of_perfect_centralizer_of_not_mem (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier)
    (hred : ReducedNongeneration 3 (Subgroup.centralizer ({x} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3) Tb
      (((Subgroup.centralizer ({x} : Set G) ⊓ M).subgroupOf
        (Subgroup.centralizer ({x} : Set G))).map (QuotientGroup.mk' (primeComplementCore 3))))
    (hR4 : 4 ≤ CFSG.Open.pRank 3 (Tb : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)))
    (hcat : CatalogSimpleSections (Subgroup.centralizer ({x} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3))
    (hzZ : QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)
      ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ Subgroup.center _)
    (hx3 : orderOf x = 3) (hKC : IsComponentOf KC ⊤) (hKCn : KC.Normal)
    (huniqC : ∀ L' : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3),
        IsComponentOf L' ⊤ → L' = KC)
    (hzK : QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)
      ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∉ KC) (hxM : x ∈ M)
    (hxbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ barM M L)
    {D' : Subgroup (barM M L)}
    (hD'C : D' ≤ Subgroup.centralizer ({⟨_, hxbL⟩} : Set (barM M L)))
    (hD'p : ⁅D', D'⁆ = D') (hD'3 : 3 ∣ Nat.card D') : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hO2 : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hxMp : orderOf (⟨x, hxM⟩ : M) = 3 := by rw [← Subgroup.orderOf_coe]; exact hx3
  have hzp : orderOf (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer
      ({x} : Set G)) 3) ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) = 3 :=
    orderOf_mk_of_coprime hp _ (primeComplementCore_coprime 3)
      (by rw [← Subgroup.orderOf_coe]; exact hx3)
  have hDbC : D'.map (barM M L).subtype ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hD'C hc)))
  have hDbp : ⁅D'.map (barM M L).subtype, D'.map (barM M L).subtype⁆ =
      D'.map (barM M L).subtype := by rw [← Subgroup.map_commutator, hD'p]
  have hDb3 : 3 ∣ Nat.card (D'.map (barM M L).subtype) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hD'3
  have hxMpg : IsPGroup 3 (Subgroup.zpowers (⟨x, hxM⟩ : M)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxMp, pow_one])
  obtain ⟨DM, hDMC, hDMp, hDM3⟩ :=
    exists_perfect_centralizer_lift (CFSG.pCore 2 ↥M) hO2 hxMpg hDbC hDbp hDb3
  have hDGC : DM.map M.subtype ≤ Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hDMC hc)))
  have hDGp : ⁅DM.map M.subtype, DM.map M.subtype⁆ = DM.map M.subtype := by
    rw [← Subgroup.map_commutator, hDMp]
  have hDG3 : 3 ∣ Nat.card (DM.map M.subtype) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hDM3
  have hcop := coprime_card_of_perfect_of_not_mem hred hR4 hcat hzZ hzp hKC hKCn huniqC hzK
    hβ hKO hΓ hSch hDGC (Subgroup.map_subtype_le _) hDGp
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop hDG3

theorem false_of_centralizer_aut_dvd_of_not_mem [hLn : (barM M L).Normal] (hβ : KFactBeta)
    (hTor : KFactOneLieTorus) (hCL : blockCentralizer M L ≤ GLBPrimeCore 3 H)
    (hred : ReducedNongeneration 3 (Subgroup.centralizer ({x} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3) Tb
      (((Subgroup.centralizer ({x} : Set G) ⊓ M).subgroupOf
        (Subgroup.centralizer ({x} : Set G))).map (QuotientGroup.mk' (primeComplementCore 3))))
    (hR4 : 4 ≤ CFSG.Open.pRank 3 (Tb : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)))
    (hcat : CatalogSimpleSections (Subgroup.centralizer ({x} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3))
    (hzZ : QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)
      ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ Subgroup.center _)
    (hx3 : orderOf x = 3) (hKC : IsComponentOf KC ⊤) (hKCn : KC.Normal)
    (hzK : QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)
      ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∉ KC) (hxM : x ∈ M)
    (hxbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ barM M L)
    (hcard : Nat.card (Subgroup.centralizer
      ({MulAut.conj (⟨_, hxbL⟩ : barM M L)} : Set (MulAut (barM M L)))) ∣ 2 ^ 7 * 3 ^ 7) :
    False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set z := QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)
    ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hzdef
  have hzp : orderOf z = 3 := orderOf_mk_of_coprime hp _ (primeComplementCore_coprime 3)
    (by rw [← Subgroup.orderOf_coe]; exact hx3)
  obtain ⟨hKs, hKnab, hKcat, hKAut, T₀, hT₀nc, hT₀Γ⟩ :=
    hred.exists_sylow_of_not_mem hR4 hcat hzZ hzp hKC hKCn hzK hβ
  obtain ⟨n', e', hF⟩ := hTor KC hKs hKnab hKcat 3 (by norm_num) T₀ hT₀nc hT₀Γ (by omega)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Tb hKCn.isSubnormal
  obtain ⟨⟨V, hVT, hVel, hVcard⟩, hn2, c, hcN, hc6, u, huT, hcu⟩ :=
    exists_torusPrime_of_sylow hF T
  set U := (Tb : Subgroup _) ⊓ KC with hU
  set V' := V.map KC.subtype with hV'
  have hV'el : IsElemAbelian 3 V' := elementary_abelian_map 3 hVel KC.subtype
  have hV'card : Nat.card V' = 3 ^ n' := by
    rw [hV', Subgroup.card_map_of_injective KC.subtype_injective, hVcard]
  have hV'U : V' ≤ U := by
    rw [← hT]
    exact Subgroup.map_mono hVT
  have hzV' : z ∉ V' := fun hzV => hzK (Subgroup.mem_inf.mp (hV'U hzV)).2
  have hz3 : z ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [hzp] at h1
  have hzTb : z ∈ (Tb : Subgroup _) := by
    have hnorm : (Subgroup.zpowers z).Normal := ⟨fun k hk g => by
      have hkc : k ∈ Subgroup.center _ := (Subgroup.zpowers_le.2 hzZ) hk
      rw [Subgroup.mem_center_iff.1 hkc g, mul_inv_cancel_right]
      exact hk⟩
    have hzpg : IsPGroup 3 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])
    exact hzpg.le_sylow_of_normal Tb (Subgroup.mem_zpowers z)
  have hU2 : 2 ≤ CFSG.Open.pRank 3 U :=
    hn2.trans (le_csSup (pRank_bddAbove 3 hp _) ⟨V', hV'U, hV'el, hV'card⟩)
  have hU3 : 3 ≤ CFSG.Open.pRank 3 (U ⊔ ((Tb : Subgroup _) ⊓
      Subgroup.centralizer (U : Set _))) := by
    have hzC : z ∈ (Tb : Subgroup _) ⊓ Subgroup.centralizer (U : Set _) :=
      ⟨hzTb, Subgroup.mem_centralizer_iff.mpr fun v _ => Subgroup.mem_center_iff.mp hzZ v⟩
    have h := succ_le_pRank_of_isElemAbelian hp hV'el hV'card
      (Subgroup.mem_centralizer_iff.mpr fun v _ => Subgroup.mem_center_iff.mp hzZ v) hz3 hzV'
      (hV'U.trans le_sup_left) (Subgroup.mem_sup_right hzC)
    omega
  have hNU : Subgroup.normalizer (U : Set _) ≤
      ((Subgroup.centralizer ({x} : Set G) ⊓ M).subgroupOf
        (Subgroup.centralizer ({x} : Set G))).map (QuotientGroup.mk' (primeComplementCore 3)) :=
    (normalizer_le_weakCore 3 inf_le_left hU2 hU3).trans hred.weakCore_le
  have hcN' : KC.subtype c ∈ Subgroup.normalizer (U : Set _) := by
    rw [← hT]
    exact Subgroup.le_normalizer_map KC.subtype ⟨c, hcN, rfl⟩
  have hc6' : Nat.Coprime (orderOf (KC.subtype c)) 6 := by
    rw [orderOf_injective KC.subtype KC.subtype_injective c]
    exact hc6
  refine false_of_torusPrime hCL le_rfl hxM hxbL hcard
    (QuotientGroup.mk' (primeComplementCore 3)) (Tb.isPGroup'.to_le inf_le_left)
    (Subgroup.le_normalizer.trans hNU) (hNU hcN') hcN' hc6'
    ⟨KC.subtype u, ?_, fun h => hcu ?_⟩
  · show KC.subtype u ∈ U
    rw [← hT]
    exact ⟨u, huT, rfl⟩
  · exact KC.subtype_injective (by rw [map_mul, map_mul, map_inv]; exact h)

theorem false_of_small_block_of_not_mem [(barM M L).Normal] (hβ : KFactBeta)
    (hKO : KFactOneLie) (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier)
    (hTor : KFactOneLieTorus) (hC : KFactU62OmegaTenThreeCentAut)
    (hCL : blockCentralizer M L ≤ GLBPrimeCore 3 H)
    (hred : ReducedNongeneration 3 (Subgroup.centralizer ({x} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3) Tb
      (((Subgroup.centralizer ({x} : Set G) ⊓ M).subgroupOf
        (Subgroup.centralizer ({x} : Set G))).map (QuotientGroup.mk' (primeComplementCore 3))))
    (hR4 : 4 ≤ CFSG.Open.pRank 3 (Tb : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)))
    (hcat : CatalogSimpleSections (Subgroup.centralizer ({x} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3))
    (hzZ : QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)
      ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ Subgroup.center _)
    (hx3 : orderOf x = 3) (hKC : IsComponentOf KC ⊤) (hKCn : KC.Normal)
    (huniqC : ∀ L' : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3),
        IsComponentOf L' ⊤ → L' = KC)
    (hzK : QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({x} : Set G)) 3)
      ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∉ KC) (hxM : x ∈ M)
    (hxbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ barM M L)
    {d' : TauCeti.ValidLieTypeIndex} (hd' : IsUSixTwoIndex d' ∨ IsOmegaMinusTwoIndex 5 d')
    (he : Nonempty (barM M L ≃* CatGroup d')) : False := by
  rcases hC (barM M L) d' hd' he ⟨_, hxbL⟩ (orderOf_barM_mk_eq_three hx3 hxM hxbL) with
    ⟨D', hD'C, hD'p, hD'3⟩ | hcard
  · exact false_of_perfect_centralizer_of_not_mem hβ hKO hΓ hSch hred hR4 hcat hzZ hx3 hKC hKCn
      huniqC hzK hxM hxbL hD'C hD'p hD'3
  · exact false_of_centralizer_aut_dvd_of_not_mem hβ hTor hCL hred hR4 hcat hzZ hx3 hKC hKCn
      hzK hxM hxbL hcard

end Branches

theorem d1Sp62CMOutResidue_of_prime (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (hTor : KFactOneLieTorus)
    (hKOm : KFactOmegaMinusThreePerfectCent) (hC : KFactU62OmegaTenThreeCentAut) :
    D1Sp62CMOutResidue := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd e L hL hCL h4 x hxR hx3
    hxH hO hA hE hY hW Tb KC hred hR4 hcat hzZ hKC hKCn huniqC hB hzK
  subst hp3
  have hLn : (barM M L).Normal := hL.2.2.1
  have hxM : x ∈ M := hcfg.ext.le_M hxR
  have hxbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ barM M L :=
    hL.2.2.2.1 ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hxR, rfl⟩
  rcases hL.2.2.2.2.2 with ⟨d', hd', he, -⟩ | ⟨m, d', hm, hd', he, -⟩
  · exact false_of_small_block_of_not_mem hβ hKO hΓ hSch hTor hC hCL hred hR4 hcat hzZ hx3 hKC
      hKCn huniqC hzK hxM hxbL (Or.inl hd') he
  · rcases Nat.lt_or_ge m 6 with hm6 | hm6
    · interval_cases m
      · exact (h4 d' hd').false he.some
      · exact false_of_small_block_of_not_mem hβ hKO hΓ hSch hTor hC hCL hred hR4 hcat hzZ hx3
          hKC hKCn huniqC hzK hxM hxbL (Or.inr hd') he
    · obtain ⟨D', hD'C, hD'p, hD'3⟩ := hKOm (barM M L) m d' hm6 hd' he ⟨_, hxbL⟩
        (orderOf_barM_mk_eq_three hx3 hxM hxbL)
      exact false_of_perfect_centralizer_of_not_mem hβ hKO hΓ hSch hred hR4 hcat hzZ hx3 hKC
        hKCn huniqC hzK hxM hxbL hD'C hD'p hD'3

end CFSG.AGLEmbedding
