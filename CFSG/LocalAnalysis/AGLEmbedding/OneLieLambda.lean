module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZComp
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaOrbit
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMData
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Reduction

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.false_of_mem_twoPrimeComponent (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (hZc : KFactBlockCenterCyclic) (hComp : D1OneLieZZComp)
    (hd : D1OneLieData p P M H R Rbar K)
    (huniq : D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)))
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    (hno : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)))
    {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p)
    (hzJ : z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆)
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) (hzL : z ∈ L) : False := by
  have hp : p.Prime := hd.cfg.red.prime
  have hp2 : p ≠ 2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have h3 := hd.toPhaseThree hK
  obtain ⟨n, e, hMD⟩ := hd.mData hK hT
  have hLK := hd.le_normalizer_of_mem hMD hWK hzR hzN hzp hL hzL
  obtain ⟨m, hm, hLm⟩ := hd.exists_weakSBlock_map_conj hK h84 hD2 hY hWK hzR hzN hzp hzJ hL hzL
  have hcyc : ∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ barM M L →
      A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsPGroup p A →
        IsCyclic A := by
    intro A hAL hAC hAp
    set c := MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨m, hm⟩) with hc
    have hbar : barM M (L.map (MulAut.conj m).toMonoidHom) = (barM M L).map c.toMonoidHom :=
      barM_map_conj hm L
    have hAC' : A.map c.toMonoidHom ≤ Subgroup.centralizer
        (barM M (L.map (MulAut.conj m).toMonoidHom) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [hbar]
      rintro _ ⟨a, ha, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨l, hl, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hAC ha) l hl]
    have h1 := hZc G M (pCoreOf 2 H) _ h3.isKGroup.1 h3.asc81bHyp hLm
      (h3.nineThree_not_one h85 hD2 hLm).1 (h3.not_isSylowTwoOf_inf h85 hD2 hLm) p hp hp2
      (A.map c.toMonoidHom) (by rw [hbar]; exact Subgroup.map_mono hAL) hAC' (hAp.map _)
    let e := A.equivMapOfInjective c.toMonoidHom c.injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact hComp G p P M H R Rbar K hd huniq hY hWK hU3 hno z hzR hzN hzp hzJ L hL hzL hLK
    (hd.inf_le_d1PlusCore hK h84 hD2 hMD hY hL hLK hcyc) ⟨m, hm, hLm⟩

theorem D1OneLieData.false_of_mem_d1PlusCore (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (hZc : KFactBlockCenterCyclic) (hComp : D1OneLieZZComp)
    (hd : D1OneLieData p P M H R Rbar K)
    (huniq : D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)))
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    (hno : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)))
    {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p)
    (hzJ : z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆)
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) {a : G} (haL : a ∈ L)
    (haN : a ∈ d1PlusCore p H K) (hap : orderOf a = p) : False := by
  obtain ⟨k, -, hLk, hzLk⟩ := hd.exists_mem_map_conj hL haL haN hap hzR hzN hzp
  exact hd.false_of_mem_twoPrimeComponent hK hT h84 h85 hD2 hZc hComp huniq hY hWK hU3 hno hzR
    hzN hzp hzJ hLk hzLk

theorem D1OneLieData.false_of_eq_three (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hZc : KFactBlockCenterCyclic) (hComp : D1OneLieZZComp)
    (hd : D1OneLieData p P M H R Rbar K)
    (huniq : D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)))
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    (hno : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)))
    (hp3 : p = 3) {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p)
    (hzJ : z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆) : False := by
  have h3 := hd.toPhaseThree hK
  obtain ⟨L, hL⟩ := h3.exists_weakSBlock h84 hD2
  obtain ⟨a, ⟨haS, haL⟩, g, ⟨hgS, hgL⟩, ha3, hga⟩ := hΛ G M (pCoreOf 2 H) L h3.isKGroup.1
    h3.asc81bHyp hL (h3.nineThree_not_one h85 hD2 hL).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL)
  have haH : a ∈ H := h3.normalizer_twoCore_H ▸ haS
  have hgH : g ∈ H := h3.normalizer_twoCore_H ▸ hgS
  have haN := hd.mem_d1PlusCore_of_mul_conj_mem hK h84 hD2 hY hU3 hL.toIsTwoPrimeComponent haH
    haL hgH hgL hga
  exact hd.false_of_mem_d1PlusCore hK hT h84 h85 hD2 hZc hComp huniq hY hWK hU3 hno hzR hzN hzp
    hzJ hL.toIsTwoPrimeComponent haL haN (ha3.trans hp3.symm)

end Reduction

theorem d1OneLieZZ3_of_comp (hK : KFactOneLie) (hT : KFactOneLieTorus) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (hD2 : D1NoXBlock) (hΛ : KFactBlockInvertedThree)
    (hZc : KFactBlockCenterCyclic) (hComp : D1OneLieZZComp) : D1OneLieZZ3 := by
  intro G _ _ p P M H R Rbar K hd huniq hY _ hWK hU3 hno hp3 z hzR hzN hzp hzJ
  exact hd.false_of_eq_three hK hT h84 h85 hD2 hΛ hZc hComp huniq hY hWK hU3 hno hp3 hzR hzN hzp
    hzJ

theorem d1OneLieZZb3_of_comp (hK : KFactOneLie) (hT : KFactOneLieTorus) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (hD2 : D1NoXBlock) (hΛ : KFactBlockInvertedThree)
    (hZc : KFactBlockCenterCyclic) (hComp : D1OneLieZZComp) : D1OneLieZZb3 := by
  intro G _ _ p P M H R Rbar K hd huniq hY _ hWK hU3 hno hp3 z hzR hzN hzp hzJ
  exact hd.false_of_eq_three hK hT h84 h85 hD2 hΛ hZc hComp huniq hY hWK hU3 hno hp3 hzR hzN hzp
    hzJ

theorem d1OneLieZZbHat_of_comp (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (hZc : KFactBlockCenterCyclic) (hComp : D1OneLieZZComp) : D1OneLieZZbHat := by
  intro G _ _ p P M H R Rbar K hd huniq hY _ hWK hU3 hno _ z hzR hzN hzp hzJ L hL hV
  exfalso
  obtain ⟨V, hV, hVp, hpV⟩ := hV
  have hp : p.Prime := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have h3 := hd.toPhaseThree hK
  have hWM : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ M := inf_le_right.trans hL.le
  obtain ⟨V', hV'W, hV'p, hV'bar⟩ := exists_perfect_le_of_le_barM hWM hV hVp
  have hV'H : V' ≤ H := hV'W.trans (inf_le_left.trans h3.normalizer_twoCore_H.le)
  have hV'N := hd.le_d1PlusCore_of_perfect hK h84 hD2 hY hU3 hL hV'H (hV'W.trans inf_le_right)
    hV'p
  have hpV' : p ∣ Nat.card V' := by
    rw [← hV'bar, barM] at hpV
    refine hpV.trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hV'W.trans hWM)).toEquiv]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hpV'
  exact hd.false_of_mem_d1PlusCore hK hT h84 h85 hD2 hZc hComp huniq hY hWK hU3 hno hzR hzN hzp
    hzJ hL (hV'W.trans inf_le_right a.2) (hV'N a.2) (by rw [Subgroup.orderOf_coe, ha])

end CFSG.AGLEmbedding
