module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieKMax
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZCompCloseThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZClose
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaOrbit
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMData
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZComp

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Three

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.card_inf_d1PlusCore_eq_of_eq_three (hK : KFactOneLie)
    (hT : KFactOneLieTorus) (hΓ : KFactOneLieBorelSolvable) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hZc : KFactBlockCenterCyclic)
    (hExp3 : KFactBlockSylowThreeExp) (hd : D1OneLieData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hI : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hWK : d1MapPCore p M H ≤ K)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    (hp3 : p = 3) {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p) :
    Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) = p := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have h3 := hd.toPhaseThree hK
  obtain ⟨n, e, hMD⟩ := hd.mData hK hT
  set S := pCoreOf 2 H with hS
  obtain ⟨hNHM, -, -⟩ := hd.d1PlusCore_facts
  obtain ⟨L₀, hL₀⟩ := h3.exists_weakSBlock h84 hD2
  obtain ⟨a, ⟨haS, haL⟩, g, ⟨hgS, hgL⟩, ha3, hga⟩ := hΛ G M S L₀ h3.isKGroup.1
    h3.asc81bHyp hL₀ (h3.nineThree_not_one h85 hD2 hL₀).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL₀)
  have haH : a ∈ H := h3.normalizer_twoCore_H ▸ haS
  have hgH : g ∈ H := h3.normalizer_twoCore_H ▸ hgS
  have haN := hd.mem_d1PlusCore_of_mul_conj_mem hK h84 hD2 hY hU3 hL₀.toIsTwoPrimeComponent
    haH haL hgH hgL hga
  obtain ⟨k, hkN, hBc, hzB⟩ := hd.exists_mem_map_conj hL₀.toIsTwoPrimeComponent haL haN
    (ha3.trans hp3.symm) hzR hzN hzp
  set B := L₀.map (MulAut.conj k).toMonoidHom with hB
  have hkHM : k ∈ H ⊓ M := hNHM hkN
  have hkS : k ∈ Subgroup.normalizer (S : Set G) := h3.normalizer_twoCore_H.symm ▸ hkHM.1
  have hBw : IsWeakSBlock M S B := hL₀.map_conj hkHM.2 hkS
  have hBK : H ⊓ M ≤ Subgroup.normalizer (B : Set G) :=
    hd.le_normalizer_of_mem hMD hWK hzR hzN hzp hBc hzB
  have hcyc := hZc G M S B h3.isKGroup.1 h3.asc81bHyp hBw (h3.nineThree_not_one h85 hD2 hBw).1
    (h3.not_isSylowTwoOf_inf h85 hD2 hBw) p hp hd.cfg.red.ne_two
  have hVN : Subgroup.normalizer (S : Set G) ⊓ B ≤ d1PlusCore p H K :=
    hd.inf_le_d1PlusCore hK h84 hD2 hMD hY hBc hBK hcyc
  have hNV : d1PlusCore p H K ≤
      Subgroup.normalizer ((Subgroup.normalizer (S : Set G) ⊓ B : Subgroup G) : Set G) := by
    refine (le_inf ?_ (hNHM.trans hBK)).trans Subgroup.inf_normalizer_le_normalizer_inf
    intro x hx
    exact Subgroup.le_normalizer (h3.normalizer_twoCore_H.symm ▸ (hNHM hx).1)
  have hka : k * a * k⁻¹ ∈ Subgroup.normalizer (S : Set G) ⊓ B :=
    ⟨(Subgroup.normalizer (S : Set G)).mul_mem
      ((Subgroup.normalizer (S : Set G)).mul_mem hkS haS) ((Subgroup.normalizer _).inv_mem hkS),
      ⟨a, haL, rfl⟩⟩
  have hkg : k * g * k⁻¹ ∈ Subgroup.normalizer (S : Set G) ⊓ B :=
    ⟨(Subgroup.normalizer (S : Set G)).mul_mem
      ((Subgroup.normalizer (S : Set G)).mul_mem hkS hgS) ((Subgroup.normalizer _).inv_mem hkS),
      ⟨g, hgL, rfl⟩⟩
  have hka3 : orderOf (k * a * k⁻¹) = p := by
    have h1 := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective a
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    rw [h1, ha3, hp3]
  have hkga : k * g * k⁻¹ * (k * a * k⁻¹) * (k * g * k⁻¹)⁻¹ * (k * a * k⁻¹) ∈
      GLBPrimeCore p H := by
    have e : k * g * k⁻¹ * (k * a * k⁻¹) * (k * g * k⁻¹)⁻¹ * (k * a * k⁻¹) =
        k * (g * a * g⁻¹ * a) * k⁻¹ := by group
    rw [e]
    exact h3.twoCore_M_le_glbPrimeCore ((Subgroup.mem_normalizer_iff.mp
      (localGroup_le_normalizer_pCoreOf 2 M hkHM.2) _).mp hga)
  have hRV := hd.inf_d1PlusCore_le_of_mem hI hVN hNV hka hkg hka3 hkga
  have hle := hd.card_inf_d1PlusCore_le_three hK hΓ h85 h93 hD2 hExp3 hI hp3 hBw hRV hVN
  have hdvd : p ∣ Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) := by
    have h1 := Subgroup.orderOf_dvd_natCard (R ⊓ d1PlusCore p H K) ⟨hzR, hzN⟩
    rwa [hzp] at h1
  have hpos : 0 < Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) := Nat.card_pos
  set c := Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) with hcdef
  obtain ⟨m, hm⟩ := hdvd
  have hm' : c = 3 * m := by rw [hm, hp3]
  rw [hp3]
  omega

end Three

theorem d1OneLieZZ3_of (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (hCC : D1OneLieCompetitorComp)
    (hExp3 : KFactBlockSylowThreeExp) (hΛ : KFactBlockInvertedThree)
    (hZc : KFactBlockCenterCyclic) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock) :
    D1OneLieZZ3 := by
  intro G _ _ p P M H R Rbar K hd hJ hY hI hWK hU3 hno hp3 z hzR hzN hzp _
  exact hd.false_of_zz_dichotomy hK hT hSch hCC h84 hD2 hCGT hJ hY hWK hU3 hno
    (hd.card_inf_d1PlusCore_eq_of_eq_three hK hT hΓ h84 h85 h93 hD2 hΛ hZc hExp3 hY hI hWK hU3
      hp3 hzR hzN hzp)

theorem d1OneLieZZComp_of_comp (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (hCC : D1OneLieCompetitorComp)
    (hExp3 : KFactBlockSylowThreeExp) (hΛ : KFactBlockInvertedThree)
    (hZc : KFactBlockCenterCyclic) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hCGT : AschbacherLocalCGTBlock)
    (hBig : D1OneLieZZbBig) : D1OneLieZZComp := by
  intro G _ _ p P M H R Rbar K hd hJ hY hWK hU3 hno z hzR hzN hzp hzJ L hL hzL hLK hLN hLm
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hI : ∀ L' : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L' ⊤ → L' = K
  · exact d1OneLieZZaCore_of hK h84 h85 h86 h93 hD2 hKin hKP hC3 hK5 hΓ
      (d1OneLieZZ3_of hK hT hΓ hSch hCC hExp3 hΛ hZc h84 h85 h93 hD2 hCGT)
      G p P M H R Rbar K hd hJ hY hI hWK hU3 hno z hzR hzN hzp hzJ
  push Not at hI
  by_cases hc : Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) = p
  · exact hd.false_of_zz_dichotomy hK hT hSch hCC h84 hD2 hCGT hJ hY hWK hU3 hno hc
  have hsq : p ^ 2 ∣ Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) := by
    obtain ⟨k, hk⟩ := (hd.cfg.ext.isPGroup.to_le (inf_le_left :
      R ⊓ d1PlusCore p H K ≤ R)).exists_card_eq
    have hdvd : p ∣ Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) := by
      have h1 := Subgroup.orderOf_dvd_natCard (R ⊓ d1PlusCore p H K) ⟨hzR, hzN⟩
      rwa [hzp] at h1
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [hk, pow_zero] at hdvd
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one hdvd)
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hc (by rw [hk, pow_one])
    rw [hk]
    exact pow_dvd_pow p (by omega)
  obtain ⟨T₀⟩ := (inferInstance : Nonempty (Sylow 2 ↥(d1PlusCore p H K)))
  set T : Subgroup G := (T₀ : Subgroup ↥(d1PlusCore p H K)).map (d1PlusCore p H K).subtype
    with hT
  have hTN : T ≤ d1PlusCore p H K := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := T₀.isPGroup'.map _
  have hTidx : ¬ 2 ∣ (T.subgroupOf (d1PlusCore p H K)).index := by
    rw [hT, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (d1PlusCore p H K).subtype_injective]
    exact T₀.not_dvd_index
  have h3 := hd.toPhaseThree hK
  obtain ⟨H₁, ⟨hH₁, hJH₁, hQH₁, hR₁H₁⟩, hmax⟩ := Set.exists_max_image
    {H₂ : Subgroup G | GLBIsMaxTwoLocal H₂ ∧ nclIn H (d1LiftX p H R K) ≤ H₂ ∧
      pCoreOf 2 M ≤ H₂ ∧ R ⊓ Subgroup.normalizer (T : Set G) ≤ H₂}
    (fun H₂ => Nat.card (nclIn H₂ (d1LiftX p H R K))) (Set.toFinite _)
    ⟨H, hd.cfg.ext.maxTwoLocal_H, nclIn_le_self H _,
      h3.twoCore_M_le_glbPrimeCore.trans (glbPrimeCore_le p H),
      inf_le_left.trans hd.cfg.ext.le_H⟩
  by_cases hH₁H : H₁ = H
  · subst hH₁H
    exact hd.false_of_kMax_self hK h84 hD2 hCGT hY hWK hU3 hTN hT2 hTidx inf_le_right
      fun H₂ h1 h2 h3 h4 => hmax H₂ ⟨h1, h2, h3, h4⟩
  · exact hBig G p P M H R Rbar K hd hJ hY hWK hU3 hno hI hsq z hzR hzN hzp hzJ L hL hzL hLK hLN
      hLm T hTN hT2 hTidx H₁ hH₁ hH₁H hJH₁ hQH₁ hR₁H₁
      fun H₂ h1 h2 h3 h4 => hmax H₂ ⟨h1, h2, h3, h4⟩

end CFSG.AGLEmbedding
