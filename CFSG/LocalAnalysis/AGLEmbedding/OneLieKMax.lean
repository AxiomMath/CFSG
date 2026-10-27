module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieKMaxIndex
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZNAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem eq_of_maxTwoLocal_of_kMax {P' : Sylow p G} {S H₁ X J R₁ : Subgroup G}
    (h3 : D1PhaseThree p P' M H₁ S) (hXS : X ≤ S) (hX1 : X ≠ ⊥) (hXH₁ : X ≤ H₁)
    (hJJ₁ : J ≤ nclIn H₁ X) (hJ₁ : nclIn (nclIn H₁ X) X = nclIn H₁ X)
    (hmax : ∀ H₂ : Subgroup G, GLBIsMaxTwoLocal H₂ → J ≤ H₂ → pCoreOf 2 M ≤ H₂ → R₁ ≤ H₂ →
      Nat.card (nclIn H₂ X) ≤ Nat.card (nclIn H₁ X))
    (H₂ : Subgroup G) (hH₂ : GLBIsMaxTwoLocal H₂) (hJH₂ : nclIn H₁ X ≤ H₂)
    (hRQ : R₁ ⊔ pCoreOf 2 M ≤ H₂) : H₂ = H₁ := by
  have hle : nclIn H₁ X ≤ nclIn H₂ X := by
    calc nclIn H₁ X = nclIn (nclIn H₁ X) X := hJ₁.symm
      _ ≤ nclIn H₂ X := nclIn_le_nclIn_of_le (le_nclIn hXH₁) hJH₂
  have heq : nclIn H₁ X = nclIn H₂ X := Subgroup.eq_of_le_of_card_ge hle
    (hmax H₂ hH₂ (hJJ₁.trans hJH₂) (le_sup_right.trans hRQ) (le_sup_left.trans hRQ))
  have hJn' : ((nclIn H₁ X).subgroupOf H₂).Normal := heq ▸ nclIn_normal H₂ X
  have hAJ : pCoreOf 2 (GLBPrimeCore p (nclIn H₁ X)) ≤ nclIn H₁ X :=
    (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans (glbPrimeCore_le p _)
  have hNA : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p (nclIn H₁ X)) : Set G) = H₁ :=
    maxTwoLocal_normalizer_eq_of_normal h3.maxTwoLocal_H (h3.pCoreOf_two_primeCore_ne_bot hXS hX1)
      (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _) (hAJ.trans (nclIn_le_self H₁ X))
      (normal_pCoreOf_two_glbPrimeCore p (nclIn_le_self H₁ X) (nclIn_normal H₁ X))
  have hH₂H₁ : H₂ ≤ H₁ := hNA ▸ (Subgroup.normal_subgroupOf_iff_le_normalizer
    (hAJ.trans hJH₂)).mp (normal_pCoreOf_two_glbPrimeCore p hJH₂ hJn')
  exact (hH₂.2 H₁ h3.maxTwoLocal_H.1 hH₂H₁).symm

theorem twoCore_le_of_sylowTwo {H₁ N₁ T : Subgroup G} (hH₁ : IsTwoLocal H₁) (hN₁H₁ : N₁ ≤ H₁)
    (hSN₁ : pCoreOf 2 H₁ ≤ N₁) (hTN : T ≤ N₁) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ (T.subgroupOf N₁).index) : pCoreOf 2 H₁ ≤ T ∧ T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTS : T ≤ Subgroup.normalizer (pCoreOf 2 H₁ : Set G) :=
    (hTN.trans hN₁H₁).trans (localGroup_le_normalizer_pCoreOf 2 H₁)
  have hST2 : IsPGroup 2 (pCoreOf 2 H₁ ⊔ T : Subgroup G) := IsPGroup.to_sup_of_normal_left'
    (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H₁) hT2 hTS
  have hST : pCoreOf 2 H₁ ≤ T := le_sup_left.trans
    (le_of_le_of_isPGroup_of_not_dvd_index le_sup_right (sup_le hSN₁ hTN) hST2 hTidx)
  exact ⟨hST, fun hbot => twoLocal_pCoreOf_ne_bot H₁ hH₁ (le_bot_iff.mp (hbot ▸ hST))⟩

omit [Finite G] in
theorem le_normalizer_sylowTwo_of_commutator_le {N₁ J T : Subgroup G} (hTN : T ≤ N₁)
    (hNJ : ⁅N₁, J⁆ ≤ T) : J ≤ Subgroup.normalizer (T : Set G) := by
  refine le_normalizer_of_forall_mul_mul_inv_mem fun j hj t ht => ?_
  have hc := hNJ (Subgroup.commutator_mem_commutator (N₁.inv_mem (hTN ht)) hj)
  rw [commutatorElement_def, inv_inv] at hc
  have e : j * t * j⁻¹ = t * (t⁻¹ * j * t * j⁻¹) := by group
  rw [e]
  exact T.mul_mem ht hc

theorem D1CompCore.false_of_kMax_self (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock)
    (hd : D1CompCore p P M H R Rbar K) (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hWK : d1MapPCore p M H ≤ K)
    (hCW : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    {T R₁ : Subgroup G} (hTN : T ≤ d1PlusCore p H K) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ (T.subgroupOf (d1PlusCore p H K)).index)
    (hR₁T : R₁ ≤ Subgroup.normalizer (T : Set G))
    (hmax : ∀ H₂ : Subgroup G, GLBIsMaxTwoLocal H₂ → nclIn H (d1LiftX p H R K) ≤ H₂ →
      pCoreOf 2 M ≤ H₂ → R₁ ≤ H₂ →
      Nat.card (nclIn H₂ (d1LiftX p H R K)) ≤ Nat.card (nclIn H (d1LiftX p H R K))) :
    False := by
  have hp := hd.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set X := d1LiftX p H R K with hXdef
  set N := d1PlusCore p H K with hNdef
  obtain ⟨hNHM, hHN, hON⟩ := hd.d1PlusCore_facts
  have hNH : N ≤ H := hNHM.trans inf_le_left
  have hXH : X ≤ H := d1LiftX_le_H p H R K
  have hXR : X ≤ R := d1LiftX_le p H R K
  have hXp : IsPGroup p X := hd.esc.isPGroup.to_le hXR
  obtain ⟨hND, hNJ⟩ := hd.d1PlusCore_le_and_commutator h3 h84 hD2 hY hWK
  have hp2 : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hd.red.ne_two
  obtain ⟨hST, hT1⟩ := twoCore_le_of_sylowTwo h3.maxTwoLocal_H.1 hNH
    ((pCoreOf_le_glbPrimeCore Nat.prime_two hp2 H).trans hON) hTN hT2 hTidx
  have hJT : nclIn H X ≤ Subgroup.normalizer (T : Set G) :=
    le_normalizer_sylowTwo_of_commutator_le hTN (hNJ.trans hST)
  have hQT : pCoreOf 2 M ≤ Subgroup.normalizer (T : Set G) :=
    ((h3.twoCore_M_le h3.twoCore_inf).trans hST).trans Subgroup.le_normalizer
  have hloc : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H := fun C hCT hC hchar =>
    normalizer_le_of_forall_maxTwoLocal_eq hT2 hJT (sup_le hR₁T hQT)
      (fun H₂ hH₂ hJH₂ hRQ => eq_of_maxTwoLocal_of_kMax h3 hXR hd.d1LiftX_ne_bot hXH le_rfl
        hd.nclIn_nclIn hmax H₂ hH₂ hJH₂ hRQ) hCT hC hchar
  have hDH : pCoreCentralizerPreimage p M ⊓ H ≤ X ⊔ N := by
    have hKn : K.Normal := hd.red.normal_of_rankOne hd.comp hd.noncyclic
    rintro d ⟨hdD, hdH⟩
    have hc := hCW (mk_mem_centralizer_d1MapPCore h3.twoCore_M_le_glbPrimeCore hdD hdH)
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hc
    obtain ⟨t, htT, c, hcC, htc⟩ := hc
    rw [← hd.map_d1LiftX_eq_inf] at htT
    obtain ⟨x, hx, rfl⟩ := htT
    have hn : (x : G)⁻¹ * d ∈ N := by
      refine ⟨x⁻¹ * ⟨d, hdH⟩, ?_, rfl⟩
      show QuotientGroup.mk' (primeComplementCore (G := H) p) (x⁻¹ * ⟨d, hdH⟩) ∈
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
      rw [map_mul, map_inv, ← htc, inv_mul_cancel_left]
      exact hcC
    have e : d = x * ((x : G)⁻¹ * d) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hx) hn
  obtain ⟨hDM, hMD, hQD, -⟩ := pCoreCentralizerPreimage_facts p M
  exact h3.false_of_normal_inf_le_sup_of hXp hXH hNH (hXH.trans hHN) hTN hT2 hTidx hT1 hloc
    hDM hMD hQD hND hDH hCGT hD2

theorem D1OneLieData.false_of_kMax_self (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    {T R₁ : Subgroup G} (hTN : T ≤ d1PlusCore p H K) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ (T.subgroupOf (d1PlusCore p H K)).index)
    (hR₁T : R₁ ≤ Subgroup.normalizer (T : Set G))
    (hmax : ∀ H₂ : Subgroup G, GLBIsMaxTwoLocal H₂ → nclIn H (d1LiftX p H R K) ≤ H₂ →
      pCoreOf 2 M ≤ H₂ → R₁ ≤ H₂ →
      Nat.card (nclIn H₂ (d1LiftX p H R K)) ≤ Nat.card (nclIn H (d1LiftX p H R K))) :
    False :=
  hd.toCore.false_of_kMax_self (hd.toPhaseThree hK) h84 hD2 hCGT hY hWK
    (hd.centralizer_d1MapPCore_le hK h84 hD2 hY hU3) hTN hT2 hTidx hR₁T hmax

theorem D1OneLieData.false_of_kMax_ne (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (hSch : KFactCatalogSchreier) (hCC : D1OneLieCompetitorComp) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hJ : D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)))
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    {R₁ : Subgroup G} (hR₁R : R₁ ≤ R) (hXR₁ : d1LiftX p H R K ≤ R₁)
    (hcard : Nat.card R = p * Nat.card R₁) (hR₁N : R₁ ⊓ d1PlusCore p H K = ⊥)
    {H₁ : Subgroup G} (hH₁ : GLBIsMaxTwoLocal H₁) (hne : H₁ ≠ H)
    (hJH₁ : nclIn H (d1LiftX p H R K) ≤ H₁) (hR₁H₁ : R₁ ≤ H₁)
    (hmax : ∀ H₂ : Subgroup G, GLBIsMaxTwoLocal H₂ → nclIn H (d1LiftX p H R K) ≤ H₂ →
      pCoreOf 2 M ≤ H₂ → R₁ ≤ H₂ →
      Nat.card (nclIn H₂ (d1LiftX p H R K)) ≤ Nat.card (nclIn H₁ (d1LiftX p H R K))) :
    False := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := d1LiftX p H R K with hXdef
  obtain ⟨P', S, -, h₁, hR₁S, hScard, hSrk⟩ :=
    hd.exists_sylow_of_memK hT hJ hR₁R hXR₁ hcard hH₁ hne hJH₁ hR₁H₁
  have hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S :=
    ⟨hd, hR₁R, hXR₁, hR₁N, h₁, hJH₁, hR₁S, hScard, hSrk⟩
  have hJc := hCC G p P M H R Rbar K R₁ P' H₁ S hc hY hWK
  have h3₁ := hc.toPhaseThree hSch hJc hK
  obtain ⟨hJJ₁, hJ₁eq⟩ := hc.nclIn_le_and_nclIn_eq hSch hJc
  have hXH₁ : X ≤ H₁ := (le_nclIn (d1LiftX_le_H p H R K)).trans hJH₁
  have hXp : IsPGroup p X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  have hR₁p : IsPGroup p R₁ := hd.cfg.ext.isPGroup.to_le hR₁R
  have hR₁N₁ : R₁ ≤ Subgroup.normalizer (GLBPrimeCore p H₁ : Set G) :=
    hR₁H₁.trans (le_normalizer_glbPrimeCore p H₁)
  obtain ⟨T, hTN, hT2, hTidx, hR₁T⟩ :=
    exists_le_normalizer_of_coprime (q := 2) hR₁p hR₁N₁ (glbPrimeCore_coprime p H₁)
  have hp2 : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hd.cfg.red.ne_two
  obtain ⟨hST, hT1⟩ := twoCore_le_of_sylowTwo hH₁.1 (glbPrimeCore_le p H₁)
    (pCoreOf_le_glbPrimeCore Nat.prime_two hp2 H₁) hTN hT2 hTidx
  have hJT : nclIn H₁ X ≤ Subgroup.normalizer (T : Set G) :=
    le_normalizer_sylowTwo_of_commutator_le hTN
      ((hc.commutator_nclIn_le_twoCore hSch hJc hK h84 hD2 hY).trans hST)
  have hQT : pCoreOf 2 M ≤ Subgroup.normalizer (T : Set G) :=
    ((h3₁.twoCore_M_le h3₁.twoCore_inf).trans hST).trans Subgroup.le_normalizer
  have hloc : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H₁ := fun C hCT hC hchar =>
    normalizer_le_of_forall_maxTwoLocal_eq hT2 hJT (sup_le hR₁T hQT)
      (fun H₂ hH₂ hJH₂ hRQ => eq_of_maxTwoLocal_of_kMax h3₁ (hXR₁.trans hR₁S)
        hd.d1LiftX_ne_bot hXH₁ hJJ₁ hJ₁eq hmax H₂ hH₂ hJH₂ hRQ) hCT hC hchar
  obtain ⟨hDM, hMD, hQD, -⟩ := pCoreCentralizerPreimage_facts p M
  exact h3₁.false_of_normal_inf_le_sup_of hXp hXH₁ (glbPrimeCore_le p H₁)
    (hXH₁.trans (le_normalizer_glbPrimeCore p H₁)) hTN hT2 hTidx hT1 hloc hDM hMD hQD
    (h3₁.glbPrimeCore_le_pCoreCentralizerPreimage h84 hD2)
    (hc.pCoreCentralizer_inf_le hSch hJc hK h84 hD2 hY hWK hU3) hCGT hD2

theorem D1OneLieData.false_of_zz_dichotomy (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (hSch : KFactCatalogSchreier) (hCC : D1OneLieCompetitorComp) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hJ : D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)))
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
    (hc : Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) = p) : False := by
  obtain ⟨T, hTN, hT2, hTidx, -, hXR₁, hcard, hR₁N⟩ :=
    hd.exists_indexP hK h84 hD2 hY hWK hno hc
  have h3 := hd.toPhaseThree hK
  obtain ⟨H₁, ⟨hH₁, hJH₁, -, hR₁H₁⟩, hmax⟩ := Set.exists_max_image
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
  · exact hd.false_of_kMax_ne hK hT hSch hCC h84 hD2 hCGT hJ hY hWK hU3 inf_le_left hXR₁ hcard
      hR₁N hH₁ hH₁H hJH₁ hR₁H₁ fun H₂ h1 h2 h3 h4 => hmax H₂ ⟨h1, h2, h3, h4⟩

end CFSG.AGLEmbedding
