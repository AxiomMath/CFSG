module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Third
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PU

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Block

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.map_barM_eq_of_weakBlock (hd : D1OneSmallData 3 P M H R Rbar K)
    {L : Subgroup G} (hLw : IsWeakSBlock H (pCoreOf 2 (H ⊓ M)) L)
    (hLW : ¬ barM H L ≤
      (primeComplementCore (G := H) 3).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :
    (barM H L).map (twoPrimeMap H Nat.prime_three (by norm_num)) = K := by
  set φ := twoPrimeMap H Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2) with hφ
  have hLc : IsComponentOf (barM H L) ⊤ := hLw.component
  have hker : ¬ barM H L ≤ φ.ker := fun h =>
    hLW fun x hx => mem_map_of_twoPrimeMap_eq_one Nat.prime_three (by norm_num) (h hx)
  have hK' : IsComponentOf ((barM H L).map φ) ⊤ :=
    isComponentOf_map_top_of_surj φ (twoPrimeMap_surjective Nat.prime_three (by norm_num)) hLc
      hker
  by_contra hne
  have hKC : (barM H L).map φ ≤
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (ComponentClassification.LocalComponents.commute_of_ne _ _ hK' hd.comp hne)
  obtain ⟨zb, hzbR, hzbK, hzbp, hzbc⟩ := hd.z
  have hCX := hd.cfg.red.centralizer_le_of_rankOne hd.noncyclic hzbR hzbK hzbp hzbc
  have hLHM : L ≤ H ⊓ M := by
    intro l hl
    have hlH : l ∈ H := hLw.le hl
    have hmem : φ (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨l, hlH⟩) ∈ d1X0 3 M H :=
      hCX (hKC ⟨_, ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, rfl⟩)
    rw [hφ, twoPrimeMap_mk] at hmem
    obtain ⟨m, hm, hmx⟩ := hmem
    have hm' : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
    have h1 : QuotientGroup.mk' (primeComplementCore (G := H) 3) (m⁻¹ * ⟨l, hlH⟩) = 1 := by
      rw [map_mul, map_inv, hmx, inv_mul_cancel]
    have hcore := hd.cfg.ext.primeCore_le ((mk'_primeComplementCore_eq_one_iff 3 _).mp h1)
    have e : l = (m : G) * ((m⁻¹ * ⟨l, hlH⟩ : H) : G) := by simp
    exact ⟨hlH, e ▸ M.mul_mem hm' hcore⟩
  exact hLw.not_le_normalizer
    (hLHM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)))

theorem D1OneSmallData.l34BlockFacts_ib (hUE : KFactUPrimeExc) (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData 3 P M H R Rbar K) (hL : IsLinThreeFour K)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) {L : Subgroup G}
    (hLw : IsWeakSBlock H (pCoreOf 2 (H ⊓ M)) L)
    (hLW : ¬ barM H L ≤
      (primeComplementCore (G := H) 3).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :
    L34BlockFacts M H L K (twoPrimeMap H Nat.prime_three (by norm_num)) :=
  l34BlockFacts_of_map_eq (hd.map_barM_eq_of_weakBlock hLw hLW) hd.center ((hO K).2.1 hL)
    (hd.inf_normalizer_twoCore_inf hUE rfl hL hS) hLw hLW


end Block

section Rest

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_l34_pu_ib (hUE : KFactUPrimeExc) (hO : KFactSmallThreeOrders)
    (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3)
    (hL : IsLinThreeFour K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hPU : ∀ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) → C ≠ ⊥ →
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic → ¬ H ≤ Subgroup.normalizer (C : Set G)) :
    False := by
  subst hp3
  obtain ⟨L, hLw, hLW⟩ := hd.exists_weakBlock_twoCore_inf hO hL hS
  have hB := hd.l34BlockFacts_ib hUE hO hL hS hLw hLW
  have h72 : ∀ Y : Subgroup (H ⧸ primeComplementCore (G := H) 3), Y ≤ d1X0 3 M H ⊓ K →
      Nat.card Y ∣ 72 := fun Y hY =>
    hd.card_dvd_seventytwo hUE hL (hY.trans inf_le_left) (hY.trans inf_le_right)
  have hyp := hd.asc81bHyp_twoCore_inf hUE rfl hL hS hPU
  have hK := (hd.cfg.ext.isKGroup_of_isKProper hd.cfg.glob.kProper).2
  exact false_of_l34BlockFacts hNO h93 hL hK hyp hLw
    (hD2 G hd.cfg.glob.toAGLGlobal H L hd.cfg.ext.maxTwoLocal_H hLw.le hLw.subnormal) hB h72

@[expose] def D1SmallGEVIbNormalAllRest8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    ¬ D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    ¬ D1SmallOuterR p H Rbar K →
    ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    GLBIsMaxTwoLocal H →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    D1GEVStarSmall p P M R z K →
    (∀ Hs : Subgroup G, GLBIsMaxTwoLocal Hs →
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs →
      ∀ hzHs : z ∈ Hs, ¬ (Subgroup.zpowers
        (QuotientGroup.mk' (primeComplementCore (G := Hs) p) ⟨z, hzHs⟩)).Normal) →
    p = 3 → IsLinThreeFour K → D1SmallU2Fails p M H K →
    GLBPrimeCore p (H ⊓ M) ≠ GLBPrimeCore p H → pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H →
    (∀ H₁ : Subgroup G, GLBIsMaxTwoLocal H₁ → H ⊓ M ≤ H₁ → H₁ = H ∨ H₁ = M) →
    (∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧ H ≤ Subgroup.normalizer (C : Set G)) →
    False

theorem d1SmallGEVIbNormalAllRest7_of_rest8 (hUE : KFactUPrimeExc) (hO : KFactSmallThreeOrders)
    (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (h8 : D1SmallGEVIbNormalAllRest8) : D1SmallGEVIbNormalAllRest7 := by
  intro G _ _ p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
    hp3 hL hU2 hcore hS hA
  by_cases hX : ∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧ H ≤ Subgroup.normalizer (C : Set G)
  · exact h8 G p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
      hp3 hL hU2 hcore hS hA hX
  · exact hd.false_of_l34_pu_ib hUE hO hNO h93 hD2 hp3 hL hS fun C hCU hC1 hchar hHC =>
      hX ⟨C, hCU, hC1, hchar, hHC⟩

theorem d1SmallGEVIbNormalAllRest6_of_rest8 (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (h8 : D1SmallGEVIbNormalAllRest8) : D1SmallGEVIbNormalAllRest6 :=
  d1SmallGEVIbNormalAllRest6_of_rest7 hβ hα h2 h3 hUE hSch hΓ3 hOut hExp hOrb hSh3 hO
    (d1SmallGEVIbNormalAllRest7_of_rest8 hUE hO hNO h93 hD2 h8)

end Rest

end CFSG.AGLEmbedding
