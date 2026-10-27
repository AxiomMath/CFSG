module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34MSide

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.asc81bHyp_M_twoCore_inf_ib (hUE : KFactUPrimeExc)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3)
    (hL : IsLinThreeFour K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hY : ∀ Y : Subgroup G, Y ≤ pCoreOf 2 (H ⊓ M) → Y ≠ ⊥ →
      (Y.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic →
      M ⊓ Subgroup.normalizer (Y : Set G) ≤ H) :
    Asc81bHyp M (pCoreOf 2 (H ⊓ M)) := by
  obtain ⟨-, hNM, hO2, -⟩ := hd.normalizer_twoCore_inf_eq_ib hUE hO hNO h93 hD2 hp3 hL hS
  have hU1 : pCoreOf 2 (H ⊓ M) ≠ ⊥ := (hd.isTwoRadicalIn_twoCore_inf hUE hp3 hL hS).2.1
  refine ⟨⟨(RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)).trans inf_le_right, hU1,
    hO2.symm⟩, (hd.cfg.ext.charTwo_of_isCharTwoType hd.cfg.glob.charTwo).1, ?_⟩
  refine le_antisymm ?_ (inf_normalizer_le_cgsIn hU1)
  refine iSup_le fun C => iSup_le fun hCU => iSup_le fun hC1 => iSup_le fun hchar => ?_
  rw [hNM]
  exact le_inf (hY C hCU hC1 hchar) inf_le_left

@[expose] def D1SmallGEVIbNormalAllRest9 : Prop :=
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
    (∃ Y : Subgroup G, Y ≤ pCoreOf 2 (H ⊓ M) ∧ Y ≠ ⊥ ∧
      (Y.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧
      ¬ M ⊓ Subgroup.normalizer (Y : Set G) ≤ H) →
    False

theorem d1SmallGEVIbNormalAllRest8_of_rest9 (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (hK : CitedBlockToralThreeIb)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (h9 : D1SmallGEVIbNormalAllRest9) :
    D1SmallGEVIbNormalAllRest8 := by
  intro G _ _ p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
    hp3 hL hU2 hcore hS hA hX
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := centralizer_le_of_normalizer_vz_le hV
  by_cases hY : ∃ Y : Subgroup G, Y ≤ pCoreOf 2 (H ⊓ M) ∧ Y ≠ ⊥ ∧
      (Y.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧
      ¬ M ⊓ Subgroup.normalizer (Y : Set G) ≤ H
  · exact h9 G p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
      hp3 hL hU2 hcore hS hA hX hY
  · refine hd.false_of_ib_three_l34_of_asc81bHyp hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hNO hK h84
      h85 h86 h93 hD2 hz hnIa hB0 hp3 hL hOR hS hCz
      (hd.asc81bHyp_M_twoCore_inf_ib hUE hO hNO h93 hD2 hp3 hL hS fun Y hYU hY1 hchar => ?_)
    by_contra hn
    exact hY ⟨Y, hYU, hY1, hchar, hn⟩

end CFSG.AGLEmbedding
