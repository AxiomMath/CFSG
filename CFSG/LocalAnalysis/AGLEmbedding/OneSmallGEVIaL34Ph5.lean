module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34MSide

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.asc81bHyp_M_twoCore_inf (hUE : KFactUPrimeExc) (hO : KFactSmallThreeOrders)
    (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) (hI : D1SmallIa p H K) (hp3 : p = 3)
    (hL : IsLinThreeFour K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hY : ∀ Y : Subgroup G, Y ≤ pCoreOf 2 (H ⊓ M) → Y ≠ ⊥ →
      (Y.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic →
      M ⊓ Subgroup.normalizer (Y : Set G) ≤ H) :
    Asc81bHyp M (pCoreOf 2 (H ⊓ M)) := by
  obtain ⟨-, hNM, hO2, -⟩ := hd.normalizer_twoCore_inf_eq hUE hO hNO h93 hD2 hI hp3 hL hS
  have hU1 : pCoreOf 2 (H ⊓ M) ≠ ⊥ := (hd.isTwoRadicalIn_twoCore_inf hUE hp3 hL hS).2.1
  refine ⟨⟨(RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)).trans inf_le_right, hU1,
    hO2.symm⟩,
    (hd.cfg.ext.charTwo_of_isCharTwoType hd.cfg.glob.charTwo).1, ?_⟩
  refine le_antisymm ?_ (inf_normalizer_le_cgsIn hU1)
  refine iSup_le fun C => iSup_le fun hCU => iSup_le fun hC1 => iSup_le fun hchar => ?_
  rw [hNM]
  exact le_inf (hY C hCU hC1 hchar) inf_le_left

@[expose] def D1SmallGEVNormalL34Ph5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    p = 3 → IsLinThreeFour K → ¬ D1SmallOuterR p H Rbar K → D1SmallU2Fails p M H K →
    GLBPrimeCore p (H ⊓ M) ≠ GLBPrimeCore p H → pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    Subgroup.centralizer ({z} : Set G) ≤ H →
    GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ GLBPrimeCore p H →
    (∀ hzH : z ∈ H,
      (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩)).Normal) →
    (∀ H₁ : Subgroup G, GLBIsMaxTwoLocal H₁ → H ⊓ M ≤ H₁ → H₁ = H ∨ H₁ = M) →
    (∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧ H ≤ Subgroup.normalizer (C : Set G)) →
    (∃ Y : Subgroup G, Y ≤ pCoreOf 2 (H ⊓ M) ∧ Y ≠ ⊥ ∧
      (Y.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧
      ¬ M ⊓ Subgroup.normalizer (Y : Set G) ≤ H) →
    False

theorem d1SmallGEVNormalL34Ph4_of_ph5 (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (hK : CitedBlockToralThree)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hPh5 : D1SmallGEVNormalL34Ph5) :
    D1SmallGEVNormalL34Ph4 := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hS hcomm hnot hV hCz
    hcore hA hM hX
  by_cases hY : ∃ Y : Subgroup G, Y ≤ pCoreOf 2 (H ⊓ M) ∧ Y ≠ ⊥ ∧
      (Y.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧
      ¬ M ⊓ Subgroup.normalizer (Y : Set G) ≤ H
  · exact hPh5 G p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hS hcomm hnot hV
      hCz hcore hA hM hX hY
  · refine hd.false_of_l34_ia_of_asc81bHyp hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hNO hK h84 h85
      h86 h93 hD2 hz hI hB0 hp3 hL hOR hS hCz
      (hd.asc81bHyp_M_twoCore_inf hUE hO hNO h93 hD2 hI hp3 hL hS fun Y hYU hY1 hchar => ?_)
    by_contra hn
    exact hY ⟨Y, hYU, hY1, hchar, hn⟩

end CFSG.AGLEmbedding
