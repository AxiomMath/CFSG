module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34SqCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34Ph5
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Rest9

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1SmallGEVNormalL34Ph6 : Prop :=
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
    (∀ A : Subgroup G, A ≤ centerOf (pCoreOf 2 H) → A ≠ ⊥ →
      H ≤ Subgroup.normalizer (A : Set G) →
      M ≤ Subgroup.normalizer
        ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G) →
      ¬ IsSylowTwoOf (pCoreOf 2 (H ⊓ M)) (M ⊓ Subgroup.centralizer
          ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G)) ∧
        z ∉ Subgroup.centralizer
          ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G)) →
    False

theorem d1SmallGEVNormalL34Ph5_of_ph6 (hUE : KFactUPrimeExc) (hOrb : KFactSmallOrbits)
    (hExp : KFactSmallSylowExp) (hOut : KFactSmallOutPPrime) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hPh6 : D1SmallGEVNormalL34Ph6) : D1SmallGEVNormalL34Ph5 := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hS hcomm hnot hV hCz
    hcore hA hM hX hY
  refine hPh6 G p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hS hcomm hnot hV
    hCz hcore hA hM hX hY fun A hAS hA1 hHA hYM =>
      ⟨fun hsyl => ?_, fun hzC => ?_⟩
  · exact hd.false_of_fixed_normal_core hUE hOrb hExp hOut hSh3 hO hz hB0 hp3 hL hOR
      (hd.normalizer_twoCore_inf_eq_ib hUE hO hNO h93 hD2 hp3 hL hS).2.1 hAS hA1 hHA hYM
      (Or.inl hsyl)
  · exact hd.false_of_fixed_normal_core hUE hOrb hExp hOut hSh3 hO hz hB0 hp3 hL hOR
      (hd.normalizer_twoCore_inf_eq_ib hUE hO hNO h93 hD2 hp3 hL hS).2.1 hAS hA1 hHA hYM
      (Or.inr hzC)

@[expose] def D1SmallGEVIbNormalAllRest10 : Prop :=
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
    (∀ A : Subgroup G, A ≤ centerOf (pCoreOf 2 H) → A ≠ ⊥ →
      H ≤ Subgroup.normalizer (A : Set G) →
      M ≤ Subgroup.normalizer
        ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G) →
      ¬ IsSylowTwoOf (pCoreOf 2 (H ⊓ M)) (M ⊓ Subgroup.centralizer
          ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G)) ∧
        z ∉ Subgroup.centralizer
          ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G)) →
    False

theorem d1SmallGEVIbNormalAllRest9_of_rest10 (hUE : KFactUPrimeExc) (hOrb : KFactSmallOrbits)
    (hExp : KFactSmallSylowExp) (hOut : KFactSmallOutPPrime) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (h10 : D1SmallGEVIbNormalAllRest10) : D1SmallGEVIbNormalAllRest9 := by
  intro G _ _ p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
    hp3 hL hU2 hcore hS hA hX hY
  refine h10 G p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
    hp3 hL hU2 hcore hS hA hX hY fun A hAS hA1 hHA hYM =>
      ⟨fun hsyl => ?_, fun hzC => ?_⟩
  · exact hd.false_of_fixed_normal_core hUE hOrb hExp hOut hSh3 hO hz hB0 hp3 hL hOR
      (hd.normalizer_twoCore_inf_eq_ib hUE hO hNO h93 hD2 hp3 hL hS).2.1 hAS hA1 hHA hYM
      (Or.inl hsyl)
  · exact hd.false_of_fixed_normal_core hUE hOrb hExp hOut hSh3 hO hz hB0 hp3 hL hOR
      (hd.normalizer_twoCore_inf_eq_ib hUE hO hNO h93 hD2 hp3 hL hS).2.1 hAS hA1 hHA hYM
      (Or.inr hzC)

end CFSG.AGLEmbedding
