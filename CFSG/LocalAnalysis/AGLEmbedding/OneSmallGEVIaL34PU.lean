module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUNine
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34Third

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem false_of_l34BlockFacts (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hL : IsLinThreeFour K)
    (hKH : Open.IsKGroup ↥H) (hyp : Asc81bHyp H (pCoreOf 2 (H ⊓ M))) {L : Subgroup G}
    (hLw : IsWeakSBlock H (pCoreOf 2 (H ⊓ M)) L) (hX : ¬ NineThreeOne L)
    (hB : L34BlockFacts M H L K (twoPrimeMap H Nat.prime_three (by norm_num)))
    (h72 : ∀ Y : Subgroup (H ⧸ primeComplementCore (G := H) 3), Y ≤ d1X0 3 M H ⊓ K →
      Nat.card Y ∣ 72) : False := by
  rcases h93 G H (pCoreOf 2 (H ⊓ M)) L hKH hyp hLw with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact hX h1
  · exact hB.not_nineThreeTwo h72 h2
  · exact hB.not_nineThreeThree hNO hL h3
  · exact hB.not_nineThreeFour h4
  · exact hB.not_nineThreeFive h5
  · exact hB.not_nineThreeSix h6
  · exact hB.not_nineThreeSeven h7
  · exact hB.not_nineThreeEight h72 h8

theorem D1OneSmallData.false_of_l34_pu (hUE : KFactUPrimeExc) (hO : KFactSmallThreeOrders)
    (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) (hI : D1SmallIa p H K) (hp3 : p = 3)
    (hL : IsLinThreeFour K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hPU : ∀ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) → C ≠ ⊥ →
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic → ¬ H ≤ Subgroup.normalizer (C : Set G)) :
    False := by
  subst hp3
  obtain ⟨L, hLw, hLW⟩ := hd.exists_weakBlock_twoCore_inf hO hL hS
  have hB := hd.l34BlockFacts hUE hO hI hL hS hLw hLW
  have h72 : ∀ Y : Subgroup (H ⧸ primeComplementCore (G := H) 3), Y ≤ d1X0 3 M H ⊓ K →
      Nat.card Y ∣ 72 := fun Y hY =>
    hd.card_dvd_seventytwo hUE hL (hY.trans inf_le_left) (hY.trans inf_le_right)
  have hyp := hd.asc81bHyp_twoCore_inf hUE rfl hL hS hPU
  have hK := (hd.cfg.ext.isKGroup_of_isKProper hd.cfg.glob.kProper).2
  exact false_of_l34BlockFacts hNO h93 hL hK hyp hLw
    (hD2 G hd.cfg.glob.toAGLGlobal H L hd.cfg.ext.maxTwoLocal_H hLw.le hLw.subnormal) hB h72

@[expose] def D1SmallGEVNormalL34Ph4 : Prop :=
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
    False

theorem d1SmallGEVNormalL34Ph3_of_ph4 (hUE : KFactUPrimeExc) (hO : KFactSmallThreeOrders)
    (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hPh4 : D1SmallGEVNormalL34Ph4) : D1SmallGEVNormalL34Ph3 := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hS hcomm hnot hV hCz
    hcore hA hM
  by_cases hX : ∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧ H ≤ Subgroup.normalizer (C : Set G)
  · exact hPh4 G p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hS hcomm hnot hV
      hCz hcore hA hM hX
  · exact hd.false_of_l34_pu hUE hO hNO h93 hD2 hI hp3 hL hS fun C hCU hC1 hchar hHC =>
      hX ⟨C, hCU, hC1, hchar, hHC⟩

end CFSG.AGLEmbedding
