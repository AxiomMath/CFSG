module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Perf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarRes
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34Third

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_l34_third_nine (hβ : KFactBeta) (hα : KFactAlphaW)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {H₁ : Subgroup G} (hH₁ : GLBIsMaxTwoLocal H₁) (hHM : H ⊓ M ≤ H₁) (hne : H₁ ≠ H)
    (hneM : H₁ ≠ M) : False := by
  have hH₁M : ¬ H₁ ≤ M := fun h => hneM (hH₁.2 M hd.cfg.ext.maxTwoLocal_M.1 h).symm
  have hinf := hd.inf_le_of_l34 hUE hp3 hL hH₁ hHM hne
  obtain ⟨hR, -⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut (fun _ _ => hOR))
  refine hd.false_of_l34_escape_nine hβ hα h2 h3 hOut hExp hOrb hSh3 hO hz hB0 hp3 hL hOR hH₁
    hH₁M ((le_inf hd.cfg.ext.le_H hd.cfg.ext.le_M).trans hHM)
    (fun n hnN hnC => hHM ⟨hCz hnC, hd.cfg.ext.normalizer_le hnN⟩) fun U hU hUp => ?_
  have hUH : U ≤ H := hU.trans (inf_le_right.trans hCz)
  have hUM : U ≤ M := (le_inf hUH (hU.trans inf_le_left)).trans hinf
  exact hd.not_nine_dvd_card_of_perfect hUE hSch hΓ3 hp3 hL hR (le_inf hUH hUM) hUp

@[expose] def D1SmallGEVIbNormalAllRest7 : Prop :=
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
    (∀ H₁ : Subgroup G, GLBIsMaxTwoLocal H₁ → H ⊓ M ≤ H₁ → H₁ = H ∨ H₁ = M) → False

theorem d1SmallGEVIbNormalAllRest6_of_rest7 (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (h7 : D1SmallGEVIbNormalAllRest7) :
    D1SmallGEVIbNormalAllRest6 := by
  intro G _ _ p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
    hp3 hL hU2 hcore hS
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := centralizer_le_of_normalizer_vz_le hV
  refine h7 G p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hAlt hcomm hnot hHmax hV hstar hns
    hp3 hL hU2 hcore hS fun H₁ hH₁ hHM => ?_
  by_contra hcon
  push Not at hcon
  exact hd.false_of_l34_third_nine hβ hα h2 h3 hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hz hB0 hp3 hL
    hOR hCz hH₁ hHM hcon.1 hcon.2

end CFSG.AGLEmbedding
