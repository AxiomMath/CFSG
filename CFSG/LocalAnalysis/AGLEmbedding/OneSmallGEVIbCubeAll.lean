module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCube
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAll

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1SmallGEVIbNormalAllRest2 : Prop :=
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
    (p = 3 ∨ IsAltTwoP p K ∨ (p = 5 ∧ IsFi22 K)) → False

theorem d1SmallGEVIbNormalAllRest_of_rest2 (hUP : KFactUPrimeSmall)
    (hSch : KFactCatalogSchreier) (hK8 : KFactSmallBorelSolvable)
    (hΓs : KFactSmallGammaSolvableSpor) (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hShape : KFactSmallSylowShape) (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hI : D1IbCubeInputs) (hRest2 : D1SmallGEVIbNormalAllRest2) :
    D1SmallGEVIbNormalAllRest := by
  intro G _ _ p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hgp hcomm hnot hH hVH hsm hall hcase
  by_cases h2 : p = 3 ∨ IsAltTwoP p K ∨ (p = 5 ∧ IsFi22 K)
  · exact hRest2 G p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hgp hcomm hnot hH hVH hsm
      hall h2
  push Not at h2
  obtain ⟨hp3, hA, hFi⟩ := h2
  have hT2 : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) ≠ p ^ 2 := by
    rcases hcase with h | h | h | h
    · exact absurd h hp3
    · exact h
    · exact absurd h hA
    · exact absurd h.2 (hFi h.1)
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 5 with h | h
    · interval_cases p
      · exact absurd rfl hp2
      · exact absurd rfl hp3
      · exact absurd hp (by decide)
    · exact h
  obtain ⟨T₁, hT₁, hs, hnab, hcat, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  have hT₁card : Nat.card T₁ = Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      K : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  have hT3 : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ 3 := by
    rcases hShape K hs hnab hcat p hp hp2 T₁ hT₁nc hΓ hd.small with h | ⟨h, -⟩
    · exact absurd (hT₁card ▸ h) hT2
    · exact hT₁card ▸ h
  exact D1OneSmallData.false_of_ibNormal_cube hUP hSch hK8 hΓs hOut hExp hShape hInn hKP hC3p hK5p
    hI hd hz hnIa hB0 (fun h => hp3 h.1) hVH hp5 hT3 hA (fun h => hFi h.1 h.2)

theorem d1SmallGEVIbNormalAll_of_rest2 (hUP : KFactUPrimeSmall) (hSch2 : KFactCatalogSchreier)
    (hK8s : KFactSmallBorelSolvable) (hΓs : KFactSmallGammaSolvableSpor)
    (hSO : KFactSmallOutPPrime) (hSE : KFactSmallSylowExp) (hShp : KFactSmallSylowShape)
    (hOrb : KFactSmallOrbits) (hInn : KFactBlockAutPrimeInner) (hKPp : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hOPA : KFactBlockOutPrime) (hORb : KFactBlockOutRankIb) (hTAb : KFactBlockToralIb)
    (hC3Tq : CitedBlockThreeToralIbSq) (hPlb : KFactBlockPlaneIb)
    (hOrb3 : KFactSmallOrbitsCube) (hIbR2 : D1SmallGEVIbNormalAllRest2) :
    D1SmallGEVIbNormalAll :=
  have hB : D1IbBlockInputs :=
    ⟨h84, h85, h86, h93, hD2, hK2, hC3, hK5, hOPA, hSch2, hORb, hTAb,
      citedBlockThreeToralIb_of_sq hC3Tq⟩
  d1SmallGEVIbNormalAll_of_rest hUP hSch2 hK8s hΓs hSO hSE hOrb hInn hKPp hC3p hK5p hB
    (d1SmallGEVIbNormalAllRest_of_rest2 hUP hSch2 hK8s hΓs hSO hSE hShp hInn hKPp hC3p hK5p
      ⟨hB, hPlb, hC3Tq, hOrb3⟩ hIbR2)

end CFSG.AGLEmbedding
