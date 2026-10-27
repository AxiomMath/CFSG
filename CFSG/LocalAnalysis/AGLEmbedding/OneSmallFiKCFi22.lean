module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCEven
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCCz
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCAb

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.twoCore_comm_fi22 (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hFN : KFactFi22NoTwo) (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) (hIso : D1CzIso p z K)
    (hFi : p = 5 ∧ IsFi22 K) :
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) ∧
    (¬ D1CzEven p z →
      pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G)) := by
  have h3 : p ≠ 3 := by rw [hFi.1]; decide
  obtain ⟨hcardR, -⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 fun h => absurd h h3
  obtain ⟨-, T, Pbar, KC, -, hRT, -, hc⟩ := hd.exists_czReduced hz
  have hNoTwo : ∀ (S : Sylow p K) (W : Subgroup K), IsPGroup 2 W →
      (S : Subgroup K) ≤ Subgroup.normalizer (W : Set K) → W = ⊥ := by
    obtain ⟨rfl, hK⟩ := hFi
    exact hFN K hK
  obtain ⟨hZKC, hcardKC, hNoTwoKC⟩ := hd.czComponent_facts_of_iso hNoTwo hc hIso
  exact ⟨hd.twoCore_comm_mem_core_of_reduced hz hB0 hRT hc hZKC hcardKC hNoTwoKC hcardR,
    fun hodd => hd.twoCore_inf_centralizer_le_of_reduced hz hB0 hodd hRT hc hZKC hcardKC
      hNoTwoKC hcardR⟩

end Config

@[expose] def D1SmallFi22EV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    p = 5 → IsFi22 K → 3 ∉ GLBBetaFour G → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    False

theorem d1SmallFi22_of (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hShape : KFactSmallSylowShape) (hFN : KFactFi22NoTwo) (hFO : KFactFi22Orbits)
    (hEV : D1SmallFi22EV) : D1SmallFi22 := by
  intro G _ _ p P M H R Rbar K hd huniq z hz h5 hK h3 hB0 hIso
  obtain ⟨hcomm, hodd⟩ := hd.twoCore_comm_fi22 hOut hExp hFN hz hB0 hIso ⟨h5, hK⟩
  have hnot := hd.false_of_twoCore_le_fi22 hOut hExp hShape hFO hz hB0 ⟨h5, hK⟩
  by_cases hE : D1CzEven p z
  · exact hEV G p P M H R Rbar K hd huniq z hz h5 hK h3 hB0 hE hIso hcomm hnot
  · exact hnot (hodd hE)

end CFSG.AGLEmbedding
