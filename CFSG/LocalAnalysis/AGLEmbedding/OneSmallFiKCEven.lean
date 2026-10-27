module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroNoTwo
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPCz

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.twoCore_comm_mem_core_of_reduced (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z)
    {T : Sylow p (Subgroup.centralizer ({z} : Set G))}
    (hRT : R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype)
    {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hc : D1CzReduced p M z T Pbar KC) (hZKC : Subgroup.center KC = ⊥)
    (hcardKC : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) =
      Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _))
    (hNoTwoKC : ∀ (S : Sylow p KC) (W : Subgroup KC), IsPGroup 2 W →
      (S : Subgroup KC) ≤ Subgroup.normalizer (W : Set KC) → W = ⊥)
    (hcard : Nat.card R ≤
      p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _)) :
    ∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) :=
  hd.twoCore_comm_mem_core_of_comp hz hB0 hRT hc.sylow_eq hc.normal hc.center hc.order hZKC hcardKC
    hNoTwoKC hcard

theorem D1OneSmallData.twoCore_inf_centralizer_le_of_reduced
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hodd : ¬ D1CzEven p z)
    {T : Sylow p (Subgroup.centralizer ({z} : Set G))}
    (hRT : R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype)
    {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hc : D1CzReduced p M z T Pbar KC) (hZKC : Subgroup.center KC = ⊥)
    (hcardKC : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) =
      Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _))
    (hNoTwoKC : ∀ (S : Sylow p KC) (W : Subgroup KC), IsPGroup 2 W →
      (S : Subgroup KC) ≤ Subgroup.normalizer (W : Set KC) → W = ⊥)
    (hcard : Nat.card R ≤
      p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _)) :
    pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) :=
  hd.twoCore_inf_centralizer_le_of_comm hodd
    (hd.twoCore_comm_mem_core_of_reduced hz hB0 hRT hc hZKC hcardKC hNoTwoKC hcard)

end Config

end CFSG.AGLEmbedding
