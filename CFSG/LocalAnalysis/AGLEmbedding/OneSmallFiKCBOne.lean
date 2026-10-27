module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPCz
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOne

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_b1_of_reduced (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hnSP : ¬ D1CzSP p z) (hnB0 : ¬ D1CzB0 p R z) {m : G}
    {T : Sylow p (Subgroup.centralizer ({z} : Set G))}
    (hRT : R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype)
    (hTP : (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
      (P : Subgroup G).map (MulAut.conj m).toMonoidHom)
    {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hc : D1CzReduced p M z T Pbar KC) (hZKC : Subgroup.center KC = ⊥)
    (hzK : d1CzElt p z ∉ KC)
    (hB : ∀ x : D1CzQuot p z, (∃ n : ℕ, x ^ p ^ n = 1) →
      x ∈ KC ⊔ Subgroup.centralizer (KC : Set (D1CzQuot p z)))
    (hexp : ∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC, t ^ p = 1)
    (hcardKC : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) =
      Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _)) :
    False :=
  hd.false_of_b1_of_comp hz hnSP hnB0 hRT hTP hc.sylow_eq hc.red hc.center hc.order hc.comp hc.normal
    hZKC hzK hB hexp hcardKC

end Config

end CFSG.AGLEmbedding
