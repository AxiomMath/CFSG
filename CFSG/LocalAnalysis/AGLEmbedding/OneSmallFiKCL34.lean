module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPBOneL34
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPCz

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_b1_l34_of_reduced (hGen : KFactL34OuterGen) (hAE : KFactL34AutExp)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hnSP : ¬ D1CzSP p z) (hp3 : p = 3) (hOP : D1CzOuterP p z) {m : G}
    {T : Sylow p (Subgroup.centralizer ({z} : Set G))}
    (hRT : R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype)
    (hTP : (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
      (P : Subgroup G).map (MulAut.conj m).toMonoidHom)
    {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hc : D1CzReduced p M z T Pbar KC) (hZKC : Subgroup.center KC = ⊥)
    (hzK : d1CzElt p z ∉ KC) (hLC : IsLinThreeFour KC)
    (hexp : ∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC, t ^ p = 1)
    (hcardKC : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) =
      Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _)) :
    False :=
  hd.false_of_b1_l34_of_comp hGen hAE hz hnSP hp3 hOP hRT hTP hc.sylow_eq hc.red hc.center hc.order
    hc.comp hc.normal hc.unique hZKC hzK hLC hexp hcardKC

end Config

end CFSG.AGLEmbedding
