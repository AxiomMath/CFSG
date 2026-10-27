module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUpCtx
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFOTwo

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
theorem L34Ctx.pCore_two_autOn_eq_bot (hd : L34Ctx M H R Rbar K)
    (hL : IsLinThreeFour K) {D₀ V W Z : Subgroup G} (hD₀H : D₀ ≤ H) (hOD : GLBPrimeCore 3 H ≤ D₀)
    (hV : IsSylowTwoOf V D₀)
    (hXW : L34FF.threeComp H R K ⊔ V ≤ Subgroup.normalizer (W : Set G))
    (hVZ : V ≤ Subgroup.centralizer (Z : Set G))
    (hW : ∀ D : Subgroup G, L34FF.threeComp H R K ⊔ V ≤ Subgroup.normalizer (D : Set G) →
      D ≤ Subgroup.centralizer (Z : Set G) → D ≤ Subgroup.centralizer (W : Set G))
    (hZW : Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (Z : Set G))
    (hβ : L34FF.threeComp H R K ⊓ Subgroup.centralizer (W : Set G) ≤
      L34FF.threeCompCore H R K) :
    CFSG.pCore 2 (autOn (L34FF.threeComp H R K ⊔ V) W) = ⊥ := by
  exact L34FF.pCore_two_autOn_eq_bot hd.isPGroup hd.map_threeComp hd.threeComp_dichotomy
    hd.not_threeComp_le_threeCompCore hD₀H hV
    (fun {l v} _ _ hlv hC => hOD ((mk'_primeComplementCore_eq_one_iff 3 ⟨l * v, hlv⟩).mp (by
      rw [hd.centralizer_eq_bot, Subgroup.mem_bot] at hC
      exact hC)))
    hXW hVZ hW hZW hβ

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
