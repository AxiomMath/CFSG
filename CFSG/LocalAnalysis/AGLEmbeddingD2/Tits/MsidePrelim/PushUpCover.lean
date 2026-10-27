module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUpRep
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFAlpha
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBeta

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
theorem L34Ctx.cover_thompsonJ (hd : L34Ctx M H R Rbar K)
    {D₀ V : Subgroup G} (hD₀H : D₀ ≤ H) (hOD : GLBPrimeCore 3 H ≤ D₀) (hV : IsSylowTwoOf V D₀)
    (hα : ∀ A : Subgroup G, IsMaxElemAbelian V A → ∀ a ∈ A, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ ∈
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))) :
    ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (thompsonJ V : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k :=
  hd.toCore.cover_thompsonJ hD₀H hOD hV hα

theorem L34Ctx.cover_omegaOneCenterOf (hFF : CitedFFL34BestOffender)
    (hd : L34Ctx M H R Rbar K) (hL : IsLinThreeFour K) {V : Subgroup G}
    {D₀ : Subgroup G} (hD₀H : D₀ ≤ H) (hOD : GLBPrimeCore 3 H ≤ D₀)
    (hV : IsSylowTwoOf V D₀) {A : Subgroup G} (hA : IsMaxElemAbelian V A)
    {a : G} (haA : a ∈ A) (haC : ∀ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ ∉
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))) :
    ∀ k ∈ K, ∃ x ∈ H ⊓ Subgroup.normalizer (omegaOneCenterOf V : Set G), ∃ hx : x ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨x, hx⟩ = k :=
  hd.toCore.cover_omegaOneCenterOf hFF hL hd.ne_top hd.kProper hD₀H hV
    (hd.omegaOneCenterOf_le_twoCore hD₀H hOD hV) (hd.twoCore_le_of_isSylowTwoOf hD₀H hOD hV)
    (fun hXW hVZ hW hZW hβ => hd.pCore_two_autOn_eq_bot hL hD₀H hOD hV hXW hVZ hW hZW hβ) hA haA
    haC

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
