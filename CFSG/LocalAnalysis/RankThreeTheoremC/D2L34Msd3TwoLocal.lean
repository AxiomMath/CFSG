module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Defs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.BetaInfSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.CharSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Escape9
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Base

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.Tits CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

section Conf

variable {G : Type} [Group G] [Finite G]

theorem betaConf3_isPSolvable_of_le_twoLocal [D2Amb3 G]
    (hSch : KFactCatalogSchreier)
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hAll : D2L34AllResidue3 P M) {N : Subgroup G} (hN : IsTwoLocal N) (hNM : ¬ N ≤ M)
    {X : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M) (hX : IsPGroup 3 X) (hXc : ¬ IsCyclic X)
    {Y : Subgroup G} (hY : Y ≤ N ⊓ M) : CFSG.HallHigman.IsPSolvable 3 ↥Y := by
  obtain ⟨N₁, E₀, hNN₁, -, hesc, hmax, -⟩ :=
    D2L34BetaConf3.exists_escape_of_not_isCyclic hc hstr hN hNM hXN hXM hX hXc
  obtain ⟨d₁, Rbar₁, K₁, hc₁⟩ := hAll E₀ N₁ E₀ hesc hmax
  have hY₁ : Y ≤ N₁ ⊓ M := le_inf ((hY.trans inf_le_left).trans hNN₁) (hY.trans inf_le_right)
  exact betaConf3_isPSolvable_of_le_inf hSch hc₁ hY₁

end Conf

@[expose] def D2L34BetaTwoLocalSylowCyclic3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M → D2L34Kmax H →
    ∀ T : Subgroup G, IsSylowTwoOf T M → ∀ N : Subgroup G, IsTwoLocal N → T ≤ N → ¬ N ≤ M →
      (∀ X : Subgroup G, X ≤ N ⊓ M → IsPGroup 3 X → IsCyclic X) →
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥(N ⊓ M) → IsSylowTwoOf T N

@[expose] def D2L34BetaTwoLocalSylow3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M → D2L34Kmax H →
    ∀ T : Subgroup G, IsSylowTwoOf T M → ∀ N : Subgroup G, IsTwoLocal N → T ≤ N →
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥(N ⊓ M) → IsSylowTwoOf T N

@[expose] def D2L34BetaNormalizerSolvable3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M → D2L34Kmax H →
    ∀ T : Subgroup G, IsSylowTwoOf T M → ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T →
      (C.subgroupOf T).Characteristic →
      CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.normalizer (C : Set G) ⊓ M)

variable {G : Type} [Group G] [Finite G]

theorem d2L34BetaTwoLocalSylow3_of_cyclic
    (hSch : KFactCatalogSchreier)
    (hcyc : D2L34BetaTwoLocalSylowCyclic3 G) : D2L34BetaTwoLocalSylow3 G := by
  intro d P M A H R Rbar K ctx hstr hKmax T hT N hN hTN hns
  have := ctx.amb
  have hc := ctx.conf
  have hAll := ctx.allResidue
  by_cases hNM : N ≤ M
  · refine ⟨hTN, hT.2.1, fun h => hT.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex T N M hTN hNM
    exact h.trans ⟨_, this.symm⟩
  by_cases hcy : ∀ X : Subgroup G, X ≤ N ⊓ M → IsPGroup 3 X → IsCyclic X
  · exact hcyc d P M A H R Rbar K ctx hstr hKmax T hT N hN hTN hNM hcy hns
  · exfalso
    obtain ⟨X, hX, hXp, hXc⟩ : ∃ X : Subgroup G, X ≤ N ⊓ M ∧ IsPGroup 3 X ∧ ¬ IsCyclic X := by
      by_contra h
      exact hcy fun X hX hXp => by
        by_contra hc
        exact h ⟨X, hX, hXp, hc⟩
    exact hns (betaConf3_isPSolvable_of_le_twoLocal hSch hc hstr hAll hN hNM
      (hX.trans inf_le_left) (hX.trans inf_le_right) hXp hXc le_rfl)

theorem d2L34BetaNormalizerSolvable3_of_twoLocalSylow
    (hFF : CitedFFL34BestOffender)
    (h1318 : D2L34BetaTwoLocalSylow3 G) : D2L34BetaNormalizerSolvable3 G := by
  intro d P M A H R Rbar K ctx hstr hKmax T hT C hC1 hCT hchar
  by_contra hns
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := ctx.amb
  have hc := ctx.conf
  have hAll := ctx.allResidue
  have hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := T) (C.subgroupOf T)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCT] at h1
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) := ⟨C, hC1, hT.2.1.to_le hCT, rfl⟩
  have hsyl := h1318 d P M A H R Rbar K ctx hstr hKmax T hT _ hloc
    (Subgroup.le_normalizer.trans hNT) hns
  obtain ⟨T₀, hT₀⟩ := exists_isSylowTwoOf (H ⊓ M)
  have hT₀M := (D2L34BetaConf3.isSylowTwoOf_of_cover hFF hc hstr hAll.onlyL34At hT₀).1
  obtain ⟨x, -, hxN, hxM, k, hk⟩ := D2L34BetaConf3.exists_two_element hc hT₀
  have hxT₀ : x ∉ T₀ := fun h => hxM ((hT₀.1.trans inf_le_right) h)
  have hlt : T₀ < Subgroup.zpowers x ⊔ T₀ :=
    lt_of_le_of_ne le_sup_right fun h => hxT₀ (h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hcard : Nat.card T < Nat.card (Subgroup.zpowers x ⊔ T₀ : Subgroup G) := by
    rw [card_eq_of_isSylowTwoOf hT hT₀M]
    exact Subgroup.card_lt_of_lt hlt
  exact not_isSylowTwoOf_of_card_lt hT.2.1 (isPGroup_zpowers_sup hT₀.2.1 hxN hk) hcard hNT hsyl

theorem d2L34BetaNormalizerSolvable3_of_cyclic
    (hSch : KFactCatalogSchreier) (hFF : CitedFFL34BestOffender)
    (hcyc : D2L34BetaTwoLocalSylowCyclic3 G) : D2L34BetaNormalizerSolvable3 G :=
  d2L34BetaNormalizerSolvable3_of_twoLocalSylow hFF (d2L34BetaTwoLocalSylow3_of_cyclic hSch hcyc)

end CFSG.LocalAnalysis.RankThreeTheoremC
