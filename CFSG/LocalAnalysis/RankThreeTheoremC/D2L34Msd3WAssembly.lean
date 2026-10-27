module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3SolvableStrong

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

@[expose] def FFCyclicInput3W (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → Nat.card R = 9 → Group.IsSolvable M →
    ∀ T : Subgroup G, IsSylowTwoOf T M → ¬ Subgroup.normalizer (T : Set G) ≤ M →
      ∀ S : Sylow 3 ↥(ffC M T),
        IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) →
        (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype ≠ ⊥ → Center3Conclusion M

theorem center3_of_solvable3W
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59) (hX : D1NoXBlock3 G)
    (hcyc : FFCyclicInput3W G) {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (hs : Group.IsSolvable M) : Center3Conclusion M := by
  have := ctx.amb
  have hc := ctx.conf
  have hOnly := ctx.allResidue.onlyL34At
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M :=
    CFSG.ABGLocalTools.isPConstrained_of_isSolvable hs
  obtain ⟨T, hTH⟩ := exists_isSylowTwoOf (H ⊓ M)
  have hTM : IsSylowTwoOf T M :=
    (D2L34BetaConf3.isSylowTwoOf_of_cover_of_nine hFF hc hR9 ctx.normRankTwo hOnly hTH).1
  have hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M :=
    D2L34BetaConf3.not_normalizer_le_of_isSylowTwoOf_of_nine hc hR9 ctx.normRankTwo hOnly hTH
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥(ffC M T)))
  by_cases hD0 : (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype = ⊥
  · have hS0 : (S : Subgroup ↥(ffC M T)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (x : G) ∈ (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype := ⟨x, hx, rfl⟩
      rw [hD0, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    have hC3 : ¬ 3 ∣ Nat.card ↥(ffC M T) := not_dvd_card_of_sylow_eq_bot S hS0
    exact center3_of_coprime_centralizer3W hI59 hX ctx hR9 hcon hTM hNT hC3
  · by_cases hDc : IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype)
    · exact hcyc d P M A H R Rbar K ctx hR9 hs T hTM hNT S hDc hD0
    · exact ffNoncyclicInput3W_of_nodes hI59 hX d P M A H R Rbar K ctx hR9 hcon T hTM hNT S hDc

theorem D2L34SideCtx3.stronglyEmbedded_of_nine
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59)
    (hX : D1NoXBlock3 G) (hcyc : FFCyclicInput3W G) {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (hs : Group.IsSolvable M) : GLBStronglyEmbedded 3 M := by
  obtain ⟨E, hEP, hE, hE9, hEc⟩ :=
    ctx.exists_center3_of_center3Conclusion (center3_of_solvable3W hFF hI59 hX hcyc ctx hR9 hs)
  exact ctx.stronglyEmbedded_of_center hEP hE hE9 hEc

@[expose] def D2L34BetaMSolvableR9 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → Group.IsSolvable M → Nat.card R = 9

theorem D2L34BetaMSolvableR9.toStrong3
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59)
    (hX : D1NoXBlock3 G) (hcyc : FFCyclicInput3W G) (h : D2L34BetaMSolvableR9 G) :
    D2L34BetaMSolvableStrong3 G :=
  fun d P M A H R Rbar K ctx hs =>
    ctx.stronglyEmbedded_of_nine hFF hI59 hX hcyc (h d P M A H R Rbar K ctx hs) hs

end CFSG.LocalAnalysis.RankThreeTheoremC
