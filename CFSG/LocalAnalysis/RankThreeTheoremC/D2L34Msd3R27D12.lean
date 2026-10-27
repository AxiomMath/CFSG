module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Kmax
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Weak
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.E81

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

private theorem isSylowTwoOf_inf_of_le {T M N : Subgroup G} (hT : IsSylowTwoOf T M)
    (hTN : T ≤ N) : IsSylowTwoOf T (N ⊓ M) := by
  refine ⟨le_inf hTN hT.1, hT.2.1, fun h => hT.2.2 ?_⟩
  have := Subgroup.relIndex_mul_relIndex T (N ⊓ M) M (le_inf hTN hT.1) inf_le_right
  exact h.trans ⟨_, this.symm⟩

private theorem card_eq_of_sylow_map {X Y : Subgroup G} (S : Sylow 3 X)
    (hS : (S : Subgroup X).map X.subtype = Y) :
    Nat.card Y = 3 ^ (Nat.card X).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← hS, Subgroup.card_map_of_injective X.subtype_injective]
  exact S.card_eq_multiplicity

theorem D2L34SideCtx3.noNonExtremal_of_l34
    (hFF : CitedFFL34BestOffender) (ctx : D2L34SideCtx3 G d P M A H R Rbar K)
    (h27 : Nat.card R = 27) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M))
    (hNE : D2NonExtremalL34At P M T) : D2NoNonExtremalAt P M T := by
  intro E N hesc hTN
  have : D2Amb3 G := ctx.amb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := ctx.conf
  have hTM : IsSylowTwoOf T M := (ctx.isSylowTwoOf_of_card27 hFF h27 hT hNE).1
  have hNTM : ¬ Subgroup.normalizer (T : Set G) ≤ M := hc.not_normalizer_le_of_isSylowTwoOf' hT
  have hTH : T ≤ H := hT.1.trans inf_le_left
  have hTN' : T ≤ N := Subgroup.le_normalizer.trans hTN
  have hT₁ : IsSylowTwoOf T (N ⊓ M) := isSylowTwoOf_inf_of_le hTM hTN'
  obtain ⟨d', Ebar, K', hw⟩ := hNE.exists_weakConf hesc hTN
  have hrk := ctx.normRankTwo
  have hmax := hc.card_le_27 h27
  have hO2H : pCoreOf 2 M ≤ H := hc.pCoreOf_two_le
  have hO2N : pCoreOf 2 M ≤ N :=
    (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hTM).trans hTN'
  obtain ⟨BH, hBHA, hBHHM, hBHel, hBH9, hBHU, hTBHU⟩ := hc.exists_permuting_elemAbelian_map_eq hT
  obtain ⟨BN, hBNA, hBNHM, hBNel, hBN9, hBNU, hTBNU⟩ := hw.exists_permuting_elemAbelian_map_eq hT₁
  have h3H := hc.two_of_three_normalized_of_map_eq hT (hBHHM.trans inf_le_left) hBHA hBHel hBH9
    hBHU hTBHU
  have h3N := hw.two_of_three_normalized_of_map_eq hT₁ (hBNHM.trans inf_le_left) hBNA hBNel hBN9
    hBNU hTBNU
  set Zc := (CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype with hZc
  set Jc := (CFSG.higherElemThompson ↥T 0).map T.subtype with hJc
  set Ec := (CFSG.higherElemThompsonOmega ↥T 1).map T.subtype with hEc
  have hZcT := OrdinaryProofs.normalizer_le_normalizer_omegaOneCenter_top T
  have hJcT := OrdinaryProofs.normalizer_le_normalizer_higherElemThompson T 0
  have hEcT := OrdinaryProofs.normalizer_le_normalizer_higherElemThompsonOmega T 1
  let good : Subgroup G → Subgroup G → Prop := fun X C =>
    ∀ N' : Subgroup G, GLBIsMaxTwoLocal N' → Subgroup.normalizer (C : Set G) ≤ N' → N' = X
  have hgH : ∀ C : Subgroup G,
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) →
      BH ≤ Subgroup.normalizer (C : Set G) → good H C := by
    intro C hCT hBC N' hN' hCN'
    have hcov := hc.cover_of_isSylowTwoOf_of_map_eq hT hBHA
      (Y := H ⊓ Subgroup.normalizer (C : Set G))
      (le_inf hTH (Subgroup.le_normalizer.trans hCT)) (le_inf (hBHHM.trans inf_le_left) hBC)
      (inf_le_inf_left H hCT)
    exact hc.toWeak.eq_of_maxTwoLocal_of_normalizer_cover27 hrk ctx.allResidue hmax hO2H hNE
      hcov hN' hCN' (hCT.trans hCN')
  have hgN : ∀ C : Subgroup G,
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) →
      BN ≤ Subgroup.normalizer (C : Set G) → good N C := by
    intro C hCT hBC N' hN' hCN'
    have hcov := hw.cover_of_isSylowTwoOf_of_map_eq hT₁ hBNA
      (Y := N ⊓ Subgroup.normalizer (C : Set G))
      (le_inf hTN' (Subgroup.le_normalizer.trans hCT)) (le_inf (hBNHM.trans inf_le_left) hBC)
      (inf_le_inf_left N hCT)
    exact hw.eq_of_maxTwoLocal_of_normalizer_cover27 hrk ctx.allResidue hmax hO2N hNE
      hcov hN' hCN' (hCT.trans hCN')
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hTM
  have : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  have hT2 : IsPGroup 2 ↥T := hTM.2.1
  have hne : ∀ C : Subgroup G, (C = Zc ∨ C = Jc ∨ C = Ec) → C ≠ ⊥ ∧ IsPGroup 2 C := by
    rintro C (rfl | rfl | rfl)
    · refine ⟨fun h => ?_, hTM.2.1.to_le (Subgroup.map_subtype_le _)⟩
      rw [Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at h
      exact OrdinaryProofs.omegaOneCenter_top_ne_bot hT2 h
    · refine ⟨fun h => ?_, hTM.2.1.to_le (Subgroup.map_subtype_le _)⟩
      rw [Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at h
      exact OrdinaryProofs.higherElemThompson_zero_ne_bot hT2 h
    · refine ⟨fun h => ?_, hTM.2.1.to_le (Subgroup.map_subtype_le _)⟩
      rw [Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at h
      exact OrdinaryProofs.higherElemThompsonOmega_one_ne_bot hT2
        (D2L34BetaConf3.two_le_pRank_of_isSylowTwoOf hc hTM hNTM) h
  have hUH : (good H Zc ∧ good H Jc) ∨ (good H Zc ∧ good H Ec) ∨ (good H Jc ∧ good H Ec) := by
    rcases h3H with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hgH _ hZcT h1, hgH _ hJcT h2⟩
    · exact Or.inr (Or.inl ⟨hgH _ hZcT h1, hgH _ hEcT h2⟩)
    · exact Or.inr (Or.inr ⟨hgH _ hJcT h1, hgH _ hEcT h2⟩)
  have hUN : (good N Zc ∧ good N Jc) ∨ (good N Zc ∧ good N Ec) ∨ (good N Jc ∧ good N Ec) := by
    rcases h3N with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hgN _ hZcT h1, hgN _ hJcT h2⟩
    · exact Or.inr (Or.inl ⟨hgN _ hZcT h1, hgN _ hEcT h2⟩)
    · exact Or.inr (Or.inr ⟨hgN _ hJcT h1, hgN _ hEcT h2⟩)
  have hcommon : ∃ C : Subgroup G, (C = Zc ∨ C = Jc ∨ C = Ec) ∧ good H C ∧ good N C := by
    rcases hUH with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
      rcases hUN with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
      first
        | exact ⟨Zc, Or.inl rfl, ‹good H Zc›, ‹good N Zc›⟩
        | exact ⟨Jc, Or.inr (Or.inl rfl), ‹good H Jc›, ‹good N Jc›⟩
        | exact ⟨Ec, Or.inr (Or.inr rfl), ‹good H Ec›, ‹good N Ec›⟩
  obtain ⟨C, hC, hCH, hCN⟩ := hcommon
  obtain ⟨hC1, hC2⟩ := hne C hC
  obtain ⟨N'', hNC, hN''⟩ := exists_maximal_twoLocal (⟨C, hC1, hC2, rfl⟩ :
    IsTwoLocal (Subgroup.normalizer (C : Set G)))
  have hHN : H = N := (hCH N'' hN'' hNC).symm.trans (hCN N'' hN'' hNC)
  obtain ⟨SE, hSE⟩ := hesc.isSylow
  obtain ⟨SR, hSR⟩ := hc.esc.isSylow
  have hE := card_eq_of_sylow_map SE hSE
  have hR := card_eq_of_sylow_map SR hSR
  rw [hHN, ← hE, h27, hesc.card_A] at hR
  norm_num at hR

end CFSG.LocalAnalysis.RankThreeTheoremC
