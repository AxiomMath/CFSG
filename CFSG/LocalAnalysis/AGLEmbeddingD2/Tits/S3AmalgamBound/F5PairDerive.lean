module

public import CFSG.Quasithin.Background.C118NoOuter
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Pair

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim

@[expose] def FFGroupStep : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M →
    ∀ (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) M))
      (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU)))),
      M ≤ Subgroup.normalizer ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) : Set G) →
      (∀ L ∈ I, Nat.card L = 6) → autI hU (thompsonJ M) = ⨆ L ∈ I, L →
      IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)) →
      (∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) → S3Family I →
      ∀ L ∈ I, ∃ H₀ : Subgroup G, H₀ ≤ M ∧ L ≤ autI hU H₀ ∧
        (∀ Q : Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU)),
          Q ≤ autI hU H₀ → IsPGroup 3 Q → Nat.card Q ≤ 3) ∧
        InClassG H₀ (baum T) ∧
        (IsL2OrA3Block H₀ (twoResidual H₀) →
          ∃ Y : Subgroup G, Y ≤ M ∧ IsSubnormal Y M ∧ InClassXBlock Y)

theorem ffPairStep_of_groupStep (hN : D1NoXBlock) (hG : FFGroupStep) : FFPairStep := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl hperm hfam
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact B6.pCoreOf_two_le_of_isSylowTwoOf hT
  obtain ⟨C₁, C₂, h1, h1Z, h1char, h2, h2B, h2char, hall⟩ := theoremC118 G T hT.2.1 hT1
  have hZV : quasithinOmegaOneCenter T ≤ conjClosure (quasithinOmegaOneCenter T) M :=
    le_conjClosure _ M
  have hC₁T : C₁ ≤ T := h1Z.trans (C1GN.omegaOneCenterOf_le_self T)
  have hC₂T : C₂ ≤ baum T := h2B
  have hC₁B : C₁ ≤ baum T := h1Z.trans (C1GN.omegaOneCenterOf_le_baum T)
  refine ⟨C₁, C₂, h1, hT.2.1.to_le hC₁T, h2, hT.2.1.to_le (h2B.trans (C1GN.baum_le T)), ?_, ?_, ?_,
    ?_, ?_⟩
  · exact (normalizer_le_normalizer_of_characteristic_subgroupOf hC₁T h1char)
  · exact (normalizer_le_normalizer_baum T).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hC₂T h2char)
  · intro x hx
    have hxc : ∀ c ∈ C₁, c * x = x * c := fun c hc =>
      Subgroup.mem_centralizer_iff.1 hx.1 c (hZV (h1Z hc))
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hxc)
  · exact fun x hx => normalizer_le_normalizer_of_characteristic_subgroupOf hC₂T h2char hx.2
  · intro L hL
    obtain ⟨H₀, hHM, hHL, hH3, hGcl, hblock⟩ := hG d G P M A H R Rbar K hc hstr hAll T hT hNT hU I
      hMN hcard hJM hSyl hperm hfam L hL
    refine ⟨H₀, hHM, hHL, hH3, ?_⟩
    have hd := hall G H₀ (baum T).subtype (baum T).subtype_injective
      (by rwa [Subgroup.range_subtype])
    rw [Subgroup.map_subgroupOf_eq_of_le hC₁B, Subgroup.map_subgroupOf_eq_of_le h2B] at hd
    rcases hd with h | h | h
    · left
      intro x hx
      have hxc : ∀ c ∈ C₁, c * x = x * c := fun c hc =>
        ((Subgroup.mem_centralizer_iff.1 (h hc).2 x hx)).symm
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hxc)
    · exact Or.inr h
    · exfalso
      obtain ⟨Y, hYM, hYs, hYX⟩ := hblock h
      exact hN G hc.glob.toAGLGlobal M Y hc.esc.maxTwoLocal_M hYM hYs hYX

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
