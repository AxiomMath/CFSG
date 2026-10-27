module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Escape
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFConstrained
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5End
public import CFSG.Quasithin.Background.C118NoOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

theorem ffQuotientConstrained3
    [D2Amb3 G] {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) (S : Sylow 3 ↥(ffC M T))
    (hS : ¬ IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype)) :
    CFSG.ABGLocalTools.IsPConstrained 3
      ↥(autOn M (conjClosure (quasithinOmegaOneCenter T) M)) := by
  set Z := quasithinOmegaOneCenter T with hZdef
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1
  have hZ2 : IsPGroup 2 Z := hT.2.1.to_le (Setup.omegaOneCenterOf_le T)
  have hNZ : ¬ Subgroup.normalizer (Z : Set G) ≤ M := fun h =>
    hNT ((CFSG.AGLEmbeddingD2.Tits.MsidePrelim.normalizer_le_normalizer_quasithinOmegaOneCenter
      T).trans h)
  have hCZ : ffC M T ≤ M ⊓ Subgroup.normalizer (Z : Set G) := by
    refine le_inf inf_le_right (inf_le_left.trans ?_)
    exact (Subgroup.centralizer_le (CFSG.Quasithin.le_conjClosure Z M)).trans
      (Subgroup.centralizer_le_normalizer _)
  have h9 : ∀ X : Subgroup G, X ≤ ffC M T → IsPGroup 3 X → ¬ IsCyclic X → Nat.card X ≤ 9 :=
    fun X hX hXp hXc => D2L34BetaConf3.card_le_nine_of_le_normalizer hc hstr hZ1 hZ2 hNZ
      (hX.trans hCZ) hXp hXc
  exact ffQuotientConstrained3_of_small hcon S hS h9

theorem exists_ffPairData3 (hN : NoXBlockFor G) (hGS : FFGroupStep3 G)
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) M))
    (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU))))
    (hMN : M ≤ Subgroup.normalizer ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) :
      Set G))
    (hcard : ∀ L ∈ I, Nat.card L = 6) (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L)
    (hSyl : IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)))
    (hperm : ∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) (hfam : S3Family I) :
    ∃ C₁ C₂ : Subgroup G, FFPairData M T hU I C₁ C₂ := by
  have hc := ctx.conf
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
  refine ⟨C₁, C₂, h1, hT.2.1.to_le hC₁T, h2, hT.2.1.to_le (h2B.trans (C1GN.baum_le T)), ?_, ?_,
    ?_, ?_, ?_⟩
  · exact (normalizer_le_normalizer_of_characteristic_subgroupOf hC₁T h1char)
  · exact (normalizer_le_normalizer_baum T).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hC₂T h2char)
  · intro x hx
    have hxc : ∀ c ∈ C₁, c * x = x * c := fun c hc =>
      Subgroup.mem_centralizer_iff.1 hx.1 c (hZV (h1Z hc))
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hxc)
  · exact fun x hx => normalizer_le_normalizer_of_characteristic_subgroupOf hC₂T h2char hx.2
  · intro L hL
    obtain ⟨H₀, hHM, hHL, hH3, hGcl, hblock⟩ := hGS d P M A H R Rbar K ctx hstr hcon T hT hNT hU
      I hMN hcard hJM hSyl hperm hfam L hL
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
      exact hN M Y hc.esc.maxTwoLocal_M hYM hYs hYX

end CFSG.LocalAnalysis.RankThreeTheoremC
