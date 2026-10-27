module

import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFH0Consumer
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.FFH0Final
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Defs
public import CFSG.Quasithin.Background.C118NoOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

@[expose] def FFGroupStep3Free (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → ∀ T : Subgroup G, IsSylowTwoOf T M →
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

theorem ffGroupStep3Free : FFGroupStep3Free G := by
  intro d P M A H R Rbar K ctx T hT hNT hU I hMN hcard hJM hSyl hperm hfam L hL
  have := ctx.amb
  have hc := ctx.conf
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  have hVM : conjClosure (quasithinOmegaOneCenter T) M ≤ M :=
    hle.trans (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M))
  have hVT : conjClosure (quasithinOmegaOneCenter T) M ≤ T :=
    hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
  have hBJ : autI hU (baum T) ≤ autI hU (thompsonJ M) :=
    autI_baum_le_autI_thompsonJ hMN hT hVT hfam hJM (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
      hperm
  have hctx : FFCtx M T (conjClosure (quasithinOmegaOneCenter T) M) hU hMN I :=
    ⟨hVM, rfl, hT, hF, hcard, hJM, hSyl, hperm, hfam, hBJ⟩
  obtain ⟨H₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    FFH0Hyp.exists_H₀ invariantCyclicSupplement ⟨hF, hT, hle, hfam, hcard, hJM, hSyl, hperm, hL⟩
      hMN
  exact ⟨H₀, FFH0Spec.conclusion hctx hL
    (⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :
      FFH0Spec M T (conjClosure (quasithinOmegaOneCenter T) M) hU L H₀)⟩

theorem exists_ffPairData3_free (hN : NoXBlockFor G) (hGS : FFGroupStep3Free G)
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) {T : Subgroup G} (hT : IsSylowTwoOf T M)
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
    obtain ⟨H₀, hHM, hHL, hH3, hGcl, hblock⟩ := hGS d P M A H R Rbar K ctx T hT hNT hU
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
