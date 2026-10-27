module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogOmegaOrth
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogLift

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open LinearFlag
open scoped MatrixGroups

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

@[expose] def epsA : Equiv.Perm (Fin (2 * 2)) := Equiv.swap 0 2 * Equiv.swap 0 3

@[expose] def epsB : Equiv.Perm (Fin (2 * 2)) := Equiv.swap 0 3 * Equiv.swap 0 1

theorem epsA_block_zero :
    (LinearPilot.consecutiveBlock (2 * 2) 0 2).map epsA.toEmbedding = offPlaneSL 0 := by decide

theorem epsA_block_one :
    (LinearPilot.consecutiveBlock (2 * 2) 1 2).map epsA.toEmbedding = twBlockSL 0 := by decide

theorem epsB_block_zero :
    (LinearPilot.consecutiveBlock (2 * 2) 0 2).map epsB.toEmbedding = offPlaneSL 0 := by decide

theorem epsB_block_one :
    (LinearPilot.consecutiveBlock (2 * 2) 1 2).map epsB.toEmbedding = (twBlockSL 0)ᶜ := by decide

omit [CharP K 2] in
theorem exists_theta_of_reindex {F : Type} [Field F] [Finite F] [CharP F 2] (σ : K ≃+* F)
    (Ψ : SpecialLinearGroup (Fin (2 * 2)) F →* G) (hΨ : Function.Injective Ψ)
    (ε : Equiv.Perm (Fin (2 * 2))) {I₁ I₂ : Finset (Fin (2 * 2))}
    (h₁ : (LinearPilot.consecutiveBlock (2 * 2) 0 2).map ε.toEmbedding = I₁)
    (h₂ : (LinearPilot.consecutiveBlock (2 * 2) 1 2).map ε.toEmbedding = I₂) :
    ∃ θ : SL(3, K) →* G, θ.ker ≤ center SL(3, K) ∧
      (B12 K).map θ = (blockSpecialLinear (K := F) I₁).map Ψ ∧
      (B23 K).map θ = (blockSpecialLinear (K := F) I₂).map Ψ := by
  set θ : SL(3, K) →* G := Ψ.comp ((LinearPilot.reindexSpecialLinear (K := F) ε).toMonoidHom.comp
    ((CFSG.ClassicalInvolution.WeakCT.blockSL F (2 * 2) 3 0 (by omega)).comp
      (Matrix.SpecialLinearGroup.map (σ : K →+* F)))) with hθ
  have hinj : Function.Injective θ := by
    refine hΨ.comp ((LinearPilot.reindexSpecialLinear (K := F) ε).injective.comp
      ((CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := F) (m := 2 * 2) (k := 3) (i := 0)
        (by omega)).comp ?_))
    intro x y hxy
    apply Subtype.ext
    ext a b
    have h := congrArg (fun M : SpecialLinearGroup (Fin 3) F =>
      (M : Matrix (Fin 3) (Fin 3) F) a b) hxy
    simpa using h
  refine ⟨θ, ?_, ?_, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff θ).2 hinj]
    exact bot_le
  · rw [← h₁]
    exact map_range_blockSL_reindex (j := 0) (by omega) ε σ Ψ hΨ
  · rw [← h₂]
    exact map_range_blockSL_reindex (j := 1) (by omega) ε σ Ψ hΨ

theorem spOmegaPlusPieces_of_twisted {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hroot : ∀ k : Fin 3, RootKindSp e t f k .linearEven) (htw : SpThreeTwisted e) :
    SpOmegaPlusPieces (m := 1) e := by
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨F₀, _, _, _, σ₀, Φ₀, -, hN1₀, hN3₀⟩ := exists_mulEquiv_of_spThreeLinearNormalized hKc hf
    (spThreeLinearNormalized_of_twisted hset hKc hf e htC ht 0 (hroot 0) htw)
  obtain ⟨F₂, _, _, _, σ₂, Φ₂, -, hN1₂, -⟩ := exists_mulEquiv_of_spThreeLinearNormalized hKc hf
    (spThreeLinearNormalized_of_twisted hset hKc hf e htC ht 2 (hroot 2) htw)
  set Ψ : SpecialLinearGroup (Fin (2 * 2)) F₀ →* G :=
    (neighbourCore e 0).subtype.comp Φ₀.toMonoidHom with hΨ
  have hΨinj : Function.Injective Ψ := (neighbourCore e 0).subtype_injective.comp Φ₀.injective
  have hmap : ∀ H : Subgroup (SpecialLinearGroup (Fin (2 * 2)) F₀),
      (H.map Φ₀.toMonoidHom).map (neighbourCore e 0).subtype = H.map Ψ := fun H => by
    rw [hΨ, Subgroup.map_map]
  refine ⟨?_, (blockSpecialLinear (K := F₀) (twBlockSL 0)).map Ψ,
    (blockSpecialLinear (K := F₀) (twBlockSL 0)ᶜ).map Ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    fin_cases j
    · exact pieceCore_zero_eq_of_twisted hK e σ₂ Φ₂ hN1₂
    · exact pieceCore_one_eq_of_twisted hK e σ₀ Φ₀ hN1₀
    · exact absurd hj (by decide)
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ (LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right
      hy hx).eq
  · rw [← Subgroup.map_sup, ← hmap]
    exact (pieceCore_two_eq_of_twisted hK e σ₀ Φ₀ hN1₀).symm
  · intro i hi
    have hi0 : i = 0 := by
      ext
      simp only [Fin.val_zero]
      omega
    subst hi0
    exact modelToG_simpleRootSL2_zero_le_centralizer_pieceCore_two_of_twisted hset hK e htC ht σ₀
      Φ₀ hN1₀ hN3₀
  · obtain ⟨θ, hker, h1, h2⟩ := exists_theta_of_reindex σ₀ Ψ hΨinj epsA epsA_block_zero
      epsA_block_one
    refine ⟨θ, hker, ?_, h2⟩
    rw [h1, ← hmap, ← pieceCore_one_eq_map_of_twisted hK e σ₀ Φ₀ hN1₀]
    exact pieceCore_one_eq_of_twisted hK e σ₀ Φ₀ hN1₀
  · obtain ⟨θ, hker, h1, h2⟩ := exists_theta_of_reindex σ₀ Ψ hΨinj epsB epsB_block_zero
      epsB_block_one
    refine ⟨θ, hker, ?_, h2⟩
    rw [h1, ← hmap, ← pieceCore_one_eq_map_of_twisted hK e σ₀ Φ₀ hN1₀]
    exact pieceCore_one_eq_of_twisted hK e σ₀ Φ₀ hN1₀

theorem spThreeLinearEvenTwistedInput_holds :
    SpThreeLinearEvenTwistedInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot htw
  have htC : t ∈ centralizer (L : Set G) := by
    have h1 : t ∈ zpowers t := mem_zpowers t
    rw [← hKt] at h1
    exact h1.1
  exact sp2mKindType_omegaPlus_three_of_pieces hKc hf e
    (spOmegaPlusPieces_of_twisted hset hKc hf e htC hto hroot htw)

theorem spThreeLinearEvenRecognitionInput_of_standardInput
    (hs : SpThreeLinearEvenStandardInput) : SpThreeLinearEvenRecognitionInput :=
  spThreeLinearEvenRecognitionInput_of_oriented hs spThreeLinearEvenTwistedInput_holds

end Main

end CFSG.SeitzReduction.SymplecticPilot
