module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogOmega
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogOrth

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open LinearFlag
open scoped MatrixGroups

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def twistedSwapHom (e : L ≃* StatedSp 3 K) (σ : K ≃+* F)
    (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0) :
    SL(2, K) × SL(2, K) →* G :=
  ((neighbourCore e 0).subtype.comp Φ.toMonoidHom).comp
    (swapPairSL.comp ((Matrix.SpecialLinearGroup.map (σ : K →+* F)).prodMap
      (Matrix.SpecialLinearGroup.map (σ : K →+* F))))

omit [Finite G] [Finite K] [CharP K 2] [Finite F] [CharP F 2] in
theorem twistedSwapHom_apply (e : L ≃* StatedSp 3 K) (σ : K ≃+* F)
    (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0) (p : SL(2, K) × SL(2, K)) :
    twistedSwapHom e σ Φ p = ((Φ (swapPairSL (Matrix.SpecialLinearGroup.map (σ : K →+* F) p.1,
      Matrix.SpecialLinearGroup.map (σ : K →+* F) p.2)) : neighbourCore e 0) : G) :=
  rfl

omit [Finite G] [Finite K] [CharP K 2] [CharP F 2] in
theorem range_twistedSwapHom (e : L ≃* StatedSp 3 K) (σ : K ≃+* F)
    (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hM : pieceCore e ({2} : Finset (Fin 3)) =
      ((blockSpecialLinear (K := F) (twBlockSL 0) ⊔
        blockSpecialLinear (K := F) (twBlockSL 0)ᶜ).map Φ.toMonoidHom).map
          (neighbourCore e 0).subtype) :
    (twistedSwapHom e σ Φ).range = pieceCore e ({2} : Finset (Fin 3)) := by
  have hsurj : Function.Surjective
      ((Matrix.SpecialLinearGroup.map (n := Fin 2) (σ : K →+* F)).prodMap
        (Matrix.SpecialLinearGroup.map (n := Fin 2) (σ : K →+* F))) := by
    rintro ⟨X, Y⟩
    refine ⟨(Matrix.SpecialLinearGroup.map (σ.symm : F →+* K) X,
      Matrix.SpecialLinearGroup.map (σ.symm : F →+* K) Y), ?_⟩
    ext <;> simp
  rw [hM, twistedSwapHom, MonoidHom.range_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 hsurj, Subgroup.map_top, range_swapPairSL, Subgroup.map_map]

omit [Finite G] [Finite K] [Finite F] in
theorem twistedSwapHom_diag (e : L ≃* StatedSp 3 K) (σ : K ≃+* F)
    (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp x))) : neighbourCore e 0) : G) =
        ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G)) (A : SL(2, K)) :
    twistedSwapHom e σ Φ (A, A) = ((e.symm (longBlock K 3 2 A) : L) : G) := by
  rw [twistedSwapHom_apply, ← spModelSL_statedSpMap_tauSp_longBlock_one, hN1,
    coe_complSpEquiv_apply, spEmbed_longBlock]
  rfl

omit [Finite G] [Finite K] [CharP K 2] [Finite F] in
theorem conj_twistedSwapHom (e : L ≃* StatedSp 3 K) (σ : K ≃+* F) {t : G}
    (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hN3 : ∀ y : SpecialLinearGroup (Fin (2 * 2)) F,
      t * (Φ y : G) * t⁻¹ = (Φ ((slFourEquivProj F).symm
        ((conjAut (2 * 2) F (spBlockSwapGL 2 F) * dualAut (2 * 2) F) (proj (2 * 2) F y))) : G))
    (p : SL(2, K) × SL(2, K)) :
    t * twistedSwapHom e σ Φ p * t⁻¹ = twistedSwapHom e σ Φ p.swap := by
  rw [twistedSwapHom_apply, twistedSwapHom_apply, hN3, slFourEquivProj_symm_graph_swapPairSL]
  rfl

theorem modelToG_simpleRootSL2_zero_le_centralizer_pieceCore_two_of_twisted
    (hset : SeitzSetting G L) (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (σ : K ≃+* F)
    (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp x))) : neighbourCore e 0) : G) =
        ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G))
    (hN3 : ∀ y : SpecialLinearGroup (Fin (2 * 2)) F,
      t * (Φ y : G) * t⁻¹ = (Φ ((slFourEquivProj F).symm
        ((conjAut (2 * 2) F (spBlockSwapGL 2 F) * dualAut (2 * 2) F) (proj (2 * 2) F y))) : G)) :
    modelToG e (simpleRootSL2 K (0 : Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) :=
  modelToG_simpleRootSL2_zero_le_centralizer_pieceCore_two_of_swapHom hset hK e htC ht
    (twistedSwapHom e σ Φ)
    (range_twistedSwapHom e σ Φ (pieceCore_two_eq_of_twisted hK e σ Φ hN1))
    (twistedSwapHom_diag e σ Φ hN1) (conj_twistedSwapHom e σ Φ hN3)

end Swap


section Pairs

variable {K : Type} [Field K] [Finite K] {F : Type} [Field F] [Finite F]

omit [Finite K] [Finite F] in
theorem reindex_mem_blockSpecialLinear {n : ℕ} (ε : Equiv.Perm (Fin n)) {I : Finset (Fin n)}
    {x : SpecialLinearGroup (Fin n) F} (hx : x ∈ blockSpecialLinear I) :
    LinearPilot.reindexSpecialLinear (K := F) ε x ∈ blockSpecialLinear (I.map ε.toEmbedding) := by
  intro i j hij
  change (reindex ε ε (x : Matrix (Fin n) (Fin n) F)) i j = (1 : Matrix (Fin n) (Fin n) F) i j
  rw [reindex_apply, submatrix_apply]
  have hij' : ε.symm i ∉ I ∨ ε.symm j ∉ I := by
    rcases hij with h | h
    · refine Or.inl fun h' => h ?_
      rw [Finset.mem_map]
      exact ⟨ε.symm i, h', by simp⟩
    · refine Or.inr fun h' => h ?_
      rw [Finset.mem_map]
      exact ⟨ε.symm j, h', by simp⟩
  rw [hx _ _ hij']
  simp only [Matrix.one_apply, ε.symm.injective.eq_iff]

variable [CharP F 2]

omit [CharP F 2] in
theorem map_range_blockSL_reindex {G : Type*} [Group G] [Finite G] {j : ℕ} (hj : j + 2 ≤ 3)
    (ε : Equiv.Perm (Fin (2 * 2))) (σ : K ≃+* F)
    (Ψ : SpecialLinearGroup (Fin (2 * 2)) F →* G) (hΨ : Function.Injective Ψ) :
    (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 j hj).range.map
        (Ψ.comp ((LinearPilot.reindexSpecialLinear (K := F) ε).toMonoidHom.comp
          ((CFSG.ClassicalInvolution.WeakCT.blockSL F (2 * 2) 3 0 (by omega)).comp
            (Matrix.SpecialLinearGroup.map (σ : K →+* F))))) =
      (blockSpecialLinear (K := F)
        ((LinearPilot.consecutiveBlock (2 * 2) j 2).map ε.toEmbedding)).map Ψ := by
  have hle : (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 j hj).range.map
        (Ψ.comp ((LinearPilot.reindexSpecialLinear (K := F) ε).toMonoidHom.comp
          ((CFSG.ClassicalInvolution.WeakCT.blockSL F (2 * 2) 3 0 (by omega)).comp
            (Matrix.SpecialLinearGroup.map (σ : K →+* F))))) ≤
      (blockSpecialLinear (K := F)
        ((LinearPilot.consecutiveBlock (2 * 2) j 2).map ε.toEmbedding)).map Ψ := by
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    have h1 : Matrix.SpecialLinearGroup.map (σ : K →+* F)
        (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 j hj A) ∈
          (CFSG.ClassicalInvolution.WeakCT.blockSL F 3 2 j hj).range := by
      rw [LinearPilot.range_blockSL_eq hj]
      apply LinearPilot.map_ringHom_mem_blockSpecialLinear
      rw [← LinearPilot.range_blockSL_eq hj]
      exact ⟨A, rfl⟩
    obtain ⟨B, hB⟩ := h1
    refine ⟨_, reindex_mem_blockSpecialLinear ε (x := CFSG.ClassicalInvolution.WeakCT.blockSL F
      (2 * 2) 2 j (by omega) B) ?_, ?_⟩
    · rw [← LinearPilot.range_blockSL_eq (by omega : j + 2 ≤ 2 * 2)]
      exact ⟨B, rfl⟩
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [← hB, CFSG.ClassicalInvolution.WeakCT.blockSL_comp_apply]
      simp
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hinj : Function.Injective
      (Ψ.comp ((LinearPilot.reindexSpecialLinear (K := F) ε).toMonoidHom.comp
          ((CFSG.ClassicalInvolution.WeakCT.blockSL F (2 * 2) 3 0 (by omega)).comp
            (Matrix.SpecialLinearGroup.map (σ : K →+* F))))) := by
    refine hΨ.comp ((LinearPilot.reindexSpecialLinear (K := F) ε).injective.comp
      ((CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := F) (m := 2 * 2) (k := 3) (i := 0)
        (by omega)).comp ?_))
    intro x y hxy
    apply Subtype.ext
    ext a b
    have h := congrArg (fun M : SpecialLinearGroup (Fin 3) F =>
      (M : Matrix (Fin 3) (Fin 3) F) a b) hxy
    simpa using h
  rw [Subgroup.card_map_of_injective hΨ, Subgroup.card_map_of_injective hinj,
    natCard_blockSpecialLinear_of_card_two (by
      rw [Finset.card_map]
      have hj' : j ≤ 1 := by omega
      interval_cases j <;> decide),
    ← Nat.card_congr (MonoidHom.ofInjective
      (CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := K) hj)).toEquiv,
    natCard_SL_two_congr σ]

end Pairs

end CFSG.SeitzReduction.SymplecticPilot
