module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogTwisted
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelShape

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (statedSpMap coe_statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open LinearFlag
open scoped MatrixGroups

section Pieces

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite G] [Finite K] [CharP K 2] [Finite F] [CharP F 2] in
theorem natCard_modelToG_simpleRootSL2 (e : L ≃* StatedSp 3 K) (j : Fin 3) :
    Nat.card (modelToG e (simpleRootSL2 K j)) = Nat.card (SpecialLinearGroup (Fin 2) K) := by
  rw [UnitaryPilot.card_modelToG, simpleRootSL2]
  exact (Nat.card_congr (MonoidHom.ofInjective (simpleRootHom_injective (K := K) j)).toEquiv).symm

omit [Finite G] [CharP K 2] [CharP F 2] in
theorem natCard_SL_two_congr (σ : K ≃+* F) :
    Nat.card (SpecialLinearGroup (Fin 2) F) = Nat.card (SpecialLinearGroup (Fin 2) K) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_congr σ.toEquiv]

omit [CharP K 2] [CharP F 2] in
theorem pieceCore_eq_modelToG_of_eq_map (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    {k : Fin 3} {J : Finset (Fin 3)} {j : Fin 3} (hj : j ∈ J) (σ : K ≃+* F)
    (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e k) {I : Finset (Fin (2 * 2))}
    (hI : I.card = 2)
    (h : pieceCore e J = ((blockSpecialLinear (K := F) I).map Φ.toMonoidHom).map
      (neighbourCore e k).subtype) :
    pieceCore e J = modelToG e (simpleRootSL2 K j) := by
  symm
  apply Subgroup.eq_of_le_of_card_ge (modelToG_simpleRootSL2_le_pieceCore e hK hj)
  rw [h, Subgroup.card_map_of_injective (neighbourCore e k).subtype_injective,
    Subgroup.card_map_of_injective Φ.injective, natCard_blockSpecialLinear_of_card_two hI,
    natCard_modelToG_simpleRootSL2, natCard_SL_two_congr σ]

theorem pieceCore_zero_eq_of_twisted (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (σ : K ≃+* F) (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 2)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp x))) : neighbourCore e 2) : G) =
        ((e.symm (complSpEquiv 2 x : complSp K 2) : L) : G)) :
    pieceCore e ({0} : Finset (Fin 3)) = modelToG e (simpleRootSL2 K 0) := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  refine pieceCore_eq_modelToG_of_eq_map hK e (Finset.mem_singleton_self 0) σ Φ
    (card_offPlaneSL 0) ?_
  exact pieceCore_eq_map_of_N1 hK e (k := 2) (by decide) σ tauSp Φ hN1 (siegelTorus K 2)
    leviTorusSp_zero_le_sup map_siegelTorus_two_le_leviTorusSp_zero
    (by rw [map_twisted_siegelTorus_eq]; exact perfectCore_centralizer_stdTorusSL hF4 0)

theorem pieceCore_one_eq_map_of_twisted (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (σ : K ≃+* F) (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp x))) : neighbourCore e 0) : G) =
        ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G)) :
    pieceCore e ({1} : Finset (Fin 3)) =
      ((blockSpecialLinear (K := F) (offPlaneSL 0)).map Φ.toMonoidHom).map
        (neighbourCore e 0).subtype := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  exact pieceCore_eq_map_of_N1 hK e (k := 0) (by decide) σ tauSp Φ hN1 (siegelTorus K 2)
    leviTorusSp_one_le_sup map_siegelTorus_zero_le_leviTorusSp_one
    (by rw [map_twisted_siegelTorus_eq]; exact perfectCore_centralizer_stdTorusSL hF4 0)

theorem pieceCore_one_eq_of_twisted (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (σ : K ≃+* F) (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp x))) : neighbourCore e 0) : G) =
        ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G)) :
    pieceCore e ({1} : Finset (Fin 3)) = modelToG e (simpleRootSL2 K 1) := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  refine pieceCore_eq_modelToG_of_eq_map hK e (Finset.mem_singleton_self 1) σ Φ
    (card_offPlaneSL 0) ?_
  exact pieceCore_eq_map_of_N1 hK e (k := 0) (by decide) σ tauSp Φ hN1 (siegelTorus K 2)
    leviTorusSp_one_le_sup map_siegelTorus_zero_le_leviTorusSp_one
    (by rw [map_twisted_siegelTorus_eq]; exact perfectCore_centralizer_stdTorusSL hF4 0)

omit [Finite K] in
theorem pieceCore_two_eq_of_twisted (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (σ : K ≃+* F) (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp x))) : neighbourCore e 0) : G) =
        ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G)) :
    pieceCore e ({2} : Finset (Fin 3)) =
      ((blockSpecialLinear (K := F) (twBlockSL 0) ⊔
        blockSpecialLinear (K := F) (twBlockSL 0)ᶜ).map Φ.toMonoidHom).map
          (neighbourCore e 0).subtype := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  exact pieceCore_eq_map_of_N1 hK e (k := 0) (by decide) σ tauSp Φ hN1 (rootTorusSp K 0)
    leviTorusSp_two_le_sup map_rootTorusSp_zero_le_leviTorusSp_two
    (by rw [map_twisted_rootTorusSp_zero_eq]; exact perfectCore_centralizer_twTorusSL hF4 0)

end Pieces

section SwapModel

variable {F : Type} [Field F]

@[expose] noncomputable def swapPairMat (X Y : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin (2 * 2)) (Fin (2 * 2)) F :=
  (Matrix.fromBlocks X 0 0 Y).submatrix (spModelIdx 2).symm (spModelIdx 2).symm

theorem swapPairMat_mul (X Y X' Y' : Matrix (Fin 2) (Fin 2) F) :
    swapPairMat X Y * swapPairMat X' Y' = swapPairMat (X * X') (Y * Y') := by
  rw [swapPairMat, swapPairMat, submatrix_mul_equiv, fromBlocks_multiply, swapPairMat]
  simp

theorem det_swapPairMat (X Y : Matrix (Fin 2) (Fin 2) F) :
    (swapPairMat X Y).det = X.det * Y.det := by
  rw [swapPairMat, det_submatrix_equiv_self, det_fromBlocks_zero₂₁]

theorem swapPairMat_transpose (X Y : Matrix (Fin 2) (Fin 2) F) :
    (swapPairMat X Y)ᵀ = swapPairMat Xᵀ Yᵀ := by
  rw [swapPairMat, swapPairMat, transpose_submatrix, fromBlocks_transpose]
  simp

@[expose] noncomputable def swapPairSL :
    SL(2, F) × SL(2, F) →* SpecialLinearGroup (Fin (2 * 2)) F where
  toFun p := ⟨swapPairMat (p.1 : Matrix (Fin 2) (Fin 2) F)
      ((p.2⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ, by
    rw [det_swapPairMat, det_transpose, p.1.2, (p.2⁻¹).2, one_mul]⟩
  map_one' := by
    apply Subtype.ext
    change swapPairMat ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
      (((1 : SL(2, F))⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ = 1
    simp only [inv_one, Matrix.SpecialLinearGroup.coe_one, transpose_one, swapPairMat,
      fromBlocks_one, submatrix_one_equiv]
  map_mul' p q := by
    apply Subtype.ext
    change swapPairMat ((p.1 * q.1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
      (((p.2 * q.2)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ =
      swapPairMat (p.1 : Matrix (Fin 2) (Fin 2) F)
          ((p.2⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ *
        swapPairMat (q.1 : Matrix (Fin 2) (Fin 2) F)
          ((q.2⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ
    rw [swapPairMat_mul, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, transpose_mul]

theorem coe_swapPairSL (p : SL(2, F) × SL(2, F)) :
    ((swapPairSL p : SpecialLinearGroup (Fin (2 * 2)) F) : Matrix (Fin (2 * 2)) (Fin (2 * 2)) F) =
      swapPairMat (p.1 : Matrix (Fin 2) (Fin 2) F)
        ((p.2⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ :=
  rfl

theorem blockSwapJ_four_eq :
    (UnitaryHigher.blockSwapJ (2 * 2) 2 : Matrix (Fin (2 * 2)) (Fin (2 * 2)) F) =
      (Matrix.fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).submatrix
        (spModelIdx 2).symm (spModelIdx 2).symm := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem blockSwapJ_mul_swapPairMat_mul (P Q : Matrix (Fin 2) (Fin 2) F) :
    (UnitaryHigher.blockSwapJ (2 * 2) 2 : Matrix (Fin (2 * 2)) (Fin (2 * 2)) F) * swapPairMat P Q *
      UnitaryHigher.blockSwapJ (2 * 2) 2 = swapPairMat Q P := by
  rw [blockSwapJ_four_eq, swapPairMat, submatrix_mul_equiv, submatrix_mul_equiv,
    fromBlocks_multiply, fromBlocks_multiply, swapPairMat]
  simp

end SwapModel

section TauBlock

variable {K : Type} [Field K] [CharP K 2] {F : Type} [Field F] [CharP F 2]

omit [CharP K 2] in
theorem coe_longBlock_two_one (A : SL(2, K)) :
    (((longBlock K 2 1 A : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      CFSG.LieType.Steinberg.Sp.blockMat (Sum.inl 1) (Sum.inr 1)
        (A : Matrix (Fin 2) (Fin 2) K) :=
  mat_longBlock 1 A

theorem coe_tauSp_longBlock_one (A : SL(2, K)) :
    (((tauSp (longBlock K 2 1 A) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.fromBlocks (A : Matrix (Fin 2) (Fin 2) K) 0 0
        ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  rw [CFSG.QuasithinUnique.Lin2.Five.coe_tauSp, coe_longBlock_two_one,
    Matrix.SpecialLinearGroup.SL2_inv_expl]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hneg : ∀ x : K, -x = x := fun x => by
    rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
  ext r c
  rw [CFSG.QuasithinUnique.Lin2.Five.tauMat_apply]
  fin_cases r <;> fin_cases c <;>
    simp [CFSG.QuasithinUnique.Lin2.Five.tauPair, CFSG.LieType.Steinberg.Sp.blockMat,
      Matrix.fromBlocks, hneg, mul_comm] <;> rfl

theorem spModelSL_statedSpMap_tauSp_longBlock_one (σ : K →+* F) (A : SL(2, K)) :
    spModelSL 2 F (statedSpMap σ 2 (tauSp (longBlock K 2 1 A))) =
      swapPairSL (SpecialLinearGroup.map σ A, SpecialLinearGroup.map σ A) := by
  apply Subtype.ext
  rw [coe_spModelSL, coe_statedSpMap, F4Pilot.coe_map_GL, coe_tauSp_longBlock_one,
    coe_swapPairSL, swapPairMat, fromBlocks_map, Matrix.map_zero _ (map_zero σ)]
  have h1 : (((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ).map σ =
      (((SpecialLinearGroup.map σ A)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
    rw [← map_inv, transpose_map]
    rfl
  rw [h1]
  rfl

theorem slFourEquivProj_symm_graph_swapPairSL (p : SL(2, F) × SL(2, F)) :
    (slFourEquivProj F).symm
        ((conjAut (2 * 2) F (spBlockSwapGL 2 F) * dualAut (2 * 2) F)
          (proj (2 * 2) F (swapPairSL p))) = swapPairSL p.swap := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj, slFourEquivProj_symm_proj]
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose, ← map_inv, coe_swapPairSL,
    coe_swapPairSL, swapPairMat_transpose, coe_spBlockSwapGL]
  have hJinv : (((spBlockSwapGL 2 F)⁻¹ : GL (Fin (2 * 2)) F) :
      Matrix (Fin (2 * 2)) (Fin (2 * 2)) F) = UnitaryHigher.blockSwapJ (2 * 2) 2 := by
    rw [inv_eq_of_mul_eq_one_right spBlockSwapGL_mul_self, coe_spBlockSwapGL]
  rw [hJinv, blockSwapJ_mul_swapPairMat_mul]
  simp

end TauBlock

section SwapRange

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem swapPairSL_fst_mem (X : SL(2, F)) :
    swapPairSL (X, 1) ∈ blockSpecialLinear (K := F) (twBlockSL 0) := by
  intro i j hij
  rw [coe_swapPairSL]
  simp only [inv_one, Matrix.SpecialLinearGroup.coe_one, transpose_one]
  fin_cases i <;> fin_cases j <;> simp_all [twBlockSL, swapPairMat, Matrix.fromBlocks] <;> rfl

omit [Finite F] in
theorem swapPairSL_snd_mem (Y : SL(2, F)) :
    swapPairSL (1, Y) ∈ blockSpecialLinear (K := F) (twBlockSL 0)ᶜ := by
  intro i j hij
  rw [coe_swapPairSL]
  simp only [Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp_all [twBlockSL, swapPairMat, Matrix.fromBlocks] <;> rfl

omit [Finite F] in
theorem swapPairSL_injective : Function.Injective (swapPairSL (F := F)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨X, Y⟩ h
  have h1 := congrArg (fun M : SpecialLinearGroup (Fin (2 * 2)) F =>
    (M : Matrix (Fin (2 * 2)) (Fin (2 * 2)) F).submatrix (spModelIdx 2) (spModelIdx 2)) h
  simp only [coe_swapPairSL, swapPairMat, submatrix_submatrix, Equiv.symm_comp_self,
    submatrix_id_id, Matrix.SpecialLinearGroup.coe_one] at h1
  rw [submatrix_one_equiv, ← fromBlocks_one, fromBlocks_inj] at h1
  obtain ⟨hX, -, -, hY⟩ := h1
  have hY' : ((Y⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← transpose_one, ← hY, transpose_transpose]
  have hX1 : X = 1 := Subtype.ext hX
  have hY1 : Y = 1 := inv_eq_one.1 (Subtype.ext hY')
  rw [hX1, hY1]
  rfl

theorem range_swapPairSL :
    (swapPairSL (F := F)).range =
      blockSpecialLinear (K := F) (twBlockSL 0) ⊔ blockSpecialLinear (K := F) (twBlockSL 0)ᶜ := by
  have hle : (swapPairSL (F := F)).range ≤
      blockSpecialLinear (K := F) (twBlockSL 0) ⊔ blockSpecialLinear (K := F) (twBlockSL 0)ᶜ := by
    rintro _ ⟨⟨X, Y⟩, rfl⟩
    have h : swapPairSL (X, Y) = swapPairSL (X, 1) * swapPairSL (1, Y) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    rw [h]
    exact mul_mem (mem_sup_left (swapPairSL_fst_mem X)) (mem_sup_right (swapPairSL_snd_mem Y))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [natCard_sup_twBlock, ← Nat.card_prod,
    Nat.card_congr (MonoidHom.ofInjective swapPairSL_injective).toEquiv]

end SwapRange

end CFSG.SeitzReduction.SymplecticPilot
