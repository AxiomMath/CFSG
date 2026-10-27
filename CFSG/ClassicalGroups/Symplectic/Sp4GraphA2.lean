module

public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticLagrangian

public section

namespace CFSG.ClassicalGroups.Symplectic

open Matrix CFSG.Open CFSG.QuasithinUnique.Lin2.Five
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp coe_upperUnipotentSp)

section Rank

variable {F : Type} [Field F]

private theorem rank_single_eq_one {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (i : m) (j : n) {c : F} (hc : c ≠ 0) :
    (Matrix.single i j c : Matrix m n F).rank = 1 := by
  apply le_antisymm
  · have e : (Matrix.single i j c : Matrix m n F) =
        vecMulVec (Pi.single i c) (Pi.single j 1) := by
      ext a b
      rw [Matrix.single_apply, vecMulVec_apply]
      by_cases ha : i = a <;> by_cases hb : j = b
      · subst ha; subst hb; simp
      · subst ha; simp [Ne.symm hb, hb]
      · simp [Pi.single_apply, Ne.symm ha, ha]
      · simp [Pi.single_apply, Ne.symm ha, ha]
    rw [e]
    exact rank_vecMulVec_le _ _
  · rw [Matrix.rank_eq_finrank_span_cols]
    have hcol : (Matrix.single i j c : Matrix m n F).col j ≠ 0 := fun h => by
      have := congrFun h i
      simp at this
      exact hc this
    have hmem : (Matrix.single i j c : Matrix m n F).col j ∈
        Submodule.span F (Set.range (Matrix.single i j c : Matrix m n F).col) :=
      Submodule.subset_span ⟨j, rfl⟩
    exact Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨_, hmem⟩, fun h => hcol (congrArg Subtype.val h)⟩

theorem rank_sub_one_le_two_of_mul_self_eq_one [CharP F 2]
    {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (h : A * A = 1) : (A - 1).rank ≤ 2 := by
  have hN : (A - 1) * (A - 1) = 0 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have e : (A - 1) * (A - 1) = (A * A - 1) + (2 : F) • (1 - A) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_one]
      module
    rw [e, h, h2, zero_smul, sub_self, add_zero]
  have := Matrix.rank_add_rank_le_card_of_mul_eq_zero hN
  simp at this
  omega

end Rank

section Block

variable {F : Type} [Field F]

theorem tauMat_fromBlocks_sub_one (S : Matrix (Fin 2) (Fin 2) F)
    (h00 : S 0 0 = 0) (h11 : S 1 1 = 0) :
    tauMat (fromBlocks 1 S 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) - 1 =
      Matrix.single (Sum.inl 0) (Sum.inr 0) (-(S 0 1 * S 1 0)) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [tauMat, tauPair, h00, h11]

private theorem displacement_eq_orthogonal [CharP F 2] {g : StatedSp 2 F} (hg : g * g = 1)
    (hrk : Matrix.rank (spMat g - 1) = 2) :
    displacement g = (pairedSympForm F 2).orthogonal (displacement g) := by
  have hiso := isTotallyIsotropic_displacement hg
  have hle : displacement g ≤ (pairedSympForm F 2).orthogonal (displacement g) :=
    fun w hw n hn => hiso n hn w hw
  have hdim : Module.finrank F (displacement g) = 2 := hrk
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [LinearMap.BilinForm.finrank_orthogonal spForm_nondegenerate, hdim]
  simp

end Block

theorem tauSp_sub_one_rank_eq_one_of_a2 {F : Type} [Field F] [CharP F 2] (g : StatedSp 2 F)
    (hg : g * g = 1)
    (hrk : Matrix.rank
      (((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) - 1) = 2)
    (ha : ∀ v, spForm 2 F v ((((g : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) - 1) *ᵥ v) = 0) :
    Matrix.rank ((((tauSp g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) - 1) = 1 := by
  classical
  have hW := displacement_eq_orthogonal hg hrk
  obtain ⟨h, S, hS, hSu, hgh⟩ :=
    CFSG.SeitzReduction.SymplecticLagrangian.exists_eq_conj_upperUnipotentSp hg hW
  set u : StatedSp 2 F := upperUnipotentSp 2 F hS with hu_def
  have hum : spMat u = fromBlocks 1 S 0 1 := coe_upperUnipotentSp hS
  have hau : ∀ w, spForm 2 F w ((spMat u - 1) *ᵥ w) = 0 := by
    intro w
    have h1 := ha (spMat h *ᵥ w)
    have h2 : (spMat g - 1) *ᵥ (spMat h *ᵥ w) = spMat h *ᵥ ((spMat u - 1) *ᵥ w) := by
      rw [sub_one_mulVec, sub_one_mulVec, hgh, spMat_mul_mulVec, spMat_mul_mulVec,
        spMat_inv_mulVec_mulVec, mulVec_sub]
    rw [h2] at h1
    exact (pairedSympForm_spMat h w _).symm.trans h1
  have hdiag : ∀ i : Fin 2, S i i = 0 := by
    intro i
    have h1 := hau (Pi.single (Sum.inr i) 1)
    rw [spForm_apply, hum] at h1
    simp [spJ_mulVec_inr] at h1
    exact h1
  have hdet : -(S 0 1 * S 1 0) ≠ 0 := by
    have h1 : S.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det S).mp hSu).ne_zero
    rw [Matrix.det_fin_two, hdiag 0, hdiag 1] at h1
    simpa using h1
  have hτ : tauSp g = tauSp h * tauSp u * (tauSp h)⁻¹ := by
    rw [hgh, map_mul, map_mul, map_inv]
  have hTTi : ((tauSp h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *
      (((tauSp h)⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) = 1 := by
    rw [← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  have hTTi' : (((tauSp h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((((tauSp h)⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
    rw [← Units.val_mul, hTTi]
    rfl
  have hconj : (((tauSp g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) - 1 =
      (((tauSp h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((((tauSp u : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) - 1) *
      ((((tauSp h)⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    rw [hτ, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hTTi']
  have hTu : IsUnit (((tauSp h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hTiu : IsUnit ((((tauSp h)⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  rw [hconj, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hTiu,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hTu, coe_tauSp, show
      ((u : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        fromBlocks 1 S 0 1 from hum, tauMat_fromBlocks_sub_one S (hdiag 0) (hdiag 1)]
  exact rank_single_eq_one _ _ hdet

end CFSG.ClassicalGroups.Symplectic
