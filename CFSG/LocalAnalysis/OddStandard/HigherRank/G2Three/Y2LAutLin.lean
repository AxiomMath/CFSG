module

public import CFSG.LocalAnalysis.SteinbergBVGL3InvolutionDimensionBound

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup Matrix CFSG.LocalAnalysis.SteinbergBV.ThreeInvolutions

@[expose] def y2l_matAut : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative (Fin 3 → ZMod 2)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.toAdd)
      invFun := fun v => Multiplicative.ofAdd
        (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.toAdd)
      left_inv := fun v => by simp [Matrix.mulVec_mulVec]
      right_inv := fun v => by simp [Matrix.mulVec_mulVec]
      map_mul' := fun v w => by simp [Matrix.mulVec_add] }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Matrix.mulVec_mulVec]

theorem y2l_matAut_apply (g : GL (Fin 3) (ZMod 2)) (v : Multiplicative (Fin 3 → ZMod 2)) :
    y2l_matAut g v = Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.toAdd) :=
  rfl

theorem y2l_matAut_injective : Function.Injective y2l_matAut := by
  intro g h hgh
  have hv : ∀ v : Fin 3 → ZMod 2, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v =
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v := fun v => by
    have := congrArg (fun φ : MulAut (Multiplicative (Fin 3 → ZMod 2)) =>
      (φ (Multiplicative.ofAdd v)).toAdd) hgh
    simpa [y2l_matAut_apply] using this
  exact Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => by
    simpa [Matrix.toLin'_apply] using hv v))

variable {M : Type} [Group M] (eM : M ≃* (Fin 3 → Multiplicative (ZMod 2)))

@[expose] def y2l_toW : M ≃* Multiplicative (Fin 3 → ZMod 2) :=
  eM.trans (MulEquiv.funMultiplicative (Fin 3) (ZMod 2)).symm

@[expose] def y2l_psiAut : GL (Fin 3) (ZMod 2) →* MulAut M :=
  (MulAut.congr (y2l_toW eM).symm).toMonoidHom.comp y2l_matAut

theorem y2l_toW_psiAut (g : GL (Fin 3) (ZMod 2)) (m : M) :
    (y2l_toW eM (y2l_psiAut eM g m)).toAdd =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (y2l_toW eM m).toAdd := by
  simp [y2l_psiAut, MulAut.congr_apply, y2l_matAut_apply]

theorem y2l_psiAut_injective : Function.Injective (y2l_psiAut eM) :=
  (MulAut.congr (y2l_toW eM).symm).injective.comp y2l_matAut_injective

theorem y2l_card_GL : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem y2l_closure_T01_pGL :
    Subgroup.closure ({T01, pGL} : Set (GL (Fin 3) (ZMod 2))) = ⊤ := by
  set H := Subgroup.closure ({T01, pGL} : Set (GL (Fin 3) (ZMod 2)))
  have h1 : T01 ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hp : pGL ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have h2 : T12 ∈ H := by
    rw [← pGL_conj_T01]
    exact mul_mem (mul_mem hp h1) (inv_mem hp)
  have h3 : T20 ∈ H := by
    rw [← pGL_conj_T12]
    exact mul_mem (mul_mem hp h2) (inv_mem hp)
  rw [eq_top_iff, ← closure_tGL_eq_top, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem y2l_psiAut_range (h168 : Nat.card (MulAut M) = 168) : (y2l_psiAut eM).range = ⊤ := by
  haveI : Finite (MulAut M) := Nat.finite_of_card_ne_zero (by rw [h168]; norm_num)
  apply Subgroup.eq_top_of_card_eq
  rw [h168, ← y2l_card_GL]
  exact (Nat.card_congr (MonoidHom.ofInjective (y2l_psiAut_injective eM)).toEquiv).symm

theorem y2l_closure_psiAut (h168 : Nat.card (MulAut M) = 168) :
    Subgroup.closure ({y2l_psiAut eM T01, y2l_psiAut eM pGL} : Set (MulAut M)) = ⊤ := by
  rw [← y2l_psiAut_range eM h168, MonoidHom.range_eq_map, ← y2l_closure_T01_pGL,
    MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]

@[expose] def y2l_coc (A : Fin 2 → Matrix (Fin 3) (Fin 3) (ZMod 2)) (d : Fin 2 → Fin 3 → ZMod 2) :
    List (Fin 2) → Fin 3 → ZMod 2
  | [] => 0
  | l :: w => d l + A l *ᵥ y2l_coc A d w

@[expose] def y2l_cocSet : Finset ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) :=
  Finset.univ.filter fun p =>
    y2l_coc ![t01, pMat] ![p.1, p.2] [0, 0] = 0 ∧ y2l_coc ![t01, pMat] ![p.1, p.2] [1, 1, 1] = 0

theorem y2l_mem_cocSet {p : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)} :
    p ∈ y2l_cocSet ↔ y2l_coc ![t01, pMat] ![p.1, p.2] [0, 0] = 0 ∧
      y2l_coc ![t01, pMat] ![p.1, p.2] [1, 1, 1] = 0 := by
  rw [y2l_cocSet, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem y2l_card_cocSet : y2l_cocSet.card = 16 := by
  decide

theorem y2l_fixed_zero : ∀ v : Fin 3 → ZMod 2, t01 *ᵥ v = v → pMat *ᵥ v = v → v = 0 := by
  decide

theorem y2l_T01_sq : T01 * T01 = 1 :=
  Units.ext (by change t01 * t01 = 1; decide)

theorem y2l_pGL_cube : pGL * pGL * pGL = 1 :=
  Units.ext (by change pMat * pMat * pMat = 1; decide)

end CFSG.OddStandard.HigherRank.G2Three.Sec2
