module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBFixed

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.ComponentClassification

theorem exists_mulEquiv_psl_of_lieModel {X : Type} [Group X] {n p f : ℕ}
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL n p f)
    (hm : CFSG.Blueprint.LieModel X .PSL n p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K) := by
  have hn : 2 ≤ n := hadm.2.2.1
  rcases hm with ⟨-, h⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    exact ⟨K, inferInstance, inferInstance, hK,
      ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm⟩⟩
  all_goals omega

open Matrix in
theorem exists_semilinearAction_of_psl_two {K : Type} [Field K] [Finite K]
    (α : MulAut (ProjectiveSpecialLinearGroup (Fin 2) K)) :
    ∃ (A : GeneralLinearGroup (Fin 2) K) (σ : K ≃+* K),
      α = CatalogueBLinearSemilinear.semilinearAction 2 K A σ := by
  obtain ⟨x, rfl⟩ := CatalogueSchreierLinearTwo.semilinearAction_surjective K α
  obtain ⟨g, σ, rfl⟩ : ∃ g σ, x = SemidirectProduct.inl g * SemidirectProduct.inr σ :=
    ⟨x.left, x.right, (SemidirectProduct.inl_left_mul_inr_right x).symm⟩
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  refine ⟨A, σ, ?_⟩
  rw [map_mul, CatalogueSchreierLinearTwo.semilinearAction_inl,
    CatalogueSchreierLinearTwo.semilinearAction_inr]
  refine congrArg₂ (· * ·) (MulEquiv.ext fun y => ?_) (MulEquiv.ext fun y => ?_)
  · apply ProjectiveSpecialLinearGroup.toPGL_injective
    change ProjectiveSpecialLinearGroup.toPGL
        (CatalogueSchreierLinearTwo.pglAction K (ProjGenLinGroup.mk A) y) =
      ProjectiveSpecialLinearGroup.toPGL (CatalogueBHigherLinearAction.pglAction 2 K
        (ProjGenLinGroup.mk A) y)
    rw [CatalogueSchreierLinearTwo.toPGL_pglAction, CatalogueBHigherLinearAction.toPGL_pglAction]
  · obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective y
    change GorensteinWalter.psl2RingEquiv σ (QuotientGroup.mk' _ B) = _
    rw [GorensteinWalter.psl2RingEquiv_mk, CatalogueBHigherLinearField.pslFieldAut_mk]
    rfl

theorem bTwo_psl {X : Type} [Group X] [Finite X] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL n p f)
    (hm : CFSG.Blueprint.LieModel X .PSL n p f) (hZ : Subgroup.center X = ⊥) {z : X}
    (hz : orderOf z = 2) : BTwo X z := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_psl_of_lieModel hadm hm
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hodd : Odd (Nat.card K) := hK ▸ hpodd.pow
  have hchar : ringChar K ≠ 2 :=
    CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  have hord : orderOf (MulAut.conj z : MulAut X) = 2 := orderOf_conj_eq_two hZ hz
  have hne : (MulAut.conj z : MulAut X) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    omega
  have hsq : (MulAut.conj z : MulAut X) ^ 2 = 1 := hord ▸ pow_orderOf_eq_one _
  have hn : 2 ≤ n := hadm.2.2.1
  intro S hS
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · have h5 : 5 ≤ Nat.card K := by
      rw [hK]
      by_contra hlt
      have h3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega)
        (Nat.le_self_pow (by have := hadm.2.1; omega) p)
      obtain ⟨k, hk⟩ := hpodd.pow (n := f)
      exact hadm.2.2.2.2 (by simp only [Prod.mk.injEq, true_and]; omega)
    obtain ⟨A, σ, hAσ⟩ :=
      exists_semilinearAction_of_psl_two (MulAut.congr e (MulAut.conj z))
    obtain ⟨hne', hsq'⟩ := CatalogueBLinearHigherB.congr_involution e hne hsq
    rw [hAσ] at hne' hsq'
    exact CatalogueBLinearHigherB.fixed_pComponent_quasisimple_of_congr e hAσ 2
      (CatalogueBLinearSemilinear.odd_linear_semilinear_involution_fixed_p_components 2 K le_rfl
        hodd (Or.inr h5) A σ hne' hsq' 2 Nat.prime_two) S hS
  · let e' := e.trans (CatalogueBLinearHigherB.nativeEquiv n K).symm
    obtain ⟨hne', hsq'⟩ := CatalogueBLinearHigherB.congr_involution e' hne hsq
    exact CatalogueBLinearHigherB.fixed_pComponent_quasisimple_of_congr e' rfl 2
      (CatalogueBLinearHigherB.odd_higher_linear_involution_fixed_p_components n K hchar hn3 _
        hne' hsq' 2 Nat.prime_two) S hS

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
