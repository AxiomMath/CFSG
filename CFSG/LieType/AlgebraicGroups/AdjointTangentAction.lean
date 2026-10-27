module

public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramComorphism

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open WithConv

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [HopfAlgebra k A]
  [Algebra.FiniteType k A]

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
theorem comp_innerCo_mem_subgroupPoints {M : Subgroup (WithConv (A →ₐ[k] k))}
    {g : WithConv (A →ₐ[k] k)} (hg : g ∈ M) :
    ∀ y ∈ subgroupPoints M, y.comp (innerCo g) ∈ subgroupPoints M := by
  intro y hy
  rw [subgroupPoints, Set.mem_preimage] at hy ⊢
  have h : toConv (y.comp (innerCo g)) = g * toConv y * g⁻¹ := by
    have := point_comp_innerCo (toConv y) g
    simpa using this
  rw [h]
  exact M.mul_mem (M.mul_mem hg hy) (M.inv_mem hg)

theorem counit_comp_quotientCo_innerCo {M : Subgroup (WithConv (A →ₐ[k] k))}
    {g : WithConv (A →ₐ[k] k)} (hg : g ∈ M) :
    (Bialgebra.counitAlgHom k (A ⧸ subgroupIdeal M)).comp
        (quotientCo M (innerCo g) (comp_innerCo_mem_subgroupPoints hg)) =
      Bialgebra.counitAlgHom k (A ⧸ subgroupIdeal M) := by
  refine Ideal.Quotient.algHom_ext k ?_
  ext a
  simp only [AlgHom.comp_apply]
  have hq : (quotientCo M (innerCo g) (comp_innerCo_mem_subgroupPoints hg))
      (Ideal.Quotient.mkₐ k (subgroupIdeal M) a) =
      Ideal.Quotient.mkₐ k (subgroupIdeal M) (innerCo g a) := rfl
  rw [hq]
  simp only [Bialgebra.counitAlgHom_apply]
  exact congrArg (fun φ : A →ₐ[k] k => φ a) (counit_comp_innerCo g)

@[expose] def adTangent (M : Subgroup (WithConv (A →ₐ[k] k))) {g : WithConv (A →ₐ[k] k)}
    (hg : g ∈ M) :
    Module.End k (TangentSpace k (A ⧸ subgroupIdeal M) (Bialgebra.counitAlgHom k _)) :=
  tangentMap (quotientCo M (innerCo g) (comp_innerCo_mem_subgroupPoints hg))
    (counit_comp_quotientCo_innerCo hg)

theorem adTangent_apply (M : Subgroup (WithConv (A →ₐ[k] k))) {g : WithConv (A →ₐ[k] k)}
    (hg : g ∈ M) (D : TangentSpace k (A ⧸ subgroupIdeal M) (Bialgebra.counitAlgHom k _))
    (a : A) :
    (adTangent M hg D).1 (Ideal.Quotient.mk _ a) = D.1 (Ideal.Quotient.mk _ (innerCo g a)) := by
  rw [adTangent, coe_tangentMap]
  rfl

theorem adTangent_one (M : Subgroup (WithConv (A →ₐ[k] k))) :
    adTangent M (one_mem M) = 1 := by
  refine LinearMap.ext fun D => Subtype.ext (LinearMap.ext fun q => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [adTangent_apply, innerCo_one]
  rfl

theorem adTangent_mul (M : Subgroup (WithConv (A →ₐ[k] k))) {g h : WithConv (A →ₐ[k] k)}
    (hg : g ∈ M) (hh : h ∈ M) :
    adTangent M (mul_mem hg hh) = adTangent M hg * adTangent M hh := by
  refine LinearMap.ext fun D => Subtype.ext (LinearMap.ext fun q => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [Module.End.mul_apply]
  rw [adTangent_apply, adTangent_apply, adTangent_apply, ← innerCo_comp_innerCo g h]
  rfl

theorem adTangent_eq_of_eq (M : Subgroup (WithConv (A →ₐ[k] k)))
    {g h : WithConv (A →ₐ[k] k)} (hgh : g = h) (hg : g ∈ M) (hh : h ∈ M) :
    adTangent M hg = adTangent M hh := by
  subst hgh
  exact congrArg (adTangent M) (Subsingleton.elim hg hh)

theorem adTangent_inv_mul (M : Subgroup (WithConv (A →ₐ[k] k))) {g : WithConv (A →ₐ[k] k)}
    (hg : g ∈ M) :
    adTangent M (M.inv_mem hg) * adTangent M hg = 1 := by
  rw [← adTangent_mul,
    adTangent_eq_of_eq M (inv_mul_cancel g) (M.mul_mem (M.inv_mem hg) hg) (one_mem M),
    adTangent_one]

theorem adTangent_mul_inv (M : Subgroup (WithConv (A →ₐ[k] k))) {g : WithConv (A →ₐ[k] k)}
    (hg : g ∈ M) :
    adTangent M hg * adTangent M (M.inv_mem hg) = 1 := by
  rw [← adTangent_mul,
    adTangent_eq_of_eq M (mul_inv_cancel g) (M.mul_mem hg (M.inv_mem hg)) (one_mem M),
    adTangent_one]

@[expose] def adTangentEquiv (M : Subgroup (WithConv (A →ₐ[k] k))) (g : M) :
    TangentSpace k (A ⧸ subgroupIdeal M) (Bialgebra.counitAlgHom k _) ≃ₗ[k]
      TangentSpace k (A ⧸ subgroupIdeal M) (Bialgebra.counitAlgHom k _) where
  toFun := adTangent M g.2
  invFun := adTangent M (M.inv_mem g.2)
  map_add' := (adTangent M g.2).map_add
  map_smul' := (adTangent M g.2).map_smul
  left_inv D := by
    change (adTangent M (M.inv_mem g.2) * adTangent M g.2) D = D
    rw [adTangent_inv_mul]
    rfl
  right_inv D := by
    change (adTangent M g.2 * adTangent M (M.inv_mem g.2)) D = D
    rw [adTangent_mul_inv]
    rfl

@[simp] theorem adTangentEquiv_apply (M : Subgroup (WithConv (A →ₐ[k] k))) (g : M)
    (D : TangentSpace k (A ⧸ subgroupIdeal M) (Bialgebra.counitAlgHom k _)) :
    adTangentEquiv M g D = adTangent M g.2 D := rfl

@[simp] theorem adTangentEquiv_symm_apply (M : Subgroup (WithConv (A →ₐ[k] k))) (g : M)
    (D : TangentSpace k (A ⧸ subgroupIdeal M) (Bialgebra.counitAlgHom k _)) :
    (adTangentEquiv M g).symm D = adTangent M (M.inv_mem g.2) D := rfl

@[expose] def adTangentHom (M : Subgroup (WithConv (A →ₐ[k] k))) :
    M →* (TangentSpace k (A ⧸ subgroupIdeal M) (Bialgebra.counitAlgHom k _) ≃ₗ[k]
      TangentSpace k (A ⧸ subgroupIdeal M) (Bialgebra.counitAlgHom k _)) where
  toFun := adTangentEquiv M
  map_one' := by
    apply LinearEquiv.ext
    intro D
    change adTangent M (one_mem M) D = D
    rw [adTangent_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro D
    change adTangent M (g * h).2 D = adTangent M g.2 (adTangent M h.2 D)
    rw [adTangent_mul M g.2 h.2]
    rfl

@[simp] theorem adTangentHom_apply (M : Subgroup (WithConv (A →ₐ[k] k))) (g : M)
    (D : TangentSpace k (A ⧸ subgroupIdeal M) (Bialgebra.counitAlgHom k _)) :
    adTangentHom M g D = adTangent M g.2 D := rfl

end CFSG.LieType.AlgebraicGroups

end
