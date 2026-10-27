module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)

variable {F : Type} [Field F]

theorem ker_proj_eq_center (r : ℕ) : (proj r F).ker = Subgroup.center (StatedSp r F) := by
  rw [ker_proj, CFSG.LieType.Universal.Symplectic.center_eq]

theorem exists_semilinear_lift [Finite F] (hodd : ringChar F ≠ 2) (h4 : 4 ≤ Nat.card F)
    {X : Type} [Group X] (ψ : StatedSp 2 F →* X) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x) (hstab : ∀ x, τ (ψ x) ∈ ψ.range) :
    ∃ (A : gsp 2 F) (σ : F ≃+* F), ∀ x : StatedSp 2 F,
      τ (ψ x) = ψ (conjSp 2 F A (fieldSp 2 F σ x)) := by
  classical
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num)
      (Or.inl (Or.inr h4))).1
  have hmem : ∀ y : X, y ∈ ψ.range → τ y ∈ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact hstab x
  let τC : ψ.range ≃* ψ.range :=
    { toFun := fun y => ⟨τ y, hmem y y.2⟩
      invFun := fun y => ⟨τ y, hmem y y.2⟩
      left_inv := fun y => Subtype.ext (hτ y)
      right_inv := fun y => Subtype.ext (hτ y)
      map_mul' := fun a b => Subtype.ext (map_mul τ (a : X) (b : X)) }
  obtain ⟨β, hβ, -⟩ := exists_mulEquiv_of_central_cover (π := proj 2 F) (proj_surjective)
    (ker_proj_eq_center 2) (θ := ψ.rangeRestrict) ψ.rangeRestrict_surjective
    (by rwa [MonoidHom.ker_rangeRestrict]) τC
  obtain ⟨hall, -, -⟩ := odd_symplectic_automorphism_semilinear_representation (r := 2) hodd le_rfl
  obtain ⟨A, σ, hAσ⟩ := hall β
  refine ⟨A, σ, ?_⟩
  let α : StatedSp 2 F →* StatedSp 2 F :=
    (conjSp 2 F A).toMonoidHom.comp (fieldSp 2 F σ).toMonoidHom
  have hα : ∀ x, proj 2 F (α x) = β (proj 2 F x) := fun x => by
    rw [hAσ, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rfl
  intro x
  have := congrArg Subtype.val (hβ α hα x)
  exact this.symm

end CFSG.ClassicalInvolution.RouteD
