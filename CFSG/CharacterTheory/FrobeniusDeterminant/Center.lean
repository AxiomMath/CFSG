module

public import CFSG.CharacterTheory.FrobeniusDeterminant.Defs
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG

open MvPolynomial Matrix

namespace FrobeniusDeterminant.Center

variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]

private theorem coeff_conj_eq_of_mem_center
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (a b : G) :
    z.1.coeff (a * b * a⁻¹) = z.1.coeff b := by
  have h := (Subalgebra.mem_center_iff.mp z.2) (MonoidAlgebra.single a (1 : ℂ))
  have h' := congrArg (fun q : MonoidAlgebra ℂ G => q.coeff (a * b)) h
  rw [MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply] at h'
  simpa [mul_assoc] using h'.symm

private theorem mem_center_of_coeff_conj_eq (z : MonoidAlgebra ℂ G)
    (hz : ∀ a b : G, z.coeff (a * b * a⁻¹) = z.coeff b) :
    z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
  rw [Subalgebra.mem_center_iff]
  intro y
  refine MonoidAlgebra.induction_linear y ?_ ?_ ?_
  · simp
  · intro x y hx hy
    rw [add_mul, mul_add, hx, hy]
  · intro a r
    ext g
    rw [MonoidAlgebra.coeff_single_mul_apply,
      MonoidAlgebra.coeff_mul_single_apply]
    have h := hz a (a⁻¹ * g)
    have h' : z.coeff (g * a⁻¹) = z.coeff (a⁻¹ * g) := by
      simpa [mul_assoc] using h
    rw [h']
    ring

@[expose] noncomputable def representative (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.exists_rep c)

private theorem mk_representative (c : ConjClasses G) :
    ConjClasses.mk (representative G c) = c :=
  Classical.choose_spec (ConjClasses.exists_rep c)

private theorem coeff_eq_of_mk_eq (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G))
    {a b : G} (h : ConjClasses.mk a = ConjClasses.mk b) :
    z.1.coeff a = z.1.coeff b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h)
  rw [← hc]
  exact (coeff_conj_eq_of_mem_center G z c a).symm

private noncomputable def classFunctionAlgebra (f : ConjClasses G → ℂ) :
    MonoidAlgebra ℂ G :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm
    (Finsupp.equivFunOnFinite.symm (fun g : G => f (ConjClasses.mk g)) : G →₀ ℂ)

@[simp] private theorem classFunctionAlgebra_coeff (f : ConjClasses G → ℂ) (g : G) :
    (classFunctionAlgebra G f).coeff g = f (ConjClasses.mk g) := by
  unfold classFunctionAlgebra
  rw [MonoidAlgebra.coeffLinearEquiv_symm_apply,
    MonoidAlgebra.coeff_ofCoeff]
  have h := congrFun
    ((Finsupp.equivFunOnFinite : (G →₀ ℂ) ≃ (G → ℂ)).apply_symm_apply
      (fun g : G => f (ConjClasses.mk g))) g
  simpa only [Finsupp.equivFunOnFinite_apply] using h

private theorem classFunctionAlgebra_mem_center (f : ConjClasses G → ℂ) :
    classFunctionAlgebra G f ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
  apply mem_center_of_coeff_conj_eq
  intro a b
  rw [classFunctionAlgebra_coeff, classFunctionAlgebra_coeff]
  congr 1
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  apply isConj_iff.mpr
  refine ⟨a⁻¹, ?_⟩
  simp [mul_assoc]

noncomputable def classFunctionCenter :
    (ConjClasses G → ℂ) →ₗ[ℂ] Subalgebra.center ℂ (MonoidAlgebra ℂ G) where
  toFun f := ⟨classFunctionAlgebra G f, classFunctionAlgebra_mem_center G f⟩
  map_add' f h := by
    apply Subtype.ext
    ext g
    simp
  map_smul' c f := by
    apply Subtype.ext
    ext g
    simp

noncomputable def centerCoeff :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₗ[ℂ] (ConjClasses G → ℂ) where
  toFun z c := z.1.coeff (representative G c)
  map_add' x y := by
    ext c
    simp
  map_smul' c x := by
    ext d
    simp

theorem centerCoeff_classFunctionCenter (f : ConjClasses G → ℂ) :
    centerCoeff G (classFunctionCenter G f) = f := by
  ext c
  change (classFunctionAlgebra G f).coeff (representative G c) = f c
  rw [classFunctionAlgebra_coeff]
  simp [mk_representative]

theorem classFunctionCenter_centerCoeff
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :
    classFunctionCenter G (centerCoeff G z) = z := by
  apply Subtype.ext
  ext g
  change (classFunctionAlgebra G (centerCoeff G z)).coeff g = z.1.coeff g
  rw [classFunctionAlgebra_coeff]
  change z.1.coeff (representative G (ConjClasses.mk g)) = z.1.coeff g
  exact coeff_eq_of_mk_eq G z (mk_representative G (ConjClasses.mk g))

noncomputable def centerCoeffEquiv :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) ≃ₗ[ℂ] (ConjClasses G → ℂ) :=
  { toLinearMap := centerCoeff G
    invFun := classFunctionCenter G
    left_inv := classFunctionCenter_centerCoeff G
    right_inv := centerCoeff_classFunctionCenter G }

theorem finrank_center_eq_card_conjClasses :
    Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) =
      Nat.card (ConjClasses G) := by
  rw [LinearEquiv.finrank_eq (centerCoeffEquiv G)]
  rw [Module.finrank_fintype_fun_eq_card]
  exact (Nat.card_eq_fintype_card :
    Nat.card (ConjClasses G) = Fintype.card (ConjClasses G)).symm

end FrobeniusDeterminant.Center

end CFSG
