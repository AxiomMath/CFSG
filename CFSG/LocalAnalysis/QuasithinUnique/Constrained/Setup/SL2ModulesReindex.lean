module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

section Reindex

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

theorem tmatE_reindex (σ : ι ≃ ι') (e : ι → ℕ) (e' : ι' → ℕ) (he : ∀ i, e' (σ i) = e i)
    (g : SL(2, F)) (y' y : ι' → Fin 2) :
    tmatE k e' g y' y = tmatE k e g (y' ∘ σ) (y ∘ σ) := by
  unfold tmatE
  rw [← Equiv.prod_comp σ]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [he]

variable [DecidableEq ι] [DecidableEq ι']

@[expose] def reindexEquiv (σ : ι ≃ ι') (e : ι → ℕ) (e' : ι' → ℕ) (he : ∀ i, e' (σ i) = e i) :
    (tensorRep F k e).Equiv (tensorRep F k e') :=
  Representation.Equiv.mk
    (LinearEquiv.funCongrLeft k k (Equiv.arrowCongr σ (Equiv.refl (Fin 2))).symm)
    (fun g => by
      refine LinearMap.ext fun f => funext fun y => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
        LinearMap.funLeft_apply, tensorRep_apply]
      refine (Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin 2))).symm _ _ fun y' => ?_).symm
      rw [tmatE_reindex σ e e' he]
      rfl)


end Reindex

section OptionSplit

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
@[expose] def optCons (a : Fin 2) (y : ι → Fin 2) : Option ι → Fin 2 := fun o => o.elim a y

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem optCons_none (a : Fin 2) (y : ι → Fin 2) : optCons a y none = a := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem optCons_some (a : Fin 2) (y : ι → Fin 2) (i : ι) : optCons a y (some i) = y i := rfl

omit [Fintype ι] [DecidableEq ι] in
@[expose] def optConsEquiv : Fin 2 × (ι → Fin 2) ≃ (Option ι → Fin 2) where
  toFun p := optCons p.1 p.2
  invFun x := (x none, fun i => x (some i))
  left_inv p := by rcases p with ⟨a, y⟩; rfl
  right_inv x := by funext o; cases o <;> rfl

theorem sum_option_pi {M : Type*} [AddCommMonoid M] (φ : (Option ι → Fin 2) → M) :
    ∑ x, φ x = ∑ a : Fin 2, ∑ y : ι → Fin 2, φ (optCons a y) := by
  rw [← Fintype.sum_equiv optConsEquiv (fun p => φ (optCons p.1 p.2)) φ (fun p => rfl),
    Fintype.sum_prod_type]

omit [DecidableEq ι] in
theorem tmatE_option (e : Option ι → ℕ) (g : SL(2, F)) (x' x : Option ι → Fin 2) :
    tmatE k e g x' x = twistMat k (e none) g (x' none) (x none) *
      tmatE k (fun i => e (some i)) g (fun i => x' (some i)) (fun i => x (some i)) := by
  unfold tmatE
  rw [Fintype.prod_option]

theorem tensorRep_option_apply (e : Option ι → ℕ) (g : SL(2, F)) (f : (Option ι → Fin 2) → k)
    (a' : Fin 2) (y' : ι → Fin 2) :
    tensorRep F k e g f (optCons a' y') = ∑ a : Fin 2, twistMat k (e none) g a' a *
      tensorRep F k (fun i => e (some i)) g (fun y => f (optCons a y)) y' := by
  rw [tensorRep_apply, sum_option_pi]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tensorRep_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [tmatE_option]
  simp only [optCons_none, optCons_some]
  ring

end OptionSplit

end CFSG.QuasithinUnique.Setup.SL2Modules
