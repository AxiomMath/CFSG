module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Base

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.GLS.Stage2.Bender.Thm1

section Lift

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def suTwist (M : U3U h) (σ : K ≃+* K) :
    gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≃*
      gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  (primeFormConjSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M⁻¹).trans
    ((primeFormFieldSU h (isPrimeFormGram_one (n := 3)) σ).trans
      (primeFormConjSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M))

theorem coe_suTwist (M : U3U h) (σ : K ≃+* K)
    (s : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    ((suTwist h M σ s : gramSU h _) : GL (Fin 3) K) =
      (M : GL (Fin 3) K) * GeneralLinearGroup.map (σ : K →+* K)
        ((M : GL (Fin 3) K)⁻¹ * (s : GL (Fin 3) K) * (M : GL (Fin 3) K)) *
          (M : GL (Fin 3) K)⁻¹ := by
  change (M : GL (Fin 3) K) * glAut σ ((M : GL (Fin 3) K)⁻¹ * (s : GL (Fin 3) K) *
    (M : GL (Fin 3) K)⁻¹⁻¹) * (M : GL (Fin 3) K)⁻¹ = _
  rw [inv_inv]
  rfl

theorem mk_suTwist (M : U3U h) (σ : K ≃+* K)
    (s : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    (QuotientGroup.mk (suTwist h M σ s) : U3T h) =
      (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M *
        primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ *
        (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M)⁻¹)
        (QuotientGroup.mk s : U3T h) := by
  rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply]
  change _ = primeFormConjAut h _ M (primeFormFieldAut h _ σ (primeFormConjAut h _ M⁻¹
    (s : primeFormP h _)))
  rw [primeFormConjAut_mk, primeFormFieldAut_mk, primeFormConjAut_mk]
  rfl

theorem lift_eq_suTwist {K' : Type} [Group K'] [Group.IsPerfect K'] (M : U3U h) (σ : K ≃+* K)
    (e : K' ≃* gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (ψ : MulAut K')
    (α : MulAut (U3T h))
    (hα : α = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M *
        primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ *
        (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M)⁻¹)
    (hψ : ∀ x : K', (QuotientGroup.mk (e (ψ x)) : U3T h) = α (QuotientGroup.mk (e x) : U3T h)) :
    ∀ x : K', ((e (ψ x) : gramSU h _) : GL (Fin 3) K) =
      (M : GL (Fin 3) K) * GeneralLinearGroup.map (σ : K →+* K)
        ((M : GL (Fin 3) K)⁻¹ * ((e x : gramSU h _) : GL (Fin 3) K) * (M : GL (Fin 3) K)) *
          (M : GL (Fin 3) K)⁻¹ := by
  have : Group.IsPerfect (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let T := suTwist h M σ
  let Ψ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≃*
      gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    MulEquiv.trans e.symm (MulEquiv.trans ψ e)
  have hT : ∀ s, (QuotientGroup.mk (T s) : U3T h) = α (QuotientGroup.mk s : U3T h) := by
    intro s
    rw [hα]
    exact mk_suTwist h M σ s
  have hΨ : ∀ s, (QuotientGroup.mk (Ψ s) : U3T h) = α (QuotientGroup.mk s : U3T h) := by
    intro s
    have := hψ (e.symm s)
    rwa [MulEquiv.apply_symm_apply] at this
  have hTs : ∀ t, (QuotientGroup.mk (T.symm t) : U3T h) = α.symm (QuotientGroup.mk t : U3T h) := by
    intro t
    refine ((MulEquiv.symm_apply_eq α).2 ?_).symm
    rw [← hT, MulEquiv.apply_symm_apply]
  have hcentral : ∀ s, s⁻¹ * (T.symm.toMonoidHom.comp Ψ.toMonoidHom) s ∈
      Subgroup.center (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    intro s
    refine normOneScalars_le_center h _ 3 ?_
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change (QuotientGroup.mk s : U3T h)⁻¹ * (QuotientGroup.mk (T.symm (Ψ s)) : U3T h) = 1
    rw [hTs, hΨ, MulEquiv.symm_apply_apply, inv_mul_cancel]
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    (T.symm.toMonoidHom.comp Ψ.toMonoidHom) hcentral
  intro x
  have h1 : Ψ (e x) = T (e x) := by
    have := congrArg (fun g => g (e x)) hid
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply] at this
    exact (T.symm_apply_eq.1 this)
  have h2 : Ψ (e x) = e (ψ x) := by
    simp [Ψ]
  rw [← h2, h1, coe_suTwist]

end Lift

end CFSG.HardMathSupport.Solomon.Coordinator
