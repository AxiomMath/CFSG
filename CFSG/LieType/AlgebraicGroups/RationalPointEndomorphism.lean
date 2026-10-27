module

public import Mathlib.FieldTheory.AxGrothendieck

public noncomputable section
open Function
namespace CFSG.LieType.AlgebraicGroups.RationalPoints
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

theorem surjective_comp_of_injective
    (σ : A →ₐ[k] A)
    (hσ : Function.Injective (fun p : A →ₐ[k] k => p.comp σ)) :
    Function.Surjective (fun p : A →ₐ[k] k => p.comp σ) := by
  classical
  obtain ⟨n, q, hq⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := k) (S := A)).mp inferInstance
  let I := RingHom.ker q.toRingHom
  let S := MvPolynomial.zeroLocus k I
  let lift (x : S) : A →ₐ[k] k :=
    AlgHom.liftOfSurjective q hq (MvPolynomial.aeval x.val) (fun a ha => by
      rw [RingHom.mem_ker]
      exact x.property a ha)
  have lift_q : ∀ (x : S) (a : MvPolynomial (Fin n) k),
      lift x (q a) = MvPolynomial.eval x.val a := by
    intro x a
    exact AlgHom.liftOfSurjective_apply _ _ _ _ a
  let c (i : Fin n) : MvPolynomial (Fin n) k := Classical.choose (hq (σ (q (MvPolynomial.X i))))
  have hc : ∀ i, q (c i) = σ (q (MvPolynomial.X i)) := fun i => Classical.choose_spec (hq _)
  let F (x : Fin n → k) (i : Fin n) := MvPolynomial.eval x (c i)
  have hmaps : S.MapsTo F S := by
    intro x hx
    let f := lift ⟨x,hx⟩
    have hf : f.comp q = MvPolynomial.aeval x := by
      ext i
      exact lift_q ⟨x,hx⟩ _
    have he : MvPolynomial.aeval (F x) = (f.comp σ).comp q := by
      ext i
      simp only [MvPolynomial.aeval_X, AlgHom.comp_apply, F]
      rw [← hc]
      exact AlgHom.congr_fun hf (c i) |>.symm
    intro a ha
    change MvPolynomial.eval (F x) a = 0
    rw [show MvPolynomial.eval (F x) a = (MvPolynomial.aeval (F x)) a by rfl, he]
    change f (σ (q a)) = 0
    have hqa : q a = 0 := RingHom.mem_ker.mp ha
    rw [hqa, map_zero, map_zero]
  have hinj : S.InjOn F := by
    intro x hx y hy hxy
    have hcomp : (lift ⟨x,hx⟩).comp σ = (lift ⟨y,hy⟩).comp σ := by
      apply (AlgHom.cancel_right hq).1
      ext i
      change lift ⟨x,hx⟩ (σ (q (MvPolynomial.X i))) =
        lift ⟨y,hy⟩ (σ (q (MvPolynomial.X i)))
      rw [← hc i, lift_q, lift_q]
      exact congrFun hxy i
    have hh := hσ hcomp
    funext i
    have h := congrArg (fun f : A →ₐ[k] k => f (q (MvPolynomial.X i))) hh
    simpa only [lift_q, MvPolynomial.eval_X] using h
  have hsurj : S.SurjOn F S := ax_grothendieck_zeroLocus I c hmaps hinj
  intro p
  let y (i : Fin n) := p (q (MvPolynomial.X i))
  have hy : y ∈ S := by
    intro a ha
    have he : p.comp q = MvPolynomial.aeval y := by
      ext i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, y]
    change MvPolynomial.eval y a = 0
    rw [show MvPolynomial.eval y a = (MvPolynomial.aeval y) a by rfl, ← he]
    change p (q a) = 0
    have hqa : q a = 0 := RingHom.mem_ker.mp ha
    rw [hqa, map_zero]
  obtain ⟨x,hx,hxy⟩ := hsurj hy
  refine ⟨lift ⟨x,hx⟩, ?_⟩
  apply (AlgHom.cancel_right hq).1
  ext i
  change lift ⟨x,hx⟩ (σ (q (MvPolynomial.X i))) = p (q (MvPolynomial.X i))
  rw [← hc i, lift_q]
  exact congrFun hxy i

end CFSG.LieType.AlgebraicGroups.RationalPoints
