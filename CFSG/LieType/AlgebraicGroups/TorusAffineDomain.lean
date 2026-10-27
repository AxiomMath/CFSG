module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open MvPolynomial

variable (k : Type) [Field k] (a b : ℕ)

@[expose] def torusAffineDet : MvPolynomial (Fin a ⊕ Fin b) k :=
  ∏ i : Fin a, X (Sum.inl i)

abbrev TorusAffine : Type := Localization.Away (torusAffineDet k a b)

theorem torusAffineDet_ne_zero : torusAffineDet k a b ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => X_ne_zero _

instance : IsDomain (TorusAffine k a b) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (torusAffineDet_ne_zero k a b))

example : Algebra.FiniteType k (TorusAffine k a b) := inferInstance

@[expose] def torusCoord (i : Fin a) : TorusAffine k a b :=
  algebraMap (MvPolynomial (Fin a ⊕ Fin b) k) _ (X (Sum.inl i))

@[expose] def affineCoord (j : Fin b) : TorusAffine k a b :=
  algebraMap (MvPolynomial (Fin a ⊕ Fin b) k) _ (X (Sum.inr j))

theorem isUnit_torusCoord (i : Fin a) : IsUnit (torusCoord k a b i) := by
  have h : IsUnit (algebraMap (MvPolynomial (Fin a ⊕ Fin b) k) (TorusAffine k a b)
      (torusAffineDet k a b)) := IsLocalization.Away.algebraMap_isUnit _
  refine isUnit_of_dvd_unit (map_dvd _ ?_) h
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

@[expose] def torusUnit (i : Fin a) : (TorusAffine k a b)ˣ :=
  (isUnit_torusCoord k a b i).unit

theorem coe_torusUnit (i : Fin a) : (torusUnit k a b i : TorusAffine k a b) = torusCoord k a b i :=
  rfl

variable {k a b}

@[expose] def torusAffineEval (t : Fin a → kˣ) (c : Fin b → k) :
    MvPolynomial (Fin a ⊕ Fin b) k →ₐ[k] k :=
  aeval (Sum.elim (fun i => (t i : k)) c)

theorem isUnit_torusAffineEval_det (t : Fin a → kˣ) (c : Fin b → k) :
    IsUnit (torusAffineEval t c (torusAffineDet k a b)) := by
  unfold torusAffineEval torusAffineDet
  rw [map_prod]
  exact IsUnit.prod_univ_iff.2 fun i => by simp

@[expose] def torusAffinePoint (t : Fin a → kˣ) (c : Fin b → k) : TorusAffine k a b →ₐ[k] k :=
  IsLocalization.Away.liftAlgHom (torusAffineDet k a b) (isUnit_torusAffineEval_det t c)

theorem torusAffinePoint_algebraMap (t : Fin a → kˣ) (c : Fin b → k)
    (p : MvPolynomial (Fin a ⊕ Fin b) k) :
    torusAffinePoint t c (algebraMap _ (TorusAffine k a b) p) = torusAffineEval t c p := by
  unfold torusAffinePoint
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

@[simp] theorem torusAffinePoint_torusCoord (t : Fin a → kˣ) (c : Fin b → k) (i : Fin a) :
    torusAffinePoint t c (torusCoord k a b i) = t i := by
  unfold torusCoord
  rw [torusAffinePoint_algebraMap]
  simp [torusAffineEval]

@[simp] theorem torusAffinePoint_affineCoord (t : Fin a → kˣ) (c : Fin b → k) (j : Fin b) :
    torusAffinePoint t c (affineCoord k a b j) = c j := by
  unfold affineCoord
  rw [torusAffinePoint_algebraMap]
  simp [torusAffineEval]

theorem TorusAffine.algHom_ext {B : Type} [CommRing B] [Algebra k B]
    {f g : TorusAffine k a b →ₐ[k] B} (ht : ∀ i, f (torusCoord k a b i) = g (torusCoord k a b i))
    (hc : ∀ j, f (affineCoord k a b j) = g (affineCoord k a b j)) : f = g := by
  have h : (f : TorusAffine k a b →+* B).comp (algebraMap (MvPolynomial (Fin a ⊕ Fin b) k) _) =
      (g : TorusAffine k a b →+* B).comp (algebraMap (MvPolynomial (Fin a ⊕ Fin b) k) _) := by
    have h' : (f.comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin a ⊕ Fin b) k)
        (TorusAffine k a b))) = g.comp (IsScalarTower.toAlgHom k _ _) := by
      refine MvPolynomial.algHom_ext fun v => ?_
      rcases v with i | j
      · exact ht i
      · exact hc j
    exact congrArg AlgHom.toRingHom h'
  exact AlgHom.toRingHom_injective
    (IsLocalization.ringHom_ext (Submonoid.powers (torusAffineDet k a b)) h)

theorem isUnit_apply_torusCoord (z : TorusAffine k a b →ₐ[k] k) (i : Fin a) :
    IsUnit (z (torusCoord k a b i)) :=
  (isUnit_torusCoord k a b i).map z

@[expose] def torusAffinePointEquiv :
    (Fin a → kˣ) × (Fin b → k) ≃ (TorusAffine k a b →ₐ[k] k) where
  toFun p := torusAffinePoint p.1 p.2
  invFun z := (fun i => (isUnit_apply_torusCoord z i).unit, fun j => z (affineCoord k a b j))
  left_inv p := by
    ext i
    · simp
    · simp
  right_inv z := TorusAffine.algHom_ext (fun i => by simp) (fun j => by simp)

theorem torusAffinePointEquiv_apply (p : (Fin a → kˣ) × (Fin b → k)) :
    torusAffinePointEquiv p = torusAffinePoint p.1 p.2 :=
  rfl

end CFSG.LieType.AlgebraicGroups
