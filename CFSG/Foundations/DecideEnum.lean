module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

@[expose] public section

namespace CFSG.DecideEnum

open Finset Matrix

@[instance_reducible] def decDetOne2 {R : Type*} [CommRing R] [DecidableEq R]
    (A : Matrix (Fin 2) (Fin 2) R) : Decidable (A.det = 1) :=
  decidable_of_iff (A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1) (by rw [det_fin_two])

@[instance_reducible] def decDetOne3 {R : Type*} [CommRing R] [DecidableEq R]
    (A : Matrix (Fin 3) (Fin 3) R) : Decidable (A.det = 1) :=
  decidable_of_iff (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
      A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 = 1)
    (by rw [det_fin_three])

@[instance_reducible] def fintypeSL2 {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] :
    Fintype (SpecialLinearGroup (Fin 2) R) :=
  @Subtype.fintype (Matrix (Fin 2) (Fin 2) R) (fun A => A.det = 1) decDetOne2 _

@[instance_reducible] def fintypeSL3 {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] :
    Fintype (SpecialLinearGroup (Fin 3) R) :=
  @Subtype.fintype (Matrix (Fin 3) (Fin 3) R) (fun A => A.det = 1) decDetOne3 _

scoped instance (priority := high) decForallSL2 {R : Type*} [CommRing R] [Fintype R]
    [DecidableEq R] (p : SpecialLinearGroup (Fin 2) R → Prop) [DecidablePred p] :
    Decidable (∀ g, p g) :=
  @Fintype.decidableForallFintype _ p _ fintypeSL2

scoped instance (priority := high) decForallSL3 {R : Type*} [CommRing R] [Fintype R]
    [DecidableEq R] (p : SpecialLinearGroup (Fin 3) R → Prop) [DecidablePred p] :
    Decidable (∀ g, p g) :=
  @Fintype.decidableForallFintype _ p _ fintypeSL3

def invSL3 {R : Type*} [CommRing R] (g : SpecialLinearGroup (Fin 3) R) :
    SpecialLinearGroup (Fin 3) R :=
  ⟨!![g 1 1 * g 2 2 - g 1 2 * g 2 1, -(g 0 1 * g 2 2) + g 0 2 * g 2 1,
        g 0 1 * g 1 2 - g 0 2 * g 1 1;
      -(g 1 0 * g 2 2) + g 1 2 * g 2 0, g 0 0 * g 2 2 - g 0 2 * g 2 0,
        -(g 0 0 * g 1 2) + g 0 2 * g 1 0;
      g 1 0 * g 2 1 - g 1 1 * g 2 0, -(g 0 0 * g 2 1) + g 0 1 * g 2 0,
        g 0 0 * g 1 1 - g 0 1 * g 1 0], by
    rw [← adjugate_fin_three, ← SpecialLinearGroup.coe_inv]; exact (g⁻¹).2⟩

theorem inv_eq_invSL3 {R : Type*} [CommRing R] (g : SpecialLinearGroup (Fin 3) R) :
    g⁻¹ = invSL3 g :=
  Subtype.ext (by rw [SpecialLinearGroup.coe_inv, adjugate_fin_three]; rfl)

end CFSG.DecideEnum
