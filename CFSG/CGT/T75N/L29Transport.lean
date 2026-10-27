module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.CGT.T75N

open Matrix

@[expose] def slRingEquiv {R S : Type} [CommRing R] [CommRing S] (n : ℕ) (κ : R ≃+* S) :
    SpecialLinearGroup (Fin n) R ≃* SpecialLinearGroup (Fin n) S := by
  refine MonoidHom.toMulEquiv (SpecialLinearGroup.map κ.toRingHom)
    (SpecialLinearGroup.map κ.symm.toRingHom) ?_ ?_
  · ext x i j
    simp
  · ext x i j
    simp

@[expose] def vecRingEquiv {R S : Type} [Ring R] [Ring S] (n : ℕ) (κ : R ≃+* S) :
    Multiplicative (Fin n → R) ≃* Multiplicative (Fin n → S) :=
  AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ => κ.toAddEquiv)

theorem vecRingEquiv_apply {R S : Type} [Ring R] [Ring S] (n : ℕ) (κ : R ≃+* S)
    (x : Multiplicative (Fin n → R)) (i : Fin n) :
    Multiplicative.toAdd (vecRingEquiv n κ x) i = κ (Multiplicative.toAdd x i) := rfl

theorem transport_natural {R S : Type} [CommRing R] [CommRing S] (n : ℕ) (κ : R ≃+* S)
    {Y V : Type} [Group Y] [Group V] (ρ : Y →* MulAut V) (e : Y ≃* SpecialLinearGroup (Fin n) R)
    (φ : V ≃* Multiplicative (Fin n → R))
    (h : ∀ (y : Y) (v : V), φ (ρ y v) = Multiplicative.ofAdd
      ((e y : Matrix (Fin n) (Fin n) R) *ᵥ Multiplicative.toAdd (φ v))) :
    ∃ (e' : Y ≃* SpecialLinearGroup (Fin n) S) (φ' : V ≃* Multiplicative (Fin n → S)),
      ∀ (y : Y) (v : V), φ' (ρ y v) = Multiplicative.ofAdd
        ((e' y : Matrix (Fin n) (Fin n) S) *ᵥ Multiplicative.toAdd (φ' v)) := by
  refine ⟨e.trans (slRingEquiv n κ), φ.trans (vecRingEquiv n κ), fun y v => ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  have h1 : Multiplicative.toAdd ((φ.trans (vecRingEquiv n κ)) (ρ y v)) i =
      κ (((e y : Matrix (Fin n) (Fin n) R) *ᵥ Multiplicative.toAdd (φ v)) i) := by
    show Multiplicative.toAdd (vecRingEquiv n κ (φ (ρ y v))) i = _
    rw [vecRingEquiv_apply, h y v]
    rfl
  rw [h1]
  exact RingHom.map_mulVec κ.toRingHom (e y : Matrix (Fin n) (Fin n) R)
    (Multiplicative.toAdd (φ v)) i

end CFSG.CGT.T75N
