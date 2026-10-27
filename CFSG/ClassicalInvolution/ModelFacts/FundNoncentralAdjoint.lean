module

public import CFSG.ClassicalInvolution.WeakCT.WeylSigns

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Adjoint

variable {τ : Tag} {K : Type} [Field K] {F : RootOperatorFamily τ}

theorem map_wS_sq_eq_inv_torusElement (l : Fin τ.rank) (φ : SL(2, K) →* adjointGroup τ K)
    (hup : ∀ c, φ (sl2Upper c) = xPar F (Pi.single l 1) c)
    (hlow : ∀ c, φ (sl2Lower c) = xPar F (-Pi.single l 1) c) :
    φ (wS (1 : Kˣ) * wS (1 : Kˣ)) = (torusElement τ K l (-1))⁻¹ := by
  have hw : ∀ t : Kˣ, CFSG.LieType.Steinberg.weylElement (xPar F) l t = φ (wS t) :=
    fun t => weylElement_eq_map (D := adjDatum F K) hup hlow t
  have e1 : CFSG.LieType.Chevalley.weylElement τ K l = φ (wS 1) := by
    rw [weylElement_eq_xPar F l, hw]
  have h1 := weylElement_xPar (F := F) (K := K) l (-1)
  have h2' : wS (-1 : Kˣ) = (wS (1 : Kˣ))⁻¹ :=
    eq_inv_of_mul_eq_one_right wS_one_mul_wS_neg_one
  rw [hw, e1, h2', map_inv] at h1
  have h3 : torusElement τ K l (-1) = (φ (wS 1))⁻¹ * (φ (wS 1))⁻¹ :=
    eq_mul_inv_of_mul_eq h1.symm
  rw [map_mul, h3]
  simp

theorem torusElement_conj_xPar (l : Fin τ.rank) (t : Kˣ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (c : K) :
    torusElement τ K l t * xPar F β c * (torusElement τ K l t)⁻¹ =
      xPar F β (((t ^ (∑ j, τ.cartan l j * β j) : Kˣ) : K) * c) := by
  rw [xPar_of_isRoot hβ, F.torusElement_mul_eltElement_mul_inv, ← xPar_of_isRoot hβ]

theorem torusElement_neg_one_mem_center_of_map (l : Fin τ.rank) (φ : SL(2, K) →* adjointGroup τ K)
    (hup : ∀ c, φ (sl2Upper c) = xPar F (Pi.single l 1) c)
    (hlow : ∀ c, φ (sl2Lower c) = xPar F (-Pi.single l 1) c)
    (h : φ (wS (1 : Kˣ) * wS (1 : Kˣ)) ∈ Subgroup.center (adjointGroup τ K)) :
    torusElement τ K l (-1) ∈ Subgroup.center (adjointGroup τ K) := by
  have h' := inv_mem h
  rw [map_wS_sq_eq_inv_torusElement l φ hup hlow, inv_inv] at h'
  exact h'

end Adjoint

end CFSG.ClassicalInvolution.ModelFacts
