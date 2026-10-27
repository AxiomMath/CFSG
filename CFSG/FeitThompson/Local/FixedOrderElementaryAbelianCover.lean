module

import CFSG.FeitThompson.Local.ConjugateFixedPointOrders
import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.Local.IntegerFixedDimensionRelation
public import CFSG.FeitThompson.Local.LiftedAverageFixedDimension

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix Module

variable {p d : ℕ} {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]

noncomputable def glMulEquivLinearEquiv (R : Type*) [CommRing R] (n : Type*) [Fintype n]
    [DecidableEq n] : GL n R ≃* ((n → R) ≃ₗ[R] (n → R)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

@[simp]
theorem glMulEquivLinearEquiv_apply {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (M : GL n R) (v : n → R) :
    glMulEquivLinearEquiv R n M v = (M : Matrix n n R) *ᵥ v := by
  simp [glMulEquivLinearEquiv, LinearMap.GeneralLinearGroup.generalLinearEquiv,
    Matrix.GeneralLinearGroup.toLin]

noncomputable def mulAutMulEquivLinearEquiv (V : Type*) [Group V]
    (e : V ≃* Multiplicative (Fin d → ZMod p)) :
    MulAut V ≃* ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) where
  toFun f := addEquivEquivZModLinearEquiv p _ _ (AddEquiv.toMultiplicative.symm (MulAut.congr e f))
  invFun g := MulAut.congr e.symm
    (AddEquiv.toMultiplicative ((addEquivEquivZModLinearEquiv p _ _).symm g))
  left_inv f := by ext v; simp [MulAut.congr]
  right_inv g := by ext w; simp [MulAut.congr]
  map_mul' f g := by ext w; simp [MulAut.congr]

@[simp]
theorem mulAutMulEquivLinearEquiv_apply (e : V ≃* Multiplicative (Fin d → ZMod p)) (f : MulAut V)
    (w : Fin d → ZMod p) :
    mulAutMulEquivLinearEquiv V e f w
      = Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd w)))) := by
  simp [mulAutMulEquivLinearEquiv, MulAut.congr]

noncomputable def mulAutMulEquivGL (V : Type*) [Group V]
    (e : V ≃* Multiplicative (Fin d → ZMod p)) : MulAut V ≃* GL (Fin d) (ZMod p) :=
  (mulAutMulEquivLinearEquiv V e).trans (glMulEquivLinearEquiv (ZMod p) (Fin d)).symm

theorem mulAutMulEquivGL_mulVec (e : V ≃* Multiplicative (Fin d → ZMod p)) (f : MulAut V)
    (w : Fin d → ZMod p) :
    (mulAutMulEquivGL V e f : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ w
      = Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd w)))) := by
  rw [← glMulEquivLinearEquiv_apply, mulAutMulEquivGL, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, mulAutMulEquivLinearEquiv_apply]

noncomputable def elementaryAbelianRep (A : Type*) [Group A] [MulDistribMulAction A V]
    (e : V ≃* Multiplicative (Fin d → ZMod p)) : A →* GL (Fin d) (ZMod p) :=
  (mulAutMulEquivGL V e).toMonoidHom.comp (MulDistribMulAction.toMulAut A V)

theorem elementaryAbelianRep_mulVec (e : V ≃* Multiplicative (Fin d → ZMod p)) (a : A)
    (w : Fin d → ZMod p) :
    (elementaryAbelianRep A e a : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ w
      = Multiplicative.toAdd (e (a • e.symm (Multiplicative.ofAdd w))) := by
  rw [elementaryAbelianRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    mulAutMulEquivGL_mulVec]
  rfl

theorem elementaryAbelianRep_mulVec_toAdd (e : V ≃* Multiplicative (Fin d → ZMod p)) (a : A)
    (v : V) :
    (elementaryAbelianRep A e a : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ Multiplicative.toAdd (e v)
      = Multiplicative.toAdd (e (a • v)) := by
  rw [elementaryAbelianRep_mulVec]; simp

theorem toAdd_mem_glFixedSpace_iff (e : V ≃* Multiplicative (Fin d → ZMod p)) (B : Subgroup A)
    (v : V) :
    Multiplicative.toAdd (e v) ∈ glFixedSpace (elementaryAbelianRep A e) B
      ↔ v ∈ FixedPoints.subgroup B V := by
  rw [mem_glFixedSpace, mem_fixedPoints_subgroup_iff]
  refine forall_congr' fun b => forall_congr' fun _ => ?_
  rw [elementaryAbelianRep_mulVec_toAdd e b v]
  exact ⟨fun h => e.injective (Multiplicative.toAdd.injective h), fun h => by rw [h]⟩

noncomputable def fixedPointsSubgroupEquivGlFixedSpace
    (e : V ≃* Multiplicative (Fin d → ZMod p)) (B : Subgroup A) :
    ↥(FixedPoints.subgroup B V) ≃ ↥(glFixedSpace (elementaryAbelianRep A e) B) :=
  Equiv.subtypeEquiv (e.toEquiv.trans (Multiplicative.toAdd (α := Fin d → ZMod p)))
    fun v => (toAdd_mem_glFixedSpace_iff e B v).symm

@[simp]
theorem fixedPointsSubgroupEquivGlFixedSpace_apply_coe
    (e : V ≃* Multiplicative (Fin d → ZMod p)) (B : Subgroup A)
    (v : ↥(FixedPoints.subgroup B V)) :
    (fixedPointsSubgroupEquivGlFixedSpace e B v : Fin d → ZMod p)
      = Multiplicative.toAdd (e (v : V)) := (rfl)

theorem natCard_fixedPoints_subgroup_eq_natCard_glFixedSpace
    (e : V ≃* Multiplicative (Fin d → ZMod p)) (B : Subgroup A) :
    Nat.card (FixedPoints.subgroup B V)
      = Nat.card (glFixedSpace (elementaryAbelianRep A e) B) :=
  Nat.card_congr (fixedPointsSubgroupEquivGlFixedSpace e B)

theorem natCard_fixedPoints_subgroup_eq_pow (hp : p.Prime)
    (e : V ≃* Multiplicative (Fin d → ZMod p)) (B : Subgroup A) :
    Nat.card (FixedPoints.subgroup B V)
      = p ^ finrank (ZMod p) (glFixedSpace (elementaryAbelianRep A e) B) := by
  have := Fact.mk hp
  rw [natCard_fixedPoints_subgroup_eq_natCard_glFixedSpace e B,
    Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

variable {ι : Type*} [Fintype ι]

theorem prod_natCard_fixedPoints_subgroup_pow_eq [Finite A] (hp : p.Prime)
    (hA : ¬ p ∣ Nat.card A) (hV : Nonempty (V ≃* Multiplicative (Fin d → ZMod p)))
    (B : ι → Subgroup A) [∀ i, DecidablePred (· ∈ B i)] (m n : ι → ℕ)
    (hmn : ∀ a : A, ∑ i with a ∈ B i, m i = ∑ i with a ∈ B i, n i) :
    ∏ i, Nat.card (FixedPoints.subgroup (B i) V) ^ (m i * Nat.card (B i))
      = ∏ i, Nat.card (FixedPoints.subgroup (B i) V) ^ (n i * Nat.card (B i)) := by
  obtain ⟨e⟩ := hV
  set ρ : A →* GL (Fin d) (ZMod p) := elementaryAbelianRep A e with hρ
  set r : ι → ℕ := fun i => finrank (ZMod p) (glFixedSpace ρ (B i)) with hr
  have hcard : ∀ i, Nat.card (FixedPoints.subgroup (B i) V) = p ^ r i := fun i => by
    rw [hr, hρ]; exact natCard_fixedPoints_subgroup_eq_pow hp e (B i)
  have hint : ∑ i, ((m i : ℤ) - n i) * (Nat.card (B i) : ℤ) * (r i : ℤ) = 0 :=
    sum_weighted_natCard_mul_finrank_glFixedSpace_eq_zero hp hA ρ B _
      (fun a => by rw [Finset.sum_sub_distrib, sub_eq_zero]; exact_mod_cast hmn a)
  have key : ∑ i, r i * (m i * Nat.card (B i)) = ∑ i, r i * (n i * Nat.card (B i)) := by
    have h1 : ∑ i, ((r i : ℤ) * (m i * Nat.card (B i)) - (r i : ℤ) * (n i * Nat.card (B i)))
        = 0 := by
      rw [← hint]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_sub_distrib, sub_eq_zero] at h1
    exact_mod_cast h1
  calc ∏ i, Nat.card (FixedPoints.subgroup (B i) V) ^ (m i * Nat.card (B i))
      = ∏ i, p ^ (r i * (m i * Nat.card (B i))) :=
        Finset.prod_congr rfl fun i _ => by rw [hcard i, ← pow_mul]
    _ = p ^ ∑ i, r i * (m i * Nat.card (B i)) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = p ^ ∑ i, r i * (n i * Nat.card (B i)) := by rw [key]
    _ = ∏ i, p ^ (r i * (n i * Nat.card (B i))) := (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ = ∏ i, Nat.card (FixedPoints.subgroup (B i) V) ^ (n i * Nat.card (B i)) :=
        Finset.prod_congr rfl fun i _ => by rw [hcard i, ← pow_mul]

theorem prod_natCard_fixedPoints_pow_eq_of_monoidHom_mulAut {A V : Type*} [Group A] [Group V]
    [Finite A] (hp : p.Prime) (hA : ¬ p ∣ Nat.card A)
    (hV : Nonempty (V ≃* Multiplicative (Fin d → ZMod p))) (φ : A →* MulAut V)
    (B : ι → Subgroup A) [∀ i, DecidablePred (· ∈ B i)] (m n : ι → ℕ)
    (hmn : ∀ a : A, ∑ i with a ∈ B i, m i = ∑ i with a ∈ B i, n i) :
    ∏ i, Nat.card {v : V // ∀ b ∈ B i, φ b v = v} ^ (m i * Nat.card (B i))
      = ∏ i, Nat.card {v : V // ∀ b ∈ B i, φ b v = v} ^ (n i * Nat.card (B i)) := by
  let inst : MulDistribMulAction A V := MulDistribMulAction.compHom V φ
  have hEq : ∀ i, Nat.card {v : V // ∀ b ∈ B i, φ b v = v}
      = Nat.card (FixedPoints.subgroup (B i) V) := fun i =>
    Nat.card_congr (Equiv.subtypeEquivRight fun v => by
      rw [mem_fixedPoints_subgroup_iff]
      exact ⟨fun h b hb => h b hb, fun h b hb => h b hb⟩)
  simp only [hEq]
  exact prod_natCard_fixedPoints_subgroup_pow_eq hp hA hV B m n hmn

end CFSG.FeitThompson
