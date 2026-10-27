module

public import CFSG.ClassicalInvolution.Phan.PhanS9O1Card
public import CFSG.ClassicalInvolution.Phan.PhanP13Fix

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open QuadraticMap CFSG.LieType.Universal.Spin

section Fix

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

@[expose] def fixSub (S : Set V) : Subgroup (spinGroup Q) where
  carrier := {g | ∀ x ∈ S, spinAction Q g x = x}
  mul_mem' {a b} ha hb x hx := by
    rw [map_mul, LinearEquiv.mul_apply, hb x hx, ha x hx]
  one_mem' x _ := by rw [map_one]; rfl
  inv_mem' {a} ha x hx := by
    have h := ha x hx
    calc spinAction Q a⁻¹ x = spinAction Q a⁻¹ (spinAction Q a x) := by rw [h]
      _ = x := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

variable {Q}

theorem mem_fixSub {S : Set V} {g : spinGroup Q} :
    g ∈ fixSub Q S ↔ ∀ x ∈ S, spinAction Q g x = x := Iff.rfl

end Fix

section Card

variable {F : Type} [Field F] [Invertible (2 : F)] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {W : Submodule F V}

theorem card_fixSub_le [Finite F] [Nontrivial V]
    [Nontrivial (LinearMap.BilinForm.orthogonal Q.polarBilin W)] (hQ : Q.Nondegenerate)
    (hW : (Q.restrict W).Nondegenerate) :
    Nat.card (fixSub Q (W : Set V)) ≤
      Nat.card (spinGroup (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W))) := by
  have hQ₁ : (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W)).Nondegenerate :=
    hQ.nondegenerate_restrict_orthogonal hW
  have := finite_spinGroup hQ₁
  set f := ((PhanP.decompOrth hW).toIsometry.comp
      (QuadraticMap.Isometry.inl (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W))
        (Q.restrict W))).spinGroupMap with hf
  have hle : fixSub Q (W : Set V) ≤ f.range := fun y hy =>
    PhanP.mem_range_spinGroupMap_of_fix hQ hW fun x hx => hy x hx
  have := Finite.of_surjective _ f.rangeRestrict_surjective
  calc Nat.card (fixSub Q (W : Set V)) ≤ Nat.card f.range := Subgroup.card_le_of_le hle
    _ ≤ _ := Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective

end Card

end CFSG.ClassicalInvolution.PhanB3.S
