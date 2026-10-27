module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.GroupAction.Hom

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] (A : Subgroup G) [A.Normal] [IsMulCommutative ↥A]

theorem conjNormal_le_ker : A ≤ (MulAut.conjNormal (H := A)).ker := by
  intro b hb
  simp only [MonoidHom.mem_ker]
  ext a
  simpa [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul] using setLike_mul_comm hb a.2

def quotientConjAut : G ⧸ A →* MulAut ↥A :=
  QuotientGroup.lift A MulAut.conjNormal (conjNormal_le_ker A)

@[simp] theorem coe_quotientConjAut_mk_apply (g : G) (a : ↥A) :
    ((quotientConjAut A (g : G ⧸ A) a : ↥A) : G) = g * a * g⁻¹ := by
  simp [quotientConjAut, MulAut.conjNormal_apply]

theorem conj_eq_conj_of_quotientMk_eq {g g' : G} (h : (g : G ⧸ A) = (g' : G ⧸ A)) (a : ↥A) :
    g * a * g⁻¹ = g' * a * g'⁻¹ := by
  rw [← coe_quotientConjAut_mk_apply A g a, ← coe_quotientConjAut_mk_apply A g' a, h]

instance quotientMulDistribMulAction : MulDistribMulAction (G ⧸ A) ↥A :=
  MulDistribMulAction.compHom ↥A (quotientConjAut A)

theorem quotient_smul_def (x : G ⧸ A) (a : ↥A) : x • a = quotientConjAut A x a := rfl

@[simp] theorem coe_quotientMk_smul (g : G) (a : ↥A) :
    (((g : G ⧸ A) • a : ↥A) : G) = g * a * g⁻¹ := by
  rw [quotient_smul_def, coe_quotientConjAut_mk_apply]

instance quotientDistribMulAction : DistribMulAction (G ⧸ A) (Additive ↥A) where
  smul x a := Additive.ofMul (x • a.toMul)
  one_smul a := by change Additive.ofMul ((1 : G ⧸ A) • a.toMul) = a; rw [one_smul]; rfl
  mul_smul x y a := by change Additive.ofMul ((x * y) • a.toMul) = _; rw [mul_smul]; rfl
  smul_zero x := by change Additive.ofMul (x • (1 : ↥A)) = 0; rw [smul_one]; rfl
  smul_add x a b := by
    change Additive.ofMul (x • (a.toMul * b.toMul)) = _; rw [smul_mul']; rfl

@[simp] theorem toMul_smul (x : G ⧸ A) (a : Additive ↥A) : (x • a).toMul = x • a.toMul := rfl

@[simp] theorem ofMul_smul (x : G ⧸ A) (a : ↥A) :
    Additive.ofMul (x • a) = x • Additive.ofMul a := rfl

@[simp] theorem coe_toMul_quotientMk_smul (g : G) (a : Additive ↥A) :
    ((((g : G ⧸ A) • a).toMul : ↥A) : G) = g * (a.toMul : ↥A) * g⁻¹ := by
  rw [toMul_smul, coe_quotientMk_smul]

end CFSG.FeitThompson
