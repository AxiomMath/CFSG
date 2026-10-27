module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.OddStandard.AltStdSmall4.GL62

open Matrix

@[expose] def fst {α : Type*} (x : Fin 6 → α) : Fin 3 → α := x ∘ Fin.castAdd 3

@[expose] def snd {α : Type*} (x : Fin 6 → α) : Fin 3 → α := x ∘ Fin.natAdd 3

@[simp] theorem fst_append {α : Type*} (v w : Fin 3 → α) : fst (Fin.append v w) = v :=
  funext (Fin.append_left v w)

@[simp] theorem snd_append {α : Type*} (v w : Fin 3 → α) : snd (Fin.append v w) = w :=
  funext (Fin.append_right v w)

theorem append_fst_snd {α : Type*} (x : Fin 6 → α) : Fin.append (fst x) (snd x) = x :=
  Fin.append_castAdd_natAdd

theorem ext_halves {α : Type*} {x y : Fin 6 → α} (h₁ : fst x = fst y) (h₂ : snd x = snd y) :
    x = y := by
  rw [← append_fst_snd x, ← append_fst_snd y, h₁, h₂]

@[simp] theorem fst_add (x y : Fin 6 → ZMod 2) : fst (x + y) = fst x + fst y := rfl

@[simp] theorem snd_add (x y : Fin 6 → ZMod 2) : snd (x + y) = snd x + snd y := rfl

@[simp] theorem fst_smul (c : ZMod 2) (x : Fin 6 → ZMod 2) : fst (c • x) = c • fst x := rfl

@[simp] theorem snd_smul (c : ZMod 2) (x : Fin 6 → ZMod 2) : snd (c • x) = c • snd x := rfl

theorem append_add (a b c d : Fin 3 → ZMod 2) :
    Fin.append (a + b) (c + d) = Fin.append a c + Fin.append b d :=
  ext_halves (by simp) (by simp)

theorem append_smul (r : ZMod 2) (a c : Fin 3 → ZMod 2) :
    Fin.append (r • a) (r • c) = r • Fin.append a c :=
  ext_halves (by simp) (by simp)

theorem add_add_self (a b : Fin 3 → ZMod 2) : a + b + b = a := by
  have h : ∀ x y : ZMod 2, x + y + y = x := by decide
  funext i
  exact h (a i) (b i)

@[expose] def appendLin (f g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun x := Fin.append (f x) (g x)
  map_add' x y := by rw [map_add, map_add, append_add]
  map_smul' c x := by rw [map_smul, map_smul, append_smul, RingHom.id_apply]

@[expose] def fstLin : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun := fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[expose] def sndLin : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun := snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem appendLin_apply (f g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (x : Fin 6 → ZMod 2) : appendLin f g x = Fin.append (f x) (g x) := rfl

@[simp] theorem fstLin_apply (x : Fin 6 → ZMod 2) : fstLin x = fst x := rfl

@[simp] theorem sndLin_apply (x : Fin 6 → ZMod 2) : sndLin x = snd x := rfl

@[expose] def involGL (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (h : M * M = 1) :
    GL (Fin 6) (ZMod 2) :=
  ⟨M, M, h, h⟩

@[simp] theorem coe_involGL (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (h : M * M = 1) :
    (involGL M h : Matrix (Fin 6) (Fin 6) (ZMod 2)) = M := rfl

theorem toMatrix'_mul_self {f : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)}
    (h : ∀ x, f (f x) = x) : LinearMap.toMatrix' f * LinearMap.toMatrix' f = 1 := by
  rw [← LinearMap.toMatrix'_comp, show f.comp f = LinearMap.id from LinearMap.ext h,
    LinearMap.toMatrix'_id]

@[expose] def zLin : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  appendLin (fstLin + sndLin) sndLin

theorem zLin_apply (x : Fin 6 → ZMod 2) : zLin x = Fin.append (fst x + snd x) (snd x) := rfl

theorem zLin_zLin (x : Fin 6 → ZMod 2) : zLin (zLin x) = x := by
  rw [zLin_apply, zLin_apply, fst_append, snd_append, add_add_self, append_fst_snd]

@[expose] def z₀ : GL (Fin 6) (ZMod 2) :=
  involGL (LinearMap.toMatrix' zLin) (toMatrix'_mul_self zLin_zLin)

theorem z0_mulVec (v w : Fin 3 → ZMod 2) :
    (z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append v w = Fin.append (v + w) w := by
  rw [z₀, coe_involGL, LinearMap.toMatrix'_mulVec, zLin_apply, fst_append, snd_append]

theorem z0_mulVec' (x : Fin 6 → ZMod 2) :
    (z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x = Fin.append (fst x + snd x) (snd x) := by
  rw [z₀, coe_involGL, LinearMap.toMatrix'_mulVec, zLin_apply]

theorem z0_mul_self : z₀ * z₀ = 1 := Units.ext (toMatrix'_mul_self zLin_zLin)

theorem z0_inv : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right z0_mul_self

@[expose] def dgLin (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  appendLin (A.mulVecLin ∘ₗ fstLin) (A.mulVecLin ∘ₗ sndLin)

theorem dgLin_apply (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x : Fin 6 → ZMod 2) :
    dgLin A x = Fin.append (A *ᵥ fst x) (A *ᵥ snd x) := rfl

@[expose] def dgMat : Matrix (Fin 3) (Fin 3) (ZMod 2) →* Matrix (Fin 6) (Fin 6) (ZMod 2) where
  toFun A := LinearMap.toMatrix' (dgLin A)
  map_one' := by
    rw [show dgLin 1 = LinearMap.id from LinearMap.ext fun x => by
      rw [dgLin_apply, one_mulVec, one_mulVec, append_fst_snd, LinearMap.id_apply],
      LinearMap.toMatrix'_id]
  map_mul' A B := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, dgLin_apply, dgLin_apply, dgLin_apply, fst_append, snd_append,
      mulVec_mulVec, mulVec_mulVec]

theorem dgMat_mulVec (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x : Fin 6 → ZMod 2) :
    dgMat A *ᵥ x = Fin.append (A *ᵥ fst x) (A *ᵥ snd x) :=
  LinearMap.toMatrix'_mulVec _ _

@[expose] def dg : GL (Fin 3) (ZMod 2) →* GL (Fin 6) (ZMod 2) := Units.map dgMat

theorem coe_dg (A : GL (Fin 3) (ZMod 2)) :
    (dg A : Matrix (Fin 6) (Fin 6) (ZMod 2)) = dgMat (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  rfl

theorem dg_mulVec (A : GL (Fin 3) (ZMod 2)) (v w : Fin 3 → ZMod 2) :
    (dg A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append v w =
      Fin.append ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)
        ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) := by
  rw [coe_dg, dgMat_mulVec, fst_append, snd_append]

theorem dg_mulVec' (A : GL (Fin 3) (ZMod 2)) (x : Fin 6 → ZMod 2) :
    (dg A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x =
      Fin.append ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ fst x)
        ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ snd x) := by
  rw [coe_dg, dgMat_mulVec]

@[expose] def B₀ : Subgroup (GL (Fin 6) (ZMod 2)) := dg.range ⊔ Subgroup.zpowers z₀

@[expose] def swapLin : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) := appendLin sndLin fstLin

theorem swapLin_apply (x : Fin 6 → ZMod 2) : swapLin x = Fin.append (snd x) (fst x) := rfl

theorem swapLin_swapLin (x : Fin 6 → ZMod 2) : swapLin (swapLin x) = x := by
  rw [swapLin_apply, swapLin_apply, fst_append, snd_append, append_fst_snd]

@[expose] def gN : GL (Fin 6) (ZMod 2) :=
  involGL (LinearMap.toMatrix' swapLin) (toMatrix'_mul_self swapLin_swapLin)

theorem gN_mulVec (v w : Fin 3 → ZMod 2) :
    (gN : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append v w = Fin.append w v := by
  rw [gN, coe_involGL, LinearMap.toMatrix'_mulVec, swapLin_apply, fst_append, snd_append]

@[expose] def gSMat : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0; 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0; 0, 1, 0, 0, 0, 0;
    1, 1, 0, 0, 1, 0]

@[expose] def gGMat : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 0]

@[expose] def gWMat : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 1, 0, 1; 0, 1, 0, 0, 1, 0; 1, 0, 0, 1, 0, 0; 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0;
    0, 0, 1, 1, 0, 0]

theorem gSMat_mul_self : gSMat * gSMat = 1 := by decide

theorem gGMat_mul_self : gGMat * gGMat = 1 := by decide

theorem gWMat_mul_self : gWMat * gWMat = 1 := by decide

@[expose] def gS : GL (Fin 6) (ZMod 2) := involGL gSMat gSMat_mul_self

@[expose] def gG : GL (Fin 6) (ZMod 2) := involGL gGMat gGMat_mul_self

@[expose] def gW : GL (Fin 6) (ZMod 2) := involGL gWMat gWMat_mul_self

@[expose] def MN : Subgroup (GL (Fin 6) (ZMod 2)) := B₀ ⊔ Subgroup.zpowers gN

@[expose] def MS : Subgroup (GL (Fin 6) (ZMod 2)) := B₀ ⊔ Subgroup.zpowers gS

@[expose] def MG : Subgroup (GL (Fin 6) (ZMod 2)) := B₀ ⊔ Subgroup.zpowers gG

@[expose] def MW : Subgroup (GL (Fin 6) (ZMod 2)) := B₀ ⊔ Subgroup.zpowers gW

@[expose] def GL62Overgroups : Prop :=
  ∀ X : Subgroup (GL (Fin 6) (ZMod 2)), B₀ ≤ X → (∀ x ∈ X, x * z₀ = z₀ * x → x ∈ B₀) →
    Nat.card X = 336 ∨ Nat.card X = 1008 ∨ Nat.card X = 56448 ∨ Nat.card X = 120960 ∨
      Nat.card X = 362880

@[expose] def GL62OvergroupsEq : Prop :=
  ∀ X : Subgroup (GL (Fin 6) (ZMod 2)), B₀ ≤ X → (∀ x ∈ X, x * z₀ = z₀ * x → x ∈ B₀) →
    (X = B₀ ∧ Nat.card X = 336) ∨ (X = MN ∧ Nat.card X = 1008) ∨ (X = MW ∧ Nat.card X = 56448) ∨
      (X = MS ∧ Nat.card X = 120960) ∨ (X = MG ∧ Nat.card X = 362880)

end CFSG.OddStandard.AltStdSmall4.GL62
