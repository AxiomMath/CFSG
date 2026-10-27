module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

@[expose] def AbelianSub (V : Subgroup G) (_hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) : Type _ :=
  Additive V

namespace AbelianSub

variable {V : Subgroup G} {hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x}

instance : AddCommGroup (AbelianSub V hV) :=
  { (inferInstance : AddGroup (Additive ↥V)) with
    add_comm := fun x y => by
      show Additive.ofMul (Additive.toMul x * Additive.toMul y) =
        Additive.ofMul (Additive.toMul y * Additive.toMul x)
      exact congrArg Additive.ofMul
        (Subtype.ext (hV _ (Additive.toMul x).2 _ (Additive.toMul y).2)) }

@[expose] def val (x : AbelianSub V hV) : G := ((Additive.toMul x : V) : G)

@[expose] def mk (v : G) (hv : v ∈ V) : AbelianSub V hV := Additive.ofMul ⟨v, hv⟩

theorem val_mem (x : AbelianSub V hV) : x.val ∈ V := (Additive.toMul x).2

@[simp] theorem val_mk (v : G) (hv : v ∈ V) : (mk (hV := hV) v hv).val = v := rfl

@[simp] theorem mk_val (x : AbelianSub V hV) : mk x.val (val_mem x) = x := rfl

@[ext] theorem ext {x y : AbelianSub V hV} (h : x.val = y.val) : x = y :=
  congrArg Additive.ofMul (Subtype.ext h)

@[simp] theorem val_add (x y : AbelianSub V hV) : (x + y).val = x.val * y.val := rfl

@[simp] theorem val_zero : (0 : AbelianSub V hV).val = 1 := rfl

@[simp] theorem val_neg (x : AbelianSub V hV) : (-x).val = x.val⁻¹ := rfl

@[simp] theorem val_sub (x y : AbelianSub V hV) : (x - y).val = x.val * y.val⁻¹ := by
  rw [sub_eq_add_neg, val_add, val_neg]

theorem mk_mul (v w : G) (hv : v ∈ V) (hw : w ∈ V) :
    mk (hV := hV) (v * w) (V.mul_mem hv hw) = mk v hv + mk w hw := rfl

theorem end_ext {f g : AddMonoid.End (AbelianSub V hV)} (h : ∀ x, (f x).val = (g x).val) :
    f = g :=
  AddMonoidHom.ext fun x => ext (h x)

private def endOfAux (f : G → G)
    (h : (∀ v ∈ V, f v ∈ V) ∧ ∀ v ∈ V, ∀ w ∈ V, f (v * w) = f v * f w) :
    AddMonoid.End (AbelianSub V hV) where
  toFun x := mk (f x.val) (h.1 _ (val_mem x))
  map_zero' := ext <| by
    have h1 := h.2 1 V.one_mem 1 V.one_mem
    rw [one_mul] at h1
    simpa using h1.symm
  map_add' x y := ext (h.2 _ (val_mem x) _ (val_mem y))

noncomputable def endOf (V : Subgroup G) (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (f : G → G) : AddMonoid.End (AbelianSub V hV) :=
  open Classical in
  if h : (∀ v ∈ V, f v ∈ V) ∧ ∀ v ∈ V, ∀ w ∈ V, f (v * w) = f v * f w then endOfAux f h
  else 0

theorem val_endOf_apply {f : G → G} (hf : ∀ v ∈ V, f v ∈ V)
    (hmul : ∀ v ∈ V, ∀ w ∈ V, f (v * w) = f v * f w) (x : AbelianSub V hV) :
    (endOf V hV f x).val = f x.val := by
  rw [endOf, dif_pos ⟨hf, hmul⟩]
  rfl

noncomputable def conj (V : Subgroup G) (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (n : G) : AddMonoid.End (AbelianSub V hV) :=
  endOf V hV fun v => n * v * n⁻¹

theorem val_conj_apply {n : G} (hn : ∀ v ∈ V, n * v * n⁻¹ ∈ V) (x : AbelianSub V hV) :
    (conj V hV n x).val = n * x.val * n⁻¹ :=
  val_endOf_apply hn (fun v _ w _ => by group) x

theorem conj_mem_of_mem_normalizer {n : G} (hn : n ∈ normalizer (V : Set G)) :
    ∀ v ∈ V, n * v * n⁻¹ ∈ V :=
  fun v hv => (mem_normalizer_iff.1 hn v).1 hv

theorem conj_one : conj V hV 1 = 1 :=
  end_ext fun x => by
    rw [val_conj_apply (fun v hv => by simpa using hv)]
    simp

theorem conj_mul {n m : G} (hn : ∀ v ∈ V, n * v * n⁻¹ ∈ V) (hm : ∀ v ∈ V, m * v * m⁻¹ ∈ V) :
    conj V hV (n * m) = conj V hV n * conj V hV m :=
  end_ext fun x => by
    have hnm : ∀ v ∈ V, n * m * v * (n * m)⁻¹ ∈ V := fun v hv => by
      have := hn _ (hm v hv)
      rwa [show n * (m * v * m⁻¹) * n⁻¹ = n * m * v * (n * m)⁻¹ by group] at this
    rw [val_conj_apply hnm, AddMonoid.End.coe_mul, Function.comp_apply,
      val_conj_apply hn, val_conj_apply hm]
    group

theorem conj_inv_mul {n : G} (hn : n ∈ normalizer (V : Set G)) :
    conj V hV n⁻¹ * conj V hV n = 1 := by
  rw [← conj_mul (conj_mem_of_mem_normalizer (inv_mem hn)) (conj_mem_of_mem_normalizer hn),
    inv_mul_cancel, conj_one]

theorem conj_mul_inv {n : G} (hn : n ∈ normalizer (V : Set G)) :
    conj V hV n * conj V hV n⁻¹ = 1 := by
  rw [← conj_mul (conj_mem_of_mem_normalizer hn) (conj_mem_of_mem_normalizer (inv_mem hn)),
    mul_inv_cancel, conj_one]

theorem add_self_eq_zero (h2 : ∀ v ∈ V, v * v = 1) (f : AddMonoid.End (AbelianSub V hV)) :
    f + f = 0 :=
  end_ext fun x => by
    change (f x + f x).val = (0 : AbelianSub V hV).val
    rw [val_add, val_zero]
    exact h2 _ (val_mem _)

end AbelianSub

end CFSG.GroupTheory
