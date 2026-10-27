module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BCHModuleAut.BCHModuleAut
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.Geometry

open scoped commutatorElement

open CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BCHModuleAut

open CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BCHCentralCommutatorLaws

variable {p : ℕ} {E : Type*} [Group E]

theorem central_of_class (hclass : commutator E ≤ Subgroup.center E) :
    ∀ x y : E, ⁅x, y⁆ ∈ Subgroup.center E := fun x y =>
  hclass (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))

section Defs

variable (hp : p.Prime) (hodd : p ≠ 2) (hexp : ∀ x : E, x ^ p = 1)
  (hclass : commutator E ≤ Subgroup.center E)

abbrev V : Type _ := Lin p E hp hodd hexp (central_of_class hclass)

@[expose] def toE (x : V hp hodd hexp hclass) : E := Lin.val hp hodd hexp (central_of_class hclass) x

@[expose] def ofE (x : E) : V hp hodd hexp hclass := Lin.mk hp hodd hexp (central_of_class hclass) x

@[simp] theorem toE_ofE (x : E) : toE hp hodd hexp hclass (ofE hp hodd hexp hclass x) = x := rfl

@[simp] theorem ofE_toE (x : V hp hodd hexp hclass) :
    ofE hp hodd hexp hclass (toE hp hodd hexp hclass x) = x := rfl

theorem toE_injective : Function.Injective (toE hp hodd hexp hclass) :=
  Lin.val_injective hp hodd hexp (central_of_class hclass)

theorem toE_add (x y : V hp hodd hexp hclass) :
    toE hp hodd hexp hclass (x + y) =
      (toE hp hodd hexp hclass x * toE hp hodd hexp hclass y) *
        (⁅toE hp hodd hexp hclass x, toE hp hodd hexp hclass y⁆ ^ ((p + 1) / 2))⁻¹ := rfl

@[simp] theorem toE_zero : toE hp hodd hexp hclass (0 : V hp hodd hexp hclass) = 1 := rfl

theorem toE_smul (c : ZMod p) (x : V hp hodd hexp hclass) :
    toE hp hodd hexp hclass (c • x) = toE hp hodd hexp hclass x ^ c.val :=
  Lin.val_smul hp hodd hexp (central_of_class hclass) c x

theorem toE_add_of_central {x y : V hp hodd hexp hclass}
    (hx : toE hp hodd hexp hclass x ∈ Subgroup.center E) :
    toE hp hodd hexp hclass (x + y) = toE hp hodd hexp hclass x * toE hp hodd hexp hclass y := by
  rw [toE_add]
  have : ⁅toE hp hodd hexp hclass x, toE hp hodd hexp hclass y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 ((Subgroup.mem_center_iff.1 hx _).symm)
  rw [this]; simp

@[expose] def Z : Submodule (ZMod p) (V hp hodd hexp hclass) where
  carrier := {x | toE hp hodd hexp hclass x ∈ Subgroup.center E}
  zero_mem' := by
    show toE hp hodd hexp hclass 0 ∈ _
    rw [toE_zero]; exact (Subgroup.center E).one_mem
  add_mem' := by
    intro x y hx hy
    show toE hp hodd hexp hclass (x + y) ∈ _
    rw [toE_add]
    exact (Subgroup.center E).mul_mem ((Subgroup.center E).mul_mem hx hy)
      ((Subgroup.center E).inv_mem (Subgroup.pow_mem (Subgroup.center E) (central_of_class hclass _ _) _))
  smul_mem' := by
    intro c x hx
    show toE hp hodd hexp hclass (c • x) ∈ _
    rw [toE_smul]
    exact Subgroup.pow_mem (Subgroup.center E) hx _

theorem mem_Z_iff (x : V hp hodd hexp hclass) :
    x ∈ Z hp hodd hexp hclass ↔ toE hp hodd hexp hclass x ∈ Subgroup.center E := Iff.rfl

@[expose] def commV (x y : V hp hodd hexp hclass) : V hp hodd hexp hclass :=
  ofE hp hodd hexp hclass ⁅toE hp hodd hexp hclass x, toE hp hodd hexp hclass y⁆

theorem commV_mem (x y : V hp hodd hexp hclass) :
    commV hp hodd hexp hclass x y ∈ Z hp hodd hexp hclass :=
  (mem_Z_iff hp hodd hexp hclass _).2 (central_of_class hclass _ _)

theorem commV_add_left (x x' y : V hp hodd hexp hclass) :
    commV hp hodd hexp hclass (x + x') y =
      commV hp hodd hexp hclass x y + commV hp hodd hexp hclass x' y := by
  apply toE_injective hp hodd hexp hclass
  rw [toE_add_of_central hp hodd hexp hclass
    (x := commV hp hodd hexp hclass _ _)
    ((mem_Z_iff hp hodd hexp hclass _).1 (commV_mem hp hodd hexp hclass _ _))]
  show ⁅toE hp hodd hexp hclass (x + x'), toE hp hodd hexp hclass y⁆ = _
  rw [toE_add, commutator_mul_central_left (central_of_class hclass), commutator_mul_left (central_of_class hclass)]
  · rfl
  · exact inv_mem (Subgroup.pow_mem _ (central_of_class hclass _ _) _)

theorem commV_add_right (x y y' : V hp hodd hexp hclass) :
    commV hp hodd hexp hclass x (y + y') =
      commV hp hodd hexp hclass x y + commV hp hodd hexp hclass x y' := by
  apply toE_injective hp hodd hexp hclass
  rw [toE_add_of_central hp hodd hexp hclass
    (x := commV hp hodd hexp hclass _ _)
    ((mem_Z_iff hp hodd hexp hclass _).1 (commV_mem hp hodd hexp hclass _ _))]
  show ⁅toE hp hodd hexp hclass x, toE hp hodd hexp hclass (y + y')⁆ = _
  rw [toE_add, commutator_mul_central_right (central_of_class hclass), commutator_mul_right (central_of_class hclass)]
  · rfl
  · exact inv_mem (Subgroup.pow_mem _ (central_of_class hclass _ _) _)

theorem commV_smul_left (c : ZMod p) (x y : V hp hodd hexp hclass) :
    commV hp hodd hexp hclass (c • x) y = c • commV hp hodd hexp hclass x y := by
  apply toE_injective hp hodd hexp hclass
  rw [toE_smul]
  show ⁅toE hp hodd hexp hclass (c • x), toE hp hodd hexp hclass y⁆ = _
  rw [toE_smul, commutator_pow_left (central_of_class hclass)]
  rfl

theorem commV_smul_right (c : ZMod p) (x y : V hp hodd hexp hclass) :
    commV hp hodd hexp hclass x (c • y) = c • commV hp hodd hexp hclass x y := by
  apply toE_injective hp hodd hexp hclass
  rw [toE_smul]
  show ⁅toE hp hodd hexp hclass x, toE hp hodd hexp hclass (c • y)⁆ = _
  rw [toE_smul, commutator_pow_right (central_of_class hclass)]
  rfl

@[expose] def bracket : V hp hodd hexp hclass →ₗ[ZMod p] V hp hodd hexp hclass →ₗ[ZMod p]
    Z hp hodd hexp hclass :=
  LinearMap.mk₂ (ZMod p) (fun x y => ⟨commV hp hodd hexp hclass x y, commV_mem hp hodd hexp hclass x y⟩)
    (fun x x' y => Subtype.ext (commV_add_left hp hodd hexp hclass x x' y))
    (fun c x y => Subtype.ext (commV_smul_left hp hodd hexp hclass c x y))
    (fun x y y' => Subtype.ext (commV_add_right hp hodd hexp hclass x y y'))
    (fun c x y => Subtype.ext (commV_smul_right hp hodd hexp hclass c x y))

theorem Z_le_ker : Z hp hodd hexp hclass ≤ (bracket hp hodd hexp hclass).ker := by
  intro z hz
  rw [LinearMap.mem_ker]
  ext y
  apply toE_injective hp hodd hexp hclass
  show ⁅toE hp hodd hexp hclass z, toE hp hodd hexp hclass y⁆ = 1
  exact commutatorElement_eq_one_iff_mul_comm.2 ((Subgroup.mem_center_iff.1 ((mem_Z_iff hp hodd hexp hclass _).1 hz) _).symm)

theorem Z_le_flip_ker : Z hp hodd hexp hclass ≤ (bracket hp hodd hexp hclass).flip.ker := by
  intro z hz
  rw [LinearMap.mem_ker]
  ext y
  apply toE_injective hp hodd hexp hclass
  show ⁅toE hp hodd hexp hclass y, toE hp hodd hexp hclass z⁆ = 1
  exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 ((mem_Z_iff hp hodd hexp hclass _).1 hz) _)

@[expose] def quotientBracket : (V hp hodd hexp hclass ⧸ Z hp hodd hexp hclass) →ₗ[ZMod p]
    (V hp hodd hexp hclass ⧸ Z hp hodd hexp hclass) →ₗ[ZMod p] Z hp hodd hexp hclass :=
  (bracket hp hodd hexp hclass).liftQ₂ (Z hp hodd hexp hclass) (Z hp hodd hexp hclass)
    (Z_le_ker hp hodd hexp hclass) (Z_le_flip_ker hp hodd hexp hclass)

@[simp] theorem quotientBracket_mk (x y : V hp hodd hexp hclass) :
    quotientBracket hp hodd hexp hclass (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      bracket hp hodd hexp hclass x y := rfl

end Defs
end CFSG.GroupTheory.CoprimeActionSupport.Geometry
