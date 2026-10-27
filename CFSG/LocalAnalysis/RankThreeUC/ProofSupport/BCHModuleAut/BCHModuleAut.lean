module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BCHAddLaws.BCHAddLaws
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.DFinsupp

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace ProofSupport

namespace BCHModuleAut

open scoped commutatorElement

open OddClassTwoBCH

variable {p : ℕ} {E : Type*} [Group E]

@[expose] def Lin (p : ℕ) (E : Type*) [Group E] (_hp : p.Prime) (_hodd : p ≠ 2)
    (_hexp : ∀ x : E, x ^ p = 1) (_hc : ∀ x y : E, ⁅x, y⁆ ∈ Subgroup.center E) : Type _ :=
  BCH p E

section

variable (hp : p.Prime) (hodd : p ≠ 2) (hexp : ∀ x : E, x ^ p = 1)
  (hc : ∀ x y : E, ⁅x, y⁆ ∈ Subgroup.center E)

@[expose] def Lin.val : Lin p E hp hodd hexp hc ≃ E := Equiv.refl _

@[expose] def Lin.mk : E ≃ Lin p E hp hodd hexp hc := Equiv.refl _

@[simp] theorem Lin.val_mk (x : E) : Lin.val hp hodd hexp hc (Lin.mk hp hodd hexp hc x) = x := rfl

theorem Lin.val_injective : Function.Injective (Lin.val hp hodd hexp hc) :=
  (Lin.val hp hodd hexp hc).injective

instance : Zero (Lin p E hp hodd hexp hc) := ⟨OddClassTwoBCH.zero (p := p)⟩

instance : Add (Lin p E hp hodd hexp hc) := ⟨fun x y => OddClassTwoBCH.add (p := p) x y⟩

instance : Neg (Lin p E hp hodd hexp hc) := ⟨fun x => OddClassTwoBCH.neg (p := p) x⟩

instance : AddCommGroup (Lin p E hp hodd hexp hc) where
  add_assoc := BCHAddLaws.add_assoc hp hodd hexp hc
  zero_add := BCHAddLaws.zero_add hp hodd hexp hc
  add_zero := BCHAddLaws.add_zero hp hodd hexp hc
  nsmul n x := BCHAddLaws.nsmul (p := p) n x
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  zsmul := zsmulRec (fun n x => BCHAddLaws.nsmul (p := p) n x)
  neg_add_cancel := BCHAddLaws.neg_add hp hodd hexp hc
  add_comm := BCHAddLaws.add_comm hp hodd hexp hc

@[simp] theorem Lin.val_add (x y : Lin p E hp hodd hexp hc) :
    Lin.val hp hodd hexp hc (x + y) =
      (Lin.val hp hodd hexp hc x * Lin.val hp hodd hexp hc y) *
        (⁅Lin.val hp hodd hexp hc x, Lin.val hp hodd hexp hc y⁆ ^ ((p + 1) / 2))⁻¹ := rfl

@[simp] theorem Lin.val_zero : Lin.val hp hodd hexp hc (0 : Lin p E hp hodd hexp hc) = 1 := rfl

theorem Lin.val_nsmul (n : ℕ) (x : Lin p E hp hodd hexp hc) :
    Lin.val hp hodd hexp hc (n • x) = Lin.val hp hodd hexp hc x ^ n :=
  BCHAddLaws.toGroup_nsmul hp hodd hexp hc n x

theorem Lin.nsmul_eq_zero (x : Lin p E hp hodd hexp hc) : p • x = 0 :=
  Lin.val_injective hp hodd hexp hc (by rw [Lin.val_nsmul, hexp]; rfl)

instance : Module (ZMod p) (Lin p E hp hodd hexp hc) :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  AddCommGroup.zmodModule (n := p) (Lin.nsmul_eq_zero hp hodd hexp hc)

theorem Lin.smul_eq_nsmul (c : ZMod p) (x : Lin p E hp hodd hexp hc) :
    c • x = c.val • x := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]

theorem Lin.val_smul (c : ZMod p) (x : Lin p E hp hodd hexp hc) :
    Lin.val hp hodd hexp hc (c • x) = Lin.val hp hodd hexp hc x ^ c.val := by
  rw [Lin.smul_eq_nsmul, Lin.val_nsmul]

@[expose] def Lin.addHom (φ : MulAut E) : Lin p E hp hodd hexp hc →+ Lin p E hp hodd hexp hc where
  toFun x := Lin.mk hp hodd hexp hc (φ (Lin.val hp hodd hexp hc x))
  map_zero' := by
    apply Lin.val_injective hp hodd hexp hc
    simp
  map_add' x y := by
    apply Lin.val_injective hp hodd hexp hc
    simp [map_commutatorElement]

@[expose] def Lin.linMap (φ : MulAut E) : Lin p E hp hodd hexp hc →ₗ[ZMod p] Lin p E hp hodd hexp hc :=
  (Lin.addHom hp hodd hexp hc φ).toZModLinearMap p

@[simp] theorem Lin.val_linMap (φ : MulAut E) (x : Lin p E hp hodd hexp hc) :
    Lin.val hp hodd hexp hc (Lin.linMap hp hodd hexp hc φ x) = φ (Lin.val hp hodd hexp hc x) := rfl

@[expose] def Lin.linEquiv (φ : MulAut E) : Lin p E hp hodd hexp hc ≃ₗ[ZMod p] Lin p E hp hodd hexp hc :=
  LinearEquiv.ofLinear (Lin.linMap hp hodd hexp hc φ) (Lin.linMap hp hodd hexp hc φ⁻¹)
    (LinearMap.ext fun x => Lin.val_injective hp hodd hexp hc (by simp))
    (LinearMap.ext fun x => Lin.val_injective hp hodd hexp hc (by simp))

@[simp] theorem Lin.val_linEquiv (φ : MulAut E) (x : Lin p E hp hodd hexp hc) :
    Lin.val hp hodd hexp hc (Lin.linEquiv hp hodd hexp hc φ x) = φ (Lin.val hp hodd hexp hc x) :=
  rfl

@[expose] def linearizeAut :
    MulAut E →* (Lin p E hp hodd hexp hc ≃ₗ[ZMod p] Lin p E hp hodd hexp hc) where
  toFun φ := Lin.linEquiv hp hodd hexp hc φ
  map_one' := LinearEquiv.ext fun x => Lin.val_injective hp hodd hexp hc (by simp)
  map_mul' φ ψ := LinearEquiv.ext fun x => Lin.val_injective hp hodd hexp hc (by simp)

end
end BCHModuleAut
end ProofSupport
end CFSG.LocalAnalysis.RankThreeUC
