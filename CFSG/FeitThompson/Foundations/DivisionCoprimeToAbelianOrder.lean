module

public import Mathlib.Data.ZMod.Basic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {A : Type*} [AddCommGroup A] {m : ℕ}

noncomputable def nsmulCoprimeAddAut (h : m.Coprime (Nat.card A)) : AddAut A :=
  { nsmulCoprime h.symm with map_add' := fun a b => by simp [nsmulCoprime_apply] }

@[simp]
theorem nsmulCoprimeAddAut_apply (h : m.Coprime (Nat.card A)) (a : A) :
    nsmulCoprimeAddAut h a = m • a :=
  nsmulCoprime_apply h.symm a

theorem coe_nsmulCoprimeAddAut (h : m.Coprime (Nat.card A)) :
    ((nsmulCoprimeAddAut h : AddAut A) : A →+ A) = nsmulAddMonoidHom m := by
  ext a; simp

theorem nsmulCoprimeAddAut_symm_apply (h : m.Coprime (Nat.card A)) (a : A) :
    (nsmulCoprimeAddAut h).symm a = (Nat.card A).gcdB m • a :=
  nsmulCoprime_symm_apply h.symm a

@[simp]
theorem nsmul_nsmulCoprimeAddAut_symm (h : m.Coprime (Nat.card A)) (a : A) :
    m • (nsmulCoprimeAddAut h).symm a = a := by
  have h2 := (nsmulCoprimeAddAut h).apply_symm_apply a
  rwa [nsmulCoprimeAddAut_apply] at h2

@[simp]
theorem nsmulCoprimeAddAut_symm_nsmul (h : m.Coprime (Nat.card A)) (a : A) :
    (nsmulCoprimeAddAut h).symm (m • a) = a := by
  have h2 := (nsmulCoprimeAddAut h).symm_apply_apply a
  rwa [nsmulCoprimeAddAut_apply] at h2

theorem nsmulCoprimeAddAut_symm_apply_eq_zmodInv_val_nsmul (h : m.Coprime (Nat.card A)) (a : A) :
    (nsmulCoprimeAddAut h).symm a = ((m : ZMod (Nat.card A))⁻¹.val) • a := by
  refine (Nat.Coprime.nsmul_right_bijective (G := A) (n := m) h.symm).injective ?_
  simp [nsmul_zmod_val_inv_nsmul (α := A) (n := m) h.symm a]

theorem nsmulCoprimeAddAut_symm_map_add (h : m.Coprime (Nat.card A)) (a b : A) :
    (nsmulCoprimeAddAut h).symm (a + b)
      = (nsmulCoprimeAddAut h).symm a + (nsmulCoprimeAddAut h).symm b :=
  map_add _ a b

theorem nsmulCoprimeAddAut_symm_comm (h : m.Coprime (Nat.card A)) (f : A →+ A) (a : A) :
    (nsmulCoprimeAddAut h).symm (f a) = f ((nsmulCoprimeAddAut h).symm a) := by
  rw [nsmulCoprimeAddAut_symm_apply, nsmulCoprimeAddAut_symm_apply, map_zsmul]

theorem nsmulCoprimeAddAut_symm_comp (h : m.Coprime (Nat.card A)) (f : A →+ A) :
    ((nsmulCoprimeAddAut h).symm : A →+ A).comp f
      = f.comp ((nsmulCoprimeAddAut h).symm : A →+ A) :=
  AddMonoidHom.ext fun a => nsmulCoprimeAddAut_symm_comm h f a

end

end CFSG.FeitThompson
