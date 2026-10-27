module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Perm

public section

namespace CFSG.OddStandard.AltStdSmall4.N0

open Equiv Equiv.Perm Subgroup

section Fin8

theorem xr_eq_xor (v w : Fin 8) : xr v w = v ^^^ w :=
  Fin.ext (Nat.mod_eq_of_lt (xor_lt_eight v.2 w.2)).symm

@[expose] def mPerm : Perm (Fin 8) where
  toFun := ![0, 2, 4, 6, 3, 1, 7, 5]
  invFun := ![0, 5, 1, 4, 2, 7, 3, 6]
  left_inv j := by revert j; decide
  right_inv j := by revert j; decide

@[expose] def IsXorAdd (f : Perm (Fin 8)) : Prop := ∀ i j : Fin 8, f (i ^^^ j) = f i ^^^ f j

theorem mPerm_isXorAdd : IsXorAdd mPerm := by
  unfold IsXorAdd
  decide

theorem sign_mPerm : sign mPerm = 1 := by decide

theorem IsXorAdd.mul {f g : Perm (Fin 8)} (hf : IsXorAdd f) (hg : IsXorAdd g) :
    IsXorAdd (f * g) := by
  intro i j
  rw [Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, hg, hf]

private theorem app_inv (f : Perm (Fin 8)) (x : Fin 8) : f (f⁻¹ x) = x := by
  rw [Perm.coe_inv, Equiv.apply_symm_apply]

theorem IsXorAdd.inv {f : Perm (Fin 8)} (hf : IsXorAdd f) : IsXorAdd f⁻¹ := by
  intro i j
  apply f.injective
  rw [hf, app_inv, app_inv, app_inv]

theorem exists_mPerm_pow_eq (i j : Fin 8) (hi : i ≠ 0) (hj : j ≠ 0) :
    ∃ k : ℕ, (mPerm ^ k) i = j := by
  have : ∀ i j : Fin 8, i ≠ 0 → j ≠ 0 → ∃ k : Fin 7, (mPerm ^ (k : ℕ)) i = j := by decide
  obtain ⟨k, hk⟩ := this i j hi hj
  exact ⟨k, hk⟩

theorem exists_xor_mPerm_eq (j : Fin 8) : ∃ i : Fin 8, i ^^^ mPerm i = j := by
  revert j
  decide

theorem xor_mPerm_eq_zero (i : Fin 8) : i ^^^ mPerm i = 0 ↔ i = 0 := by
  revert i
  decide

theorem eq_zero_of_mPerm_six (a : Fin 8)
    (h : (mPerm ^ 6) a = (mPerm ^ 2) a ^^^ mPerm a) : a = 0 := by
  revert a
  decide

end Fin8

section Ext

variable {n : ℕ}

@[expose] def e8 (hn : 8 ≤ n) : Fin 8 ≃ {x : Fin n // x.val < 8} where
  toFun i := ⟨⟨i.val, by omega⟩, i.isLt⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def ext8Hom (hn : 8 ≤ n) : Perm (Fin 8) →* Perm (Fin n) := extendDomainHom (e8 hn)

@[expose] def ext8 (hn : 8 ≤ n) (f : Perm (Fin 8)) : Perm (Fin n) := ext8Hom hn f

theorem ext8_apply_lt (hn : 8 ≤ n) (f : Perm (Fin 8)) (j : Fin 8) :
    ext8 hn f ⟨j.val, by omega⟩ = ⟨(f j).val, by omega⟩ := by
  have := Perm.extendDomain_apply_image f (e8 hn) j
  exact this

theorem ext8_apply_ge (hn : 8 ≤ n) (f : Perm (Fin 8)) {x : Fin n} (hx : 8 ≤ x.val) :
    ext8 hn f x = x :=
  Perm.extendDomain_apply_not_subtype f (e8 hn) (by omega)

theorem sign_ext8 (hn : 8 ≤ n) (f : Perm (Fin 8)) : sign (ext8 hn f) = sign f :=
  sign_extendDomain f (e8 hn)

theorem ext8_injective (hn : 8 ≤ n) : Function.Injective (ext8 hn) :=
  extendDomainHom_injective (e8 hn)

private theorem ext8_mul_tr (hn : 8 ≤ n) {f : Perm (Fin 8)} (hf : IsXorAdd f) (v : Fin 8) :
    ext8 hn f * tr hn v = tr hn (f v) * ext8 hn f := by
  have hval : ∀ y : Fin n, ∀ hy : y.val < 8, (ext8 hn f y).val = (f ⟨y.val, hy⟩).val :=
    fun y hy => congrArg Fin.val (ext8_apply_lt hn f ⟨y.val, hy⟩)
  refine Equiv.ext fun x => Fin.ext ?_
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hx : x.val < 8
  · have h8 : (tr hn v x).val < 8 := val_tr_lt hn v hx
    have h8' : (ext8 hn f x).val < 8 := by
      rw [hval x hx]
      exact (f _).2
    have h1 : (⟨(tr hn v x).val, h8⟩ : Fin 8) = ⟨x.val, hx⟩ ^^^ v :=
      (Fin.ext (val_tr_of_lt hn v hx)).trans (xr_eq_xor _ v)
    rw [hval _ h8, val_tr_of_lt hn (f v) h8', hval x hx, h1, hf]
    exact congrArg Fin.val (xr_eq_xor _ _).symm
  · push Not at hx
    rw [tr_of_ge hn v hx, ext8_apply_ge hn f hx, tr_of_ge hn _ hx]

theorem ext8_conj_tr (hn : 8 ≤ n) {f : Perm (Fin 8)} (hf : IsXorAdd f) (v : Fin 8) :
    ext8 hn f * tr hn v * (ext8 hn f)⁻¹ = tr hn (f v) := by
  rw [ext8_mul_tr hn hf, mul_inv_cancel_right]

@[expose] def extA (hn : 8 ≤ n) (f : Perm (Fin 8)) (hf : sign f = 1) :
    alternatingGroup (Fin n) :=
  ⟨ext8 hn f, by rw [Perm.mem_alternatingGroup, sign_ext8, hf]⟩

theorem extA_conj_tr (hn : 8 ≤ n) {f : Perm (Fin 8)} (hf : IsXorAdd f) (hs : sign f = 1)
    (v : Fin 8) : extA hn f hs * ⟨tr hn v, tr_mem_alternatingGroup hn v⟩ * (extA hn f hs)⁻¹ =
      ⟨tr hn (f v), tr_mem_alternatingGroup hn (f v)⟩ :=
  Subtype.ext (ext8_conj_tr hn hf v)

@[expose] def sbA (hn : 8 ≤ n) : alternatingGroup (Fin n) := extA hn mPerm sign_mPerm

theorem sbA_conj_tr (hn : 8 ≤ n) (v : Fin 8) :
    sbA hn * ⟨tr hn v, tr_mem_alternatingGroup hn v⟩ * (sbA hn)⁻¹ =
      ⟨tr hn (mPerm v), tr_mem_alternatingGroup hn (mPerm v)⟩ :=
  extA_conj_tr hn mPerm_isXorAdd sign_mPerm v

end Ext

end CFSG.OddStandard.AltStdSmall4.N0
