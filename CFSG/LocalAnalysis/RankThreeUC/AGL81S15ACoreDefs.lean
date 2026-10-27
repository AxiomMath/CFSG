module

public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open Equiv

@[expose] def permAct (C : Type) [CommGroup C] (m : ℕ) :
    Perm (Fin m) →* MulAut (Fin m → C) where
  toFun σ :=
    { toFun := fun t => t ∘ σ.symm
      invFun := fun t => t ∘ σ
      left_inv := fun t => by ext i; simp
      right_inv := fun t => by ext i; simp
      map_mul' := fun s t => rfl }
  map_one' := by ext t i; rfl
  map_mul' := fun σ τ => by ext t i; rfl

abbrev Mon (C : Type) [CommGroup C] (m : ℕ) : Type :=
  (Fin m → C) ⋊[permAct C m] Perm (Fin m)

variable {C : Type} [CommGroup C] {m : ℕ}

instance [Finite C] : Finite (Mon C m) :=
  Finite.of_equiv _ (SemidirectProduct.equivProd (N := Fin m → C) (G := Perm (Fin m))
    (φ := permAct C m)).symm

theorem permAct_apply (σ : Perm (Fin m)) (t : Fin m → C) (i : Fin m) :
    permAct C m σ t i = t (σ⁻¹ i) := rfl

@[expose] def monT (t : Fin m → C) : Mon C m := SemidirectProduct.inl t

@[expose] def monS (σ : Perm (Fin m)) : Mon C m := SemidirectProduct.inr σ

@[expose] def monScalar (C : Type) [CommGroup C] (m : ℕ) : C →* Mon C m :=
  SemidirectProduct.inl.comp (Pi.constMonoidHom (Fin m) C)

@[expose] def monPerm : Mon C m →* Perm (Fin m) := SemidirectProduct.rightHom

@[expose] def entryProd (C : Type) [CommGroup C] (m : ℕ) : (Fin m → C) →* C :=
  MonoidHom.mk' (fun t => ∏ i, t i) fun _ _ => Finset.prod_mul_distrib

@[expose] def monDet : Mon C m →* C :=
  SemidirectProduct.lift (entryProd C m) 1 fun σ => by
    ext t
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul,
      inv_one, mul_one, MonoidHom.one_apply]
    exact Equiv.prod_comp σ.symm t

theorem monDet_monT (t : Fin m → C) : monDet (monT t) = ∏ i, t i := by
  simp [monDet, monT, entryProd]

theorem monDet_monS (σ : Perm (Fin m)) : monDet (monS (C := C) σ) = 1 := by
  simp [monDet, monS]

theorem monPerm_monT (t : Fin m → C) : monPerm (monT t) = 1 := by
  simp [monPerm, monT]

theorem monPerm_monS (σ : Perm (Fin m)) : monPerm (monS (C := C) σ) = σ := by
  simp [monPerm, monS]

theorem monScalar_apply (z : C) : monScalar C m z = monT (fun _ => z) := rfl

theorem monT_mul (s t : Fin m → C) : monT (s * t) = monT s * monT t := by
  simp [monT]

theorem monS_inv (σ : Perm (Fin m)) : monS (C := C) σ⁻¹ = (monS σ)⁻¹ :=
  map_inv SemidirectProduct.inr σ

theorem monS_mul_monT_mul_monS_inv (σ : Perm (Fin m)) (t : Fin m → C) :
    monS σ * monT t * (monS σ)⁻¹ = monT (t ∘ σ.symm) := by
  have h := (SemidirectProduct.inl_aut (φ := permAct C m) σ t).symm
  have e : permAct C m σ t = t ∘ σ.symm := rfl
  rw [e] at h
  unfold monS monT
  rw [← map_inv SemidirectProduct.inr σ]
  exact h

theorem mon_eq_monT_mul_monS (x : Mon C m) : x = monT x.left * monS x.right :=
  (SemidirectProduct.inl_left_mul_inr_right x).symm

@[expose] def Ωsc (r m : ℕ) (C : Type) [CommGroup C] : Subgroup C where
  carrier := {z | ∃ s : Fin m → C, ∏ i, s i = 1 ∧ ∀ i, s i ^ r = z}
  mul_mem' := by
    rintro a b ⟨s, hs, ha⟩ ⟨s', hs', hb⟩
    refine ⟨s * s', ?_, fun i => ?_⟩
    · simp [Finset.prod_mul_distrib, hs, hs']
    · simp [mul_pow, ha i, hb i]
  one_mem' := ⟨fun _ => 1, by simp, fun _ => by simp⟩
  inv_mem' := by
    rintro a ⟨s, hs, ha⟩
    exact ⟨s⁻¹, by simp [Finset.prod_inv_distrib, hs], fun i => by simp [inv_pow, ha i]⟩

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
