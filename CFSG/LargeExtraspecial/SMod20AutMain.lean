module

public import CFSG.LargeExtraspecial.SMod20AutReal
public import CFSG.LargeExtraspecial.SMod20AutCount
import CFSG.Fischer.F4
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.LargeExtraspecial.SMod20.Aut

open CFSG.Fischer CFSG.F4.Native CFSG.SmithE Matrix Module

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

@[expose] def semiInv (A : GU0) (φ : F4 ≃+* F4) (y : W) : W :=
  fvec φ.symm (((A : GL (Fin 6) F4)⁻¹ : GL (Fin 6) F4) *ᵥ y)

theorem semiInv_add (A : GU0) (φ : F4 ≃+* F4) (x y : W) :
    semiInv A φ (x + y) = semiInv A φ x + semiInv A φ y := by
  rw [semiInv, mulVec_add, fvec_add]
  rfl

theorem semiInv_smul (A : GU0) (φ : F4 ≃+* F4) (c : F4) (y : W) :
    semiInv A φ (c • y) = φ.symm c • semiInv A φ y := by
  rw [semiInv, mulVec_smul, fvec_smul]
  rfl

theorem semiInv_zero (A : GU0) (φ : F4 ≃+* F4) : semiInv A φ 0 = 0 := by
  rw [semiInv, mulVec_zero, fvec_zero]

theorem semiInv_semiVec (A : GU0) (φ : F4 ≃+* F4) (x : W) : semiInv A φ (semiVec A φ x) = x := by
  rw [semiInv, semiVec, inv_mulVec_mulVec', fvec_symm_fvec]

theorem semiVec_semiInv (A : GU0) (φ : F4 ≃+* F4) (y : W) : semiVec A φ (semiInv A φ y) = y := by
  rw [semiInv, semiVec, fvec_fvec_symm, mulVec_inv_mulVec]

@[expose] def semiSub (A : GU0) (φ : F4 ≃+* F4) (S : Submodule F4 W) : Submodule F4 W where
  carrier := {y | semiInv A φ y ∈ S}
  add_mem' {a b} ha hb := by
    show semiInv A φ (a + b) ∈ S
    rw [semiInv_add]
    exact S.add_mem ha hb
  zero_mem' := by
    show semiInv A φ 0 ∈ S
    rw [semiInv_zero]
    exact S.zero_mem
  smul_mem' c y hy := by
    show semiInv A φ (c • y) ∈ S
    rw [semiInv_smul]
    exact S.smul_mem _ hy

theorem mem_semiSub {A : GU0} {φ : F4 ≃+* F4} {S : Submodule F4 W} {y : W} :
    y ∈ semiSub A φ S ↔ semiInv A φ y ∈ S := Iff.rfl

theorem semiVec_mem_semiSub_iff (A : GU0) (φ : F4 ≃+* F4) (S : Submodule F4 W) (x : W) :
    semiVec A φ x ∈ semiSub A φ S ↔ x ∈ S := by
  rw [mem_semiSub, semiInv_semiVec]

theorem finrank_semiSub (A : GU0) (φ : F4 ≃+* F4) (S : Submodule F4 W) :
    finrank F4 (semiSub A φ S) = finrank F4 S := by
  let j : S ≃+ semiSub A φ S :=
    { toFun := fun x => ⟨semiVec A φ x.1, (semiVec_mem_semiSub_iff A φ S x.1).2 x.2⟩
      invFun := fun y => ⟨semiInv A φ y.1, mem_semiSub.1 y.2⟩
      left_inv := fun x => Subtype.ext (semiInv_semiVec A φ x.1)
      right_inv := fun y => Subtype.ext (semiVec_semiInv A φ y.1)
      map_add' := fun a b => Subtype.ext (semiVec_add A φ a.1 b.1) }
  have h : Module.rank F4 S = Module.rank F4 (semiSub A φ S) := by
    refine rank_eq_of_equiv_equiv (φ : F4 → F4) j φ.bijective ?_
    intro r m
    exact Subtype.ext (semiVec_smul A φ r m.1)
  unfold Module.finrank
  rw [h]

theorem isTIPlane_semiSub (A : GU0) (φ : F4 ≃+* F4) {U : Submodule F4 W} (hU : IsTIPlane U) :
    IsTIPlane (semiSub A φ U) := by
  refine ⟨by rw [finrank_semiSub, hU.1], fun x hx y hy => ?_⟩
  rw [← semiVec_semiInv A φ x, ← semiVec_semiInv A φ y, hermStd_semiVec,
    hU.2 _ (mem_semiSub.1 hx) _ (mem_semiSub.1 hy), map_zero]

@[expose] def planePoints (i : ℕ) : Finset (Fin 693) :=
  Finset.univ.filter fun p => (wMask i).testBit uPts[p.val]! = true

section Pts

theorem mem_planePoints (i : ℕ) (p : Fin 693) : p ∈ planePoints i ↔ uVec p ∈ planeSub i := by
  rw [planePoints, Finset.mem_filter, ← testBit_wMask_iff, codeOf_uVec ptsFacts p.2]
  simp

theorem semiPerm_planes
    (A : GU0) (φ : F4 ≃+* F4) {i : ℕ} (hi : i < 891) :
    ∃ j < 891, ∀ p : Fin 693, p ∈ planePoints i ↔ semiPerm A φ p ∈ planePoints j := by
  obtain ⟨j, hj, hjU⟩ := exists_planeSub_eq (isTIPlane_semiSub A φ (isTIPlane_planeSub hi))
  refine ⟨j, hj, fun p => ?_⟩
  rw [mem_planePoints, mem_planePoints, hjU]
  obtain ⟨c, hc, hcp⟩ := uVec_semiPerm A φ p
  rw [hcp, ← semiVec_mem_semiSub_iff A φ (planeSub i) (uVec p)]
  constructor
  · intro h
    exact (semiSub A φ (planeSub i)).smul_mem c h
  · intro h
    have := (semiSub A φ (planeSub i)).smul_mem c⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end Pts

section AutPerm

@[expose] def IsAutPerm (α : MulAut T46) (π : Equiv.Perm (Fin 693)) : Prop :=
  (∀ g : T46, ((α g : T46) : Equiv.Perm (Fin 693)) = π * g * π⁻¹) ∧
    ∀ p : Fin 693, π * tvP p * π⁻¹ = tvP (π p)

theorem isAutPerm_semiPerm {α : MulAut T46} {A : GU0} {φ : F4 ≃+* F4}
    (h : ∀ g : T46, ((α g : T46) : Equiv.Perm (Fin 693)) = semiPerm A φ * g * (semiPerm A φ)⁻¹) :
    IsAutPerm α (semiPerm A φ) :=
  ⟨h, semiPerm_tvP A φ⟩

theorem exists_isAutPerm (α : MulAut T46) :
    ∃ A : GU0, ∃ φ : F4 ≃+* F4, IsAutPerm α (semiPerm A φ) := by
  obtain ⟨A, φ, h⟩ := exists_semiPerm α
  exact ⟨A, φ, isAutPerm_semiPerm h⟩

theorem IsAutPerm.unique {α : MulAut T46}
    {π π' : Equiv.Perm (Fin 693)} (h : IsAutPerm α π) (h' : IsAutPerm α π') : π = π' := by
  ext p
  have e1 := h.2 p
  have e2 := h'.2 p
  rw [← h.1 ⟨tvP p, tvP_mem p⟩] at e1
  rw [← h'.1 ⟨tvP p, tvP_mem p⟩] at e2
  exact congrArg Fin.val (tvP_injective (e1.symm.trans e2))

theorem IsAutPerm.mul {α β : MulAut T46} {π σ : Equiv.Perm (Fin 693)} (h : IsAutPerm α π)
    (h' : IsAutPerm β σ) : IsAutPerm (α * β) (π * σ) := by
  refine ⟨fun g => ?_, fun p => ?_⟩
  · rw [MulAut.mul_apply, h.1, h'.1, _root_.mul_inv_rev]
    group
  · rw [_root_.mul_inv_rev, Equiv.Perm.mul_apply]
    calc π * σ * tvP p * (σ⁻¹ * π⁻¹) = π * (σ * tvP p * σ⁻¹) * π⁻¹ := by group
      _ = tvP (π (σ p)) := by rw [h'.2, h.2]

theorem isAutPerm_one : IsAutPerm 1 1 :=
  ⟨fun g => by simp, fun p => by simp⟩

@[expose] noncomputable def autPermFun (α : MulAut T46) : Equiv.Perm (Fin 693) :=
  semiPerm (Classical.choose (exists_isAutPerm α))
    (Classical.choose (Classical.choose_spec (exists_isAutPerm α)))

theorem isAutPerm_autPermFun (α : MulAut T46) : IsAutPerm α (autPermFun α) :=
  Classical.choose_spec (Classical.choose_spec (exists_isAutPerm α))

theorem fieldPerm_refl : fieldPerm (RingEquiv.refl F4) = 1 := by
  apply Equiv.ext
  intro p
  apply Fin.ext
  show (ptOf (fvec (RingEquiv.refl F4) (uVec p)) (fvec_uVec_ne_zero _ p)
    (fvec_uVec_iso _ p)).val = p.val
  have : fvec (RingEquiv.refl F4) (uVec p) = uVec p := by
    funext i
    rfl
  rw [ptOf_val, this, ptIdx_uVec ptsFacts p.2]

theorem exists_semiPerm_eq (g : T46) :
    ∃ A : GU0, (g : Equiv.Perm (Fin 693)) = semiPerm A (RingEquiv.refl F4) := by
  have hg : (g : Equiv.Perm (Fin 693)) ∈ piSU.range := by rw [range_piSU]; exact g.2
  obtain ⟨s, hs⟩ := hg
  refine ⟨Subgroup.inclusion SU0_le_GU0 s, ?_⟩
  rw [semiPerm, fieldPerm_refl, mul_one, ← hs]
  rfl

end AutPerm

end CFSG.LargeExtraspecial.SMod20.Aut

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer CFSG.F4.Native CFSG.SmithE Matrix Module Aut

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

section Rep

@[expose] noncomputable def autPerm : MulAut T46 →* Equiv.Perm (Fin 693) where
  toFun := autPermFun
  map_one' := (isAutPerm_autPermFun 1).unique isAutPerm_one
  map_mul' α β :=
    (isAutPerm_autPermFun (α * β)).unique
      ((isAutPerm_autPermFun α).mul (isAutPerm_autPermFun β))

theorem isAutPerm_autPerm (α : MulAut T46) : IsAutPerm α (autPerm α) := isAutPerm_autPermFun α

theorem autPerm_conj_apply (α : MulAut T46) (g : T46) :
    ((α g : T46) : Equiv.Perm (Fin 693)) = autPerm α * g * (autPerm α)⁻¹ :=
  (isAutPerm_autPerm α).1 g

theorem autPerm_tvP (α : MulAut T46) (p : Fin 693) :
    ((α ⟨tvP p, tvP_mem p⟩ : T46) : Equiv.Perm (Fin 693)) = tvP (autPerm α p) := by
  rw [autPerm_conj_apply]
  exact (isAutPerm_autPerm α).2 p

theorem exists_autPerm_eq_semiPerm (α : MulAut T46) :
    ∃ A : GU0, ∃ φ : F4 ≃+* F4, autPerm α = semiPerm A φ := by
  obtain ⟨A, φ, h⟩ := exists_isAutPerm α
  exact ⟨A, φ, (isAutPerm_autPerm α).unique h⟩

theorem autPerm_mem_normalizer (α : MulAut T46) :
    autPerm α ∈ Subgroup.normalizer (T46 : Set (Equiv.Perm (Fin 693))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← autPerm_conj_apply α ⟨h, hh⟩]
    exact (α ⟨h, hh⟩).2
  · intro hh
    obtain ⟨g, hg⟩ := α.surjective ⟨_, hh⟩
    have e := autPerm_conj_apply α g
    rw [hg] at e
    have e' : h = (g : Equiv.Perm (Fin 693)) := by
      have := congrArg (fun x => (autPerm α)⁻¹ * x * autPerm α) e
      simpa [mul_assoc] using this
    rw [e']
    exact g.2

theorem autPerm_planes (α : MulAut T46) {i : ℕ} (hi : i < 891) :
    ∃ j < 891, ∀ p : Fin 693, p ∈ planePoints i ↔ autPerm α p ∈ planePoints j := by
  obtain ⟨A, φ, h⟩ := exists_autPerm_eq_semiPerm α
  rw [h]
  exact semiPerm_planes A φ hi

theorem autPerm_injective : Function.Injective (autPerm : MulAut T46 →* Equiv.Perm (Fin 693)) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  ext g
  rw [autPerm_conj_apply, hα]
  simp

theorem autPerm_conj (g : T46) : autPerm (MulAut.conj g) = g := by
  obtain ⟨A, hA⟩ := exists_semiPerm_eq g
  refine (isAutPerm_autPerm _).unique ⟨fun h => ?_, fun p => ?_⟩
  · simp
  · rw [hA]
    exact semiPerm_tvP A _ p

end Rep

end CFSG.LargeExtraspecial.SMod20
