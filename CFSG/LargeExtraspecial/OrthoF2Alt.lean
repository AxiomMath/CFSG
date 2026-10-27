module

public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

@[expose] def fixPerpGroup (q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {t | t ∈ orthogonalGroup q ∧
    (∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin U, t x = x) ∧ ∀ v, t v - v ∈ U}
  mul_mem' := by
    rintro s t ⟨hs, hs1, hs2⟩ ⟨ht, ht1, ht2⟩
    refine ⟨mul_mem hs ht, fun x hx => by rw [LinearEquiv.mul_apply, ht1 x hx, hs1 x hx],
      fun v => ?_⟩
    have e : (s * t) v - v = (s (t v) - t v) + (t v - v) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [e]
    exact Submodule.add_mem _ (hs2 _) (ht2 v)
  one_mem' := ⟨one_mem _, fun x _ => rfl, fun v => by simp⟩
  inv_mem' := by
    rintro t ⟨ht, ht1, ht2⟩
    refine ⟨inv_mem ht, fun x hx => ?_, fun v => ?_⟩
    · conv_lhs => rw [← ht1 x hx]
      exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' t x
    · have e : t⁻¹ v - v = -(t (t⁻¹ v) - t⁻¹ v) := by
        rw [apply_inv_apply]
        abel
      rw [e]
      exact neg_mem (ht2 _)

theorem mem_fixPerpGroup {U : Submodule (ZMod 2) V} {t : V ≃ₗ[ZMod 2] V} :
    t ∈ fixPerpGroup q U ↔ t ∈ orthogonalGroup q ∧
      (∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin U, t x = x) ∧ ∀ v, t v - v ∈ U :=
  Iff.rfl

@[expose] def altFormsModPerp (q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V) :
    AddSubgroup (LinearMap.BilinForm (ZMod 2) V) where
  carrier := {β | β.IsAlt ∧ ∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin U, ∀ y, β x y = 0}
  add_mem' := by
    rintro β γ ⟨hβ, hβ'⟩ ⟨hγ, hγ'⟩
    exact ⟨hβ.add hγ, fun x hx y => by
      rw [LinearMap.add_apply, LinearMap.add_apply, hβ' x hx, hγ' x hx, add_zero]⟩
  zero_mem' := ⟨fun x => by simp, fun x _ y => by simp⟩
  neg_mem' := by
    rintro β ⟨hβ, hβ'⟩
    exact ⟨hβ.neg, fun x hx y => by
      rw [LinearMap.neg_apply, LinearMap.neg_apply, hβ' x hx, neg_zero]⟩

theorem mem_altFormsModPerp {U : Submodule (ZMod 2) V} {β : LinearMap.BilinForm (ZMod 2) V} :
    β ∈ altFormsModPerp q U ↔
      β.IsAlt ∧ ∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin U, ∀ y, β x y = 0 :=
  Iff.rfl

@[expose] noncomputable def commForm (q : QuadraticForm (ZMod 2) V) (t : V ≃ₗ[ZMod 2] V) :
    LinearMap.BilinForm (ZMod 2) V :=
  q.polarBilin ∘ₗ ((t : V →ₗ[ZMod 2] V) - 1)

theorem commForm_apply (t : V ≃ₗ[ZMod 2] V) (x y : V) :
    commForm q t x y = polar q (t x - x) y := by
  simp [commForm]

namespace OrthoF2

theorem le_orthogonal_of_totallySingular {U : Submodule (ZMod 2) V} (hU : ∀ u ∈ U, q u = 0) :
    U ≤ LinearMap.BilinForm.orthogonal q.polarBilin U := by
  intro u hu
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  have h := hU (n + u) (Submodule.add_mem _ hn hu)
  rw [map_add_eq, hU n hn, hU u hu, zero_add, zero_add] at h
  rwa [polarBilin_apply_apply]

theorem apply_apply_sub_of_mem_fixPerpGroup {U : Submodule (ZMod 2) V} (hU : ∀ u ∈ U, q u = 0)
    {s t : V ≃ₗ[ZMod 2] V} (hs : s ∈ fixPerpGroup q U) (ht : t ∈ fixPerpGroup q U) (v : V) :
    s (t v) - t v = s v - v := by
  have hd : s (t v - v) = t v - v := hs.2.1 _ (le_orthogonal_of_totallySingular hU (ht.2.2 v))
  have e : t v = v + (t v - v) := by abel
  rw [e, map_add, hd]
  abel

end OrthoF2

theorem isElementaryAbelian_fixPerpGroup {U : Submodule (ZMod 2) V} (hU : ∀ u ∈ U, q u = 0) :
    IsElementaryAbelian 2 (fixPerpGroup q U) := by
  have key : ∀ s t : fixPerpGroup q U, ∀ v,
      ((s * t : fixPerpGroup q U) : V ≃ₗ[ZMod 2] V) v =
        (s : V ≃ₗ[ZMod 2] V) v + ((t : V ≃ₗ[ZMod 2] V) v - v) := by
    intro s t v
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply,
      ← sub_add_cancel ((s : V ≃ₗ[ZMod 2] V) ((t : V ≃ₗ[ZMod 2] V) v))
        ((t : V ≃ₗ[ZMod 2] V) v),
      apply_apply_sub_of_mem_fixPerpGroup hU s.2 t.2]
    abel
  have hcomm : ∀ s t : fixPerpGroup q U, s * t = t * s := by
    intro s t
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    rw [key, key]
    abel
  have hsq : ∀ t : fixPerpGroup q U, t ^ 2 = 1 := by
    intro t
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    rw [pow_two, key, OneMemClass.coe_one, LinearEquiv.coe_one, id, vec_sub, ← add_assoc,
      vec_add_self, zero_add]
  exact { is_comm := ⟨hcomm⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }

theorem fixPerpGroup_mulEquiv [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {U : Submodule (ZMod 2) V} (hU : ∀ u ∈ U, q u = 0) :
    ∃ e : fixPerpGroup q U ≃* Multiplicative (altFormsModPerp q U),
      ∀ t, ((Multiplicative.toAdd (e t) : altFormsModPerp q U) :
        LinearMap.BilinForm (ZMod 2) V) = commForm q t := by
  have hUU := le_orthogonal_of_totallySingular hU
  have hmem : ∀ t : fixPerpGroup q U, commForm q t ∈ altFormsModPerp q U := by
    rintro ⟨t, ht, ht1, ht2⟩
    refine ⟨fun x => ?_, fun x hx y => ?_⟩
    · change commForm q t x x = 0
      rw [commForm_apply, QuadraticMap.polar_sub_left, polar_self_eq_zero, sub_zero,
        ← map_sub_eq_polar ht]
      exact hU _ (ht2 x)
    · rw [commForm_apply, ht1 x hx, sub_self, polar_zero_left]
  let Ψ : fixPerpGroup q U →* Multiplicative (altFormsModPerp q U) :=
    { toFun := fun t => Multiplicative.ofAdd ⟨commForm q t, hmem t⟩
      map_one' := by
        change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
        congr 1
        refine Subtype.ext (LinearMap.ext₂ fun x y => ?_)
        change commForm q 1 x y = 0
        rw [commForm_apply, LinearEquiv.coe_one, id, sub_self, polar_zero_left]
      map_mul' := fun s t => by
        change Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
        congr 1
        refine Subtype.ext (LinearMap.ext₂ fun x y => ?_)
        change commForm q ((s : V ≃ₗ[ZMod 2] V) * t) x y = commForm q s x y + commForm q t x y
        rw [commForm_apply, commForm_apply, commForm_apply, LinearEquiv.mul_apply,
          ← polar_add_left]
        congr 1
        rw [← apply_apply_sub_of_mem_fixPerpGroup hU s.2 t.2 x]
        abel }
  have hinj : Function.Injective Ψ := by
    intro s t hst
    have h := congrArg (fun y => ((Multiplicative.toAdd y : altFormsModPerp q U) :
      LinearMap.BilinForm (ZMod 2) V)) hst
    change commForm q s = commForm q t at h
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    have h0 : (s : V ≃ₗ[ZMod 2] V) x - x - ((t : V ≃ₗ[ZMod 2] V) x - x) = 0 := by
      refine hq.1 _ fun y => ?_
      rw [polarBilin_apply_apply, QuadraticMap.polar_sub_left, ← commForm_apply,
        ← commForm_apply, h, sub_self]
    rw [sub_sub_sub_cancel_right, sub_eq_zero] at h0
    exact h0
  have hsurj : Function.Surjective Ψ := by
    intro y
    obtain ⟨⟨β, hβalt, hβperp⟩, rfl⟩ : ∃ z : altFormsModPerp q U, Multiplicative.ofAdd z = y :=
      ⟨Multiplicative.toAdd y, rfl⟩
    let D := LinearMap.BilinForm.toDual q.polarBilin hq
    let φ : V →ₗ[ZMod 2] V := D.symm.toLinearMap ∘ₗ β
    have hφ : ∀ x y, polar q (φ x) y = β x y := fun x y => by
      rw [← polarBilin_apply_apply]
      exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hq) (β x) y
    have hβsymm : ∀ x y, β x y = β y x := fun x y => by
      rw [← hβalt.neg_eq, zmod2_neg]
    have hφU : ∀ x, φ x ∈ U := by
      intro x
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hq (isRefl_polarBilin q) U,
        LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [polarBilin_apply_apply, polar_comm, hφ, hβsymm, hβperp n hn]
    have hφperp : ∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin U, φ x = 0 := by
      intro x hx
      refine hq.1 _ fun y => ?_
      rw [polarBilin_apply_apply, hφ, hβperp x hx]
    have hφφ : ∀ x, φ (φ x) = 0 := fun x => hφperp _ (hUU (hφU x))
    let T : V →ₗ[ZMod 2] V := LinearMap.id + φ
    have hinv : Function.Involutive T := by
      intro x
      change (x + φ x) + φ (x + φ x) = x
      rw [map_add, hφφ, add_zero, add_assoc, vec_add_self, add_zero]
    let t : V ≃ₗ[ZMod 2] V := LinearEquiv.ofInvolutive T hinv
    have htv : ∀ x, t x = x + φ x := fun x => rfl
    have ht : t ∈ fixPerpGroup q U := by
      refine ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_, fun x hx => ?_,
        fun v => ?_⟩
      · rw [htv, map_add_eq, hU _ (hφU x), polar_comm, hφ, hβalt.self_eq_zero, add_zero,
          add_zero]
      · rw [htv, hφperp x hx, add_zero]
      · rw [htv, add_sub_cancel_left]
        exact hφU v
    refine ⟨⟨t, ht⟩, ?_⟩
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    congr 1
    refine Subtype.ext (LinearMap.ext₂ fun x y => ?_)
    change commForm q t x y = β x y
    rw [commForm_apply, htv, add_sub_cancel_left, hφ]
  exact ⟨MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, fun t => rfl⟩

end CFSG.LargeExtraspecial
