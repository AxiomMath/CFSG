module

public import CFSG.LargeExtraspecial.S6Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G}

theorem add_self_zmod2 {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] (v : U) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

variable (S) in
@[expose] def flagGroup (X Y : Submodule (ZMod 2) S.Qt) : Subgroup S.O where
  carrier := {x | (∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ∧
    (∀ w ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X) ∧
    ∀ u, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Y}
  mul_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨fun v hv => ?_, fun w hw => ?_, fun u => ?_⟩
    · change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v
      rw [hy1 v hv, hx1 v hv]
    · change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - w ∈ X
      have hyw := hy2 w hw
      have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - w =
          (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) +
            ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by rw [map_sub]; abel
      rw [e, hx1 _ hyw]
      exact X.add_mem hyw (hx2 w hw)
    · change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u) - u ∈ Y
      have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u) - u =
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u) -
            (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u) + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by abel
      rw [e]
      exact Y.add_mem (hx3 _) (hy3 u)
  one_mem' := ⟨fun v _ => rfl, fun w _ => by simp, fun u => by simp⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    have hmem : ∀ u, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u =
        -((x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) -
          ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := fun u => by
      rw [apply_inv_apply_O]; abel
    refine ⟨fun v hv => ?_, fun w hw => ?_, fun u => ?_⟩
    · conv_lhs => rw [← hx1 v hv]
      exact inv_apply_apply_O x v
    · have hw' : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Y := by
        have h1 := hx3 (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w)
        rw [apply_inv_apply_O] at h1
        have e : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
            w - (w - ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by abel
        rw [e]
        exact Y.sub_mem hw h1
      rw [hmem]
      exact X.neg_mem (hx2 _ hw')
    · rw [hmem]
      exact Y.neg_mem (hx3 _)

theorem mem_flagGroup {X Y : Submodule (ZMod 2) S.Qt} {x : S.O} :
    x ∈ flagGroup S X Y ↔ (∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ∧
      (∀ w ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X) ∧
      ∀ u, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Y :=
  Iff.rfl

variable (S) in
@[expose] def flagCenter (X Y : Submodule (ZMod 2) S.Qt) : Subgroup S.O where
  carrier := {x | (∀ w ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) ∧
    ∀ u, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ X}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun w hw => ?_, fun u => ?_⟩
    · change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w
      rw [hy1 w hw, hx1 w hw]
    · change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u) - u ∈ X
      have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u) - u =
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u) -
            (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u) + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by abel
      rw [e]
      exact X.add_mem (hx2 _) (hy2 u)
  one_mem' := ⟨fun w _ => rfl, fun u => by simp⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨fun w hw => ?_, fun u => ?_⟩
    · conv_lhs => rw [← hx1 w hw]
      exact inv_apply_apply_O x w
    · have e : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u =
          -((x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) -
            ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := by
        rw [apply_inv_apply_O]; abel
      rw [e]
      exact X.neg_mem (hx2 _)

section Flag

variable {X Y : Submodule (ZMod 2) S.Qt} (hXY : X ≤ Y)
include hXY

theorem comm_mem_flagCenter {x y : S.O} (hx : x ∈ flagGroup S X Y) (hy : y ∈ flagGroup S X Y) :
    x * y * x⁻¹ * y⁻¹ ∈ flagCenter S X Y := by
  have hxi := inv_mem hx
  have hyi := inv_mem hy
  have key : ∀ u', (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u') -
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u') =
      ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u') -
        ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u')) -
      ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u') -
        ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u')) := fun u' => by
    rw [map_sub, map_sub]; abel
  have hcomm : ∀ u, ((x * y * x⁻¹ * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u))) -
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u))) :=
    fun u => by
      rw [apply_inv_apply_O, apply_inv_apply_O]
      rfl
  refine ⟨fun w hw => ?_, fun u => ?_⟩
  · set u' := ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w)
    have hu' : u' ∈ Y := by
      have h1 := hyi.2.1 w hw
      have hw1 : ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Y := by
        have e : ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
            (((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) + w := by abel
        rw [e]
        exact Y.add_mem (hXY h1) hw
      have h2 := hxi.2.1 _ hw1
      have e : u' = (u' - ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) +
          ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by abel
      rw [e]
      exact Y.add_mem (hXY h2) hw1
    have h0 := hcomm w
    rw [key, hx.1 _ (hy.2.1 _ hu'), hy.1 _ (hx.2.1 _ hu'), sub_self, sub_self, sub_self]
      at h0
    exact sub_eq_zero.mp h0
  · rw [hcomm, key]
    set u' := ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)
    exact X.sub_mem (hx.2.1 _ (hy.2.2 u')) (hy.2.1 _ (hx.2.2 u'))

omit hXY in
theorem commute_of_mem_flagCenter {c x : S.O} (hc : c ∈ flagCenter S X Y)
    (hx : x ∈ flagGroup S X Y) : c * x = x * c := by
  refine Subtype.ext (LinearEquiv.ext fun u => ?_)
  change (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u) =
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) u)
  have h1 := hc.2 u
  have h2 := hx.2.2 u
  have e1 : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u) =
      (c : S.Qt ≃ₗ[ZMod 2] S.Qt) u + (c : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by rw [map_sub]; abel
  have e2 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) u) =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u + (x : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by rw [map_sub]; abel
  rw [e1, e2, hc.1 _ h2, hx.1 _ h1]
  abel

theorem commutator_commutator_eq_bot_of_le_flagGroup {E : Subgroup S.O}
    (hE : E ≤ flagGroup S X Y) : ⁅⁅E, E⁆, E⁆ = ⊥ := by
  have h1 : ⁅E, E⁆ ≤ flagCenter S X Y := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact comm_mem_flagCenter hXY (hE hx) (hE hy)
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro c hc x hx
  rw [Subgroup.mem_bot, commutatorElement_def, commute_of_mem_flagCenter (h1 hc) (hE hx),
    mul_inv_cancel_right, mul_inv_cancel]

omit hXY in
theorem pow_four_eq_one_of_mem_flagGroup {x : S.O} (hx : x ∈ flagGroup S X Y) : x ^ 4 = 1 := by
  set p : S.Qt → S.Qt := fun u => (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u with hp
  have hpadd : ∀ u v, p (u + v) = p u + p v := fun u v => by
    simp only [hp, map_add]; abel
  have hppp : ∀ u, p (p (p u)) = 0 := fun u => by
    have h1 : p u ∈ Y := hx.2.2 u
    have h2 : p (p u) ∈ X := hx.2.1 _ h1
    simp only [hp] at h2 ⊢
    rw [hx.1 _ h2, sub_self]
  have hx2 : ∀ u, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = u + p (p u) :=
    fun u => by
      have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u) =
          (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u + p ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := by
        simp only [hp]; abel
      rw [e, show (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u + p u by simp only [hp]; abel, hpadd]
      have := add_self_zmod2 (p u)
      calc u + p u + (p u + p (p u)) = u + (p u + p u) + p (p u) := by abel
        _ = u + p (p u) := by rw [this, add_zero]
  refine Subtype.ext (LinearEquiv.ext fun u => ?_)
  change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt)
    ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u))) = u
  rw [hx2, hx2, hpadd, hpadd, hppp, add_zero, add_assoc, add_self_zmod2, add_zero]

omit hXY in
theorem isPGroup_of_le_flagGroup {E : Subgroup S.O} (hE : E ≤ flagGroup S X Y) :
    IsPGroup 2 E := fun x =>
  ⟨2, Subtype.ext (by
    rw [SubmonoidClass.coe_pow, Subgroup.coe_one]
    exact pow_four_eq_one_of_mem_flagGroup (hE x.2))⟩

end Flag

theorem mem_flagGroup_of_fix {g : G} {t τ : S.O}
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hτW : ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    τ ∈ flagGroup S (Vt S g t) (Wt S g t) := by
  refine ⟨hτV, hτW, fun u => mem_Wt.mpr fun v hv => ?_⟩
  rw [polar_sub_right, ← hτV v hv,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup τ.2, hτV v hv, sub_self]

end CFSG.LargeExtraspecial.S8
