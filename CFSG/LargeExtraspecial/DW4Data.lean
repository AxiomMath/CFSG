module

public import CFSG.LargeExtraspecial.S3Basic
public import CFSG.LargeExtraspecial.S4Restrict

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.W4

open Subgroup Module QuadraticMap
open scoped IsMulCommutative

variable {X : Type*} [Group X] [Finite X] (T : Setting X)

structure Hyp (W₁ W₂ : Submodule (ZMod 2) T.Qt) : Prop where
  compl : IsCompl W₁ W₂
  inv₁ : ∀ m : T.M, ∀ w ∈ W₁, ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₁
  inv₂ : ∀ m : T.M, ∀ w ∈ W₂, ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₂
  ts₁ : ∀ w ∈ W₁, T.q w = 0
  ts₂ : ∀ w ∈ W₂, T.q w = 0
  width : T.width = 4

structure IsZCompl {X : Type*} [Group X] (U A : Subgroup X) (z : X) : Prop where
  le : U ≤ A
  not_mem : z ∉ U
  cover : ∀ x ∈ A, x ∈ U ∨ x * z ∈ U

variable {T}

theorem polar_eq_zero_of_ts {W : Submodule (ZMod 2) T.Qt} (hW : ∀ w ∈ W, T.q w = 0)
    {u v : T.Qt} (hu : u ∈ W) (hv : v ∈ W) : polar T.q u v = 0 := by
  rw [QuadraticMap.polar, hW _ (W.add_mem hu hv), hW u hu, hW v hv]
  simp

theorem finrank_le_width_of_ts {W : Submodule (ZMod 2) T.Qt} (hW : ∀ w ∈ W, T.q w = 0) :
    finrank (ZMod 2) W ≤ T.width := by
  have hle : W ≤ LinearMap.BilinForm.orthogonal T.q.polarBilin W := fun v hv =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun u hu => by
      rw [polarBilin_apply_apply]
      exact polar_eq_zero_of_ts hW hu hv
  have h1 := LinearMap.BilinForm.finrank_orthogonal T.q_nondegenerate W
  have h2 := Submodule.finrank_mono hle
  rw [T.finrank_Qt_eq_two_mul_width] at h1
  omega

theorem isElementaryAbelian_clPre {W : Submodule (ZMod 2) T.Qt} (hW : ∀ w ∈ W, T.q w = 0) :
    IsElementaryAbelian 2 (T.clPre W) where
  is_comm := ⟨fun a b => Subtype.ext ((T.polar_cl_eq_zero_iff a.2.1 b.2.1).mp
    (polar_eq_zero_of_ts hW a.2.2 b.2.2))⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
    Subtype.ext ((T.q_cl_eq_zero_iff a.2.1).mp (hW _ a.2.2))

theorem conj_eq_of_polar_eq_zero {x y : X} (hx : x ∈ T.QG) (hy : y ∈ T.QG)
    (h : polar T.q (T.cl x) (T.cl y) = 0) : x * y * x⁻¹ = y := by
  rw [(T.polar_cl_eq_zero_iff hx hy).mp h, mul_inv_cancel_right]

theorem conj_eq_mul_z_of_polar_ne_zero {x y : X} (hx : x ∈ T.QG) (hy : y ∈ T.QG)
    (h : polar T.q (T.cl x) (T.cl y) ≠ 0) : x * y * x⁻¹ = y * T.z := by
  rcases T.commutator_eq_one_or_z hx hy with h1 | h1
  · exact absurd ((T.polar_cl_eq_zero_iff hx hy).mpr (by
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [h1, one_mul])) h
  · calc x * y * x⁻¹ = x * y * x⁻¹ * y⁻¹ * y := by group
      _ = T.z * y := by rw [h1]
      _ = y * T.z := (T.z_comm_QG hy).symm

omit [Finite X] in
theorem exists_isZCompl {A : Subgroup X} [IsElementaryAbelian 2 A] {z : X} (hz : z ∈ A)
    (hz1 : z ≠ 1) (hz2 : z * z = 1) : ∃ U, IsZCompl U A z := by
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl 2 A (zpowers ⟨z, hz⟩)
  refine ⟨C.map A.subtype, ⟨map_subtype_le C, ?_, fun x hx => ?_⟩⟩
  · rintro ⟨c, hc, hcz⟩
    have hc' : c = ⟨z, hz⟩ := Subtype.ext hcz
    have hmem : c ∈ zpowers ⟨z, hz⟩ ⊓ C := ⟨hc' ▸ mem_zpowers _, hc⟩
    rw [hC.inf_eq_bot, mem_bot] at hmem
    exact hz1 (hcz ▸ congrArg Subtype.val hmem)
  · have hmem : (⟨x, hx⟩ : A) ∈ zpowers ⟨z, hz⟩ ⊔ C := by
      rw [hC.sup_eq_top]
      exact mem_top _
    obtain ⟨y, hy, c, hc, hyc⟩ := Subgroup.mem_sup.mp hmem
    rcases (Setting.mem_zpowers_iff_of_mul_self (g := (⟨z, hz⟩ : A))
      (Subtype.ext hz2)).mp hy with rfl | rfl
    · left
      refine ⟨c, hc, ?_⟩
      rw [one_mul] at hyc
      exact congrArg Subtype.val hyc
    · right
      refine ⟨c, hc, ?_⟩
      have hcx : (c : X) = z * x := by
        have := congrArg Subtype.val hyc
        simp only [Subgroup.coe_mul] at this
        rw [← this, ← mul_assoc, hz2, one_mul]
      change (c : X) = x * z
      rw [hcx]
      exact congrArg Subtype.val (mul_comm (⟨z, hz⟩ : A) ⟨x, hx⟩)

namespace IsZCompl

variable {U : Subgroup X} {W : Submodule (ZMod 2) T.Qt} (hU : IsZCompl U (T.clPre W) T.z)
include hU

omit [Finite X] in
theorem eq_of_cl_eq {u u' : X} (hu : u ∈ U) (hu' : u' ∈ U) (h : T.cl u = T.cl u') : u = u' := by
  rcases (T.cl_eq_cl_iff (hU.le hu).1 (hU.le hu').1).mp h with h1 | h1
  · exact h1.symm
  · exfalso
    apply hU.not_mem
    have : T.z = u⁻¹ * u' := by rw [h1]; group
    rw [this]
    exact U.mul_mem (U.inv_mem hu) hu'

omit [Finite X] in
theorem exists_cl_eq {w : T.Qt} (hw : w ∈ W) : ∃ u ∈ U, T.cl u = w := by
  obtain ⟨x, hx, rfl⟩ := T.exists_cl w
  rcases hU.cover x ⟨hx, hw⟩ with h | h
  · exact ⟨x, h, rfl⟩
  · exact ⟨x * T.z, h, T.cl_mul_z hx⟩

omit [Finite X] in
theorem mem_QG {u : X} (hu : u ∈ U) : u ∈ T.QG := (hU.le hu).1

omit [Finite X] in
theorem cl_mem {u : X} (hu : u ∈ U) : T.cl u ∈ W := (hU.le hu).2

end IsZCompl

namespace Hyp

variable {W₁ W₂ : Submodule (ZMod 2) T.Qt}

theorem symm (H : Hyp T W₁ W₂) : Hyp T W₂ W₁ :=
  ⟨H.compl.symm, H.inv₂, H.inv₁, H.ts₂, H.ts₁, H.width⟩

variable (H : Hyp T W₁ W₂)
include H

theorem polar_eq_zero {u v : T.Qt} (hu : u ∈ W₁) (hv : v ∈ W₁) : polar T.q u v = 0 :=
  polar_eq_zero_of_ts H.ts₁ hu hv

theorem exists_add_eq (y : T.Qt) : ∃ a ∈ W₁, ∃ b ∈ W₂, a + b = y :=
  Submodule.mem_sup.mp (H.compl.sup_eq_top ▸ Submodule.mem_top : y ∈ W₁ ⊔ W₂)

theorem eq_zero_of_polar {v : T.Qt} (hv : v ∈ W₂) (h : ∀ u ∈ W₁, polar T.q v u = 0) : v = 0 := by
  refine T.q_nondegenerate.1 v fun y => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := H.exists_add_eq y
  rw [polarBilin_apply_apply, polar_add_right, h a ha, H.symm.polar_eq_zero hv hb, add_zero]

theorem finrank₁ : finrank (ZMod 2) W₁ = 4 := by
  have h1 := finrank_le_width_of_ts H.ts₁
  have h2 := finrank_le_width_of_ts H.ts₂
  have h3 := Submodule.finrank_add_eq_of_isCompl H.compl
  rw [T.finrank_Qt_eq_two_mul_width, H.width] at h3
  rw [H.width] at h1 h2
  omega

theorem card₁ : Nat.card W₁ = 2 ^ 4 := by rw [T.card_submodule, H.finrank₁]

theorem card_clPre₁ : Nat.card (T.clPre W₁) = 2 ^ 5 := by
  rw [T.card_clPre, H.card₁]
  norm_num

theorem eq_one_or_z_of_mem {x : X} (h1 : x ∈ T.clPre W₁) (h2 : x ∈ T.clPre W₂) :
    x = 1 ∨ x = T.z := by
  have h : T.cl x ∈ W₁ ⊓ W₂ := ⟨h1.2, h2.2⟩
  rw [H.compl.inf_eq_bot, Submodule.mem_bot] at h
  exact (T.cl_eq_zero_iff h1.1).mp h

theorem ρ_eq_one_of_fix {m : T.M}
    (h : ∀ u ∈ W₁, ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) u = u) : T.ρ m = 1 := by
  set e := ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) with he
  have h2 : ∀ w ∈ W₂, e w = w := by
    intro w hw
    have hd : e w - w ∈ W₂ := W₂.sub_mem (H.inv₂ m w hw) hw
    have := H.eq_zero_of_polar hd fun u hu => by
      have h3 : polar T.q (e w) u = polar T.q w u :=
        calc polar T.q (e w) u = polar T.q (e w) (e u) := by rw [h u hu]
          _ = polar T.q w u :=
            TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (T.ρ m).2 w u
      rw [polar_sub_left, h3, sub_self]
    exact sub_eq_zero.mp this
  refine Subtype.ext (LinearEquiv.ext fun y => ?_)
  obtain ⟨a, ha, b, hb, rfl⟩ := H.exists_add_eq y
  change e (a + b) = a + b
  rw [map_add, h a ha, h2 b hb]

omit H in
@[expose] noncomputable def res (H : Hyp T W₁ W₂) : T.M →* (W₁ ≃ₗ[ZMod 2] W₁) :=
  S4.restrictHom (T.O.subtype.comp T.ρ) W₁ fun m u hu => H.inv₁ m u hu

theorem coe_res_apply (m : T.M) (u : W₁) :
    ((H.res m u : W₁) : T.Qt) = ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) u := rfl

theorem mem_QG_of_res_eq_one {m : T.M} (h : H.res m = 1) : (m : X) ∈ T.QG := by
  refine (T.ρ_eq_one_iff m).mp (H.ρ_eq_one_of_fix fun u hu => ?_)
  have := congrArg (fun f : W₁ ≃ₗ[ZMod 2] W₁ => ((f ⟨u, hu⟩ : W₁) : T.Qt)) h
  exact this

theorem res_eq_one_of_mem_QG {m : T.M} (h : (m : X) ∈ T.QG) : H.res m = 1 := by
  refine LinearEquiv.ext fun u => Subtype.ext ?_
  rw [coe_res_apply, (T.ρ_eq_one_iff m).mpr h]
  rfl

theorem mem_clPre_of_commute {x : X} (hx : x ∈ T.QG)
    (h : ∀ y ∈ T.clPre W₁, x * y = y * x) : x ∈ T.clPre W₁ := by
  obtain ⟨a, ha, b, hb, hab⟩ := H.exists_add_eq (T.cl x)
  have hb0 : b = 0 := H.eq_zero_of_polar hb fun u hu => by
    obtain ⟨y, hy, rfl⟩ := T.exists_cl u
    have h1 : polar T.q (T.cl x) (T.cl y) = 0 :=
      (T.polar_cl_eq_zero_iff hx hy).mpr (h y ⟨hy, hu⟩)
    rw [← hab, polar_add_left, H.polar_eq_zero ha hu, zero_add] at h1
    exact h1
  refine ⟨hx, ?_⟩
  rw [← hab, hb0, add_zero]
  exact ha

theorem mem_clPre_of_mem_M {g : X} (hg : g ∈ T.M) (h : ∀ y ∈ T.clPre W₁, g * y = y * g) :
    g ∈ T.clPre W₁ := by
  have hρ : T.ρ ⟨g, hg⟩ = 1 := H.ρ_eq_one_of_fix fun u hu => by
    obtain ⟨y, hy, rfl⟩ := T.exists_cl u
    rw [T.ρ_cl ⟨g, hg⟩ hy]
    change T.cl (g * y * g⁻¹) = T.cl y
    rw [h y ⟨hy, hu⟩, mul_inv_cancel_right]
  exact H.mem_clPre_of_commute ((T.ρ_eq_one_iff _).mp hρ) h

theorem conj_mem_clPre {g : X} (hg : g ∈ T.M) {x : X} (hx : x ∈ T.clPre W₁) :
    g * x * g⁻¹ ∈ T.clPre W₁ :=
  ⟨T.conj_mem_QG hg hx.1, by rw [← T.ρ_cl ⟨g, hg⟩ hx.1]; exact H.inv₁ _ _ hx.2⟩

end Hyp

end CFSG.LargeExtraspecial.DW.W4
