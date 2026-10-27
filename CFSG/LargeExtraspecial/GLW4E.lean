module

public import CFSG.LargeExtraspecial.GLRSplitBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.GLR

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

@[expose] noncomputable def dm (a : S.O) : S.Qt →ₗ[ZMod 2] S.Qt :=
  (a : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - LinearMap.id

theorem dm_apply (a : S.O) (x : S.Qt) : dm a x = (a : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x := rfl

@[expose] noncomputable def Emap (a b : S.O) : S.Qt →ₗ[ZMod 2] S.Qt := dm a ∘ₗ dm b

theorem Emap_apply (a b : S.O) (x : S.Qt) : Emap a b x = dm a (dm b x) := rfl

structure Layered (V W : Submodule (ZMod 2) S.Qt) (a : S.O) : Prop where
  fix : ∀ v ∈ V, (a : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
  mem_V : ∀ w ∈ W, dm a w ∈ V
  mem_W : ∀ x, dm a x ∈ W

theorem dm_one : dm (1 : S.O) = 0 := LinearMap.ext fun x => by
  rw [dm_apply]
  exact sub_self x

theorem dm_mul (a b : S.O) : dm (a * b) = dm a ∘ₗ dm b + dm a + dm b := LinearMap.ext fun x => by
  simp only [LinearMap.add_apply, LinearMap.comp_apply, dm_apply, Config.mul_apply, map_sub]
  abel

variable {V W : Submodule (ZMod 2) S.Qt}

theorem Layered.dm_eq_zero {a : S.O} (ha : Layered V W a) {v : S.Qt} (hv : v ∈ V) :
    dm a v = 0 := by
  rw [dm_apply, ha.fix v hv, sub_self]

theorem Emap_eq_zero_of_mem {a b : S.O} (ha : Layered V W a) (hb : Layered V W b) {x : S.Qt}
    (hx : x ∈ W) : Emap a b x = 0 :=
  ha.dm_eq_zero (hb.mem_V x hx)

theorem Emap_mem {a b : S.O} (ha : Layered V W a) (hb : Layered V W b) (x : S.Qt) :
    Emap a b x ∈ V :=
  ha.mem_V _ (hb.mem_W x)

theorem Emap_mul_left {a a' b : S.O} (ha : Layered V W a) (ha' : Layered V W a')
    (hb : Layered V W b) : Emap (a * a') b = Emap a b + Emap a' b := LinearMap.ext fun x => by
  rw [Emap_apply, dm_mul, LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply,
    ha.dm_eq_zero (ha'.mem_V _ (hb.mem_W x)), zero_add]
  rfl

theorem Emap_mul_right {a b b' : S.O} (ha : Layered V W a) (hb : Layered V W b)
    (hb' : Layered V W b') : Emap a (b * b') = Emap a b + Emap a b' := LinearMap.ext fun x => by
  rw [Emap_apply, dm_mul, LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply,
    map_add, map_add, ha.dm_eq_zero (hb.mem_V _ (hb'.mem_W x)), zero_add]
  rfl

theorem Emap_self {a : S.O} (haa : a * a = 1) : Emap a a = 0 := by
  have h := dm_mul a a
  rw [haa, dm_one] at h
  have h2 : dm a + dm a = 0 := ZModModule.add_self _
  rw [add_assoc, h2, add_zero] at h
  exact h.symm

theorem Emap_add_swap (a b : S.O) : Emap a b + Emap b a = dm (a * b) + dm (b * a) := by
  rw [dm_mul, dm_mul]
  change dm a ∘ₗ dm b + dm b ∘ₗ dm a = _
  rw [show dm a ∘ₗ dm b + dm a + dm b + (dm b ∘ₗ dm a + dm b + dm a) =
      dm a ∘ₗ dm b + dm b ∘ₗ dm a + (dm a + dm a) + (dm b + dm b) by abel,
    ZModModule.add_self, ZModModule.add_self, add_zero, add_zero]

theorem Emap_add_swap_of_mul_eq {a b t : S.O} (htV : ∀ x, dm t x ∈ V)
    (hba : ∀ v ∈ V, ((b * a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (h : a * b = b * a * t) :
    Emap a b + Emap b a = dm t := by
  rw [Emap_add_swap, h, dm_mul]
  have hz : dm (b * a) ∘ₗ dm t = 0 := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, dm_apply, hba _ (htV x), sub_self, LinearMap.zero_apply]
  rw [hz, zero_add, add_comm (dm (b * a)) (dm t), add_assoc, ZModModule.add_self, add_zero]

theorem Emap_conj (r a b : S.O) (x : S.Qt) :
    Emap (r * a * r⁻¹) (r * b * r⁻¹) x = (r : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (Emap a b (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x)) := by
  simp only [Emap_apply, dm_apply, Config.mul_apply, map_sub, Config.apply_inv_apply,
    Config.inv_apply_apply]

theorem polar_dm (c : S.O) (u w : S.Qt) : polar S.q (dm c u) w = polar S.q u (dm c⁻¹ w) := by
  rw [dm_apply, dm_apply, polar_sub_left, polar_sub_right]
  congr 1
  rw [← Config.polar_apply_apply c u (((c⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w),
    Config.apply_inv_apply]

theorem polar_Emap (a b : S.O) (x y : S.Qt) :
    polar S.q (Emap a b x) y = polar S.q x (Emap b⁻¹ a⁻¹ y) := by
  rw [Emap_apply, Emap_apply, polar_dm, polar_dm]

end CFSG.LargeExtraspecial.GLW4
