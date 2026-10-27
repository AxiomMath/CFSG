module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup Matrix

variable {G : Type} [Group G] {K A Z : Subgroup G} {κ : G → (Fin 8 → ZMod 2)}

structure CoordHyp (K A Z : Subgroup G) (κ : G → (Fin 8 → ZMod 2)) : Prop where
  add : ∀ a ∈ A, ∀ b ∈ A, κ (a * b) = κ a + κ b
  ker : ∀ a ∈ A, κ a = 0 ↔ a ∈ Z
  surj : ∀ v, ∃ a ∈ A, κ a = v
  norm : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A
  normZ : ∀ k ∈ K, ∀ y ∈ Z, k * y * k⁻¹ ∈ Z

namespace CoordHyp

variable (h : CoordHyp K A Z κ)
include h

theorem κ_one : κ 1 = 0 := by
  have h1 := h.add 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h1
  have h2 : κ 1 + κ 1 = κ 1 + 0 := by rw [← h1, add_zero]
  exact add_left_cancel h2

theorem κ_inv {a : G} (ha : a ∈ A) : κ a⁻¹ = κ a := by
  have h1 := h.add a ha a⁻¹ (inv_mem ha)
  rw [mul_inv_cancel, h.κ_one] at h1
  have h2 : ∀ x y : Fin 8 → ZMod 2, 0 = x + y → y = x := by
    intro x y hxy
    funext i
    have := congrFun hxy i
    simp only [Pi.zero_apply, Pi.add_apply] at this
    generalize x i = p at this ⊢
    generalize y i = q at this ⊢
    revert p q
    decide
  exact h2 _ _ h1

theorem mem_of_κ_eq {a b : G} (ha : a ∈ A) (hb : b ∈ A) (hab : κ a = κ b) : a⁻¹ * b ∈ Z := by
  rw [← h.ker _ (mul_mem (inv_mem ha) hb), h.add _ (inv_mem ha) _ hb, h.κ_inv ha, hab]
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize κ b i = p
  revert p
  decide

theorem κ_conj_congr {k a b : G} (hk : k ∈ K) (ha : a ∈ A) (hb : b ∈ A) (hab : κ a = κ b) :
    κ (k * a * k⁻¹) = κ (k * b * k⁻¹) := by
  have hy := h.mem_of_κ_eq ha hb hab
  have e : k * b * k⁻¹ = (k * a * k⁻¹) * (k * (a⁻¹ * b) * k⁻¹) := by group
  have hyA : k * (a⁻¹ * b) * k⁻¹ ∈ Z := h.normZ k hk _ hy
  have hyA' : k * (a⁻¹ * b) * k⁻¹ ∈ A := h.norm k hk _ (mul_mem (inv_mem ha) hb)
  rw [e, h.add _ (h.norm k hk a ha) _ hyA', (h.ker _ hyA').mpr hyA, add_zero]

@[expose] noncomputable def ι (v : Fin 8 → ZMod 2) : G := Classical.choose (h.surj v)

theorem ι_mem (v : Fin 8 → ZMod 2) : h.ι v ∈ A := (Classical.choose_spec (h.surj v)).1

theorem κ_ι (v : Fin 8 → ZMod 2) : κ (h.ι v) = v := (Classical.choose_spec (h.surj v)).2

theorem κ_conj_ι_add {k : G} (hk : k ∈ K) (u v : Fin 8 → ZMod 2) :
    κ (k * h.ι (u + v) * k⁻¹) = κ (k * h.ι u * k⁻¹) + κ (k * h.ι v * k⁻¹) := by
  have hm : κ (h.ι (u + v)) = κ (h.ι u * h.ι v) := by
    rw [h.add _ (h.ι_mem u) _ (h.ι_mem v), h.κ_ι, h.κ_ι, h.κ_ι]
  rw [h.κ_conj_congr hk (h.ι_mem _) (mul_mem (h.ι_mem u) (h.ι_mem v)) hm,
    show k * (h.ι u * h.ι v) * k⁻¹ = (k * h.ι u * k⁻¹) * (k * h.ι v * k⁻¹) by group,
    h.add _ (h.norm k hk _ (h.ι_mem u)) _ (h.norm k hk _ (h.ι_mem v))]

theorem κ_conj_ι_zero {k : G} (hk : k ∈ K) : κ (k * h.ι 0 * k⁻¹) = 0 := by
  have hm : κ (h.ι 0) = κ 1 := by rw [h.κ_ι, h.κ_one]
  rw [h.κ_conj_congr hk (h.ι_mem _) (one_mem _) hm, mul_one, mul_inv_cancel, h.κ_one]

@[expose] noncomputable def lmap (k : K) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun v := κ ((k : G) * h.ι v * (k : G)⁻¹)
  map_add' u v := h.κ_conj_ι_add k.2 u v
  map_smul' c v := by
    rw [RingHom.id_apply]
    have hc : c = 0 ∨ c = 1 := by
      revert c
      decide
    rcases hc with rfl | rfl
    · rw [zero_smul, zero_smul]
      exact h.κ_conj_ι_zero k.2
    · rw [one_smul, one_smul]

theorem lmap_apply (k : K) (v : Fin 8 → ZMod 2) :
    h.lmap k v = κ ((k : G) * h.ι v * (k : G)⁻¹) := rfl

theorem κ_conj (k : K) {a : G} (ha : a ∈ A) : κ ((k : G) * a * (k : G)⁻¹) = h.lmap k (κ a) := by
  rw [lmap_apply]
  exact h.κ_conj_congr k.2 ha (h.ι_mem _) (h.κ_ι _).symm

theorem lmap_mul (k k' : K) : h.lmap (k * k') = (h.lmap k).comp (h.lmap k') := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply]
  have e1 : h.lmap k' v = κ ((k' : G) * h.ι v * (k' : G)⁻¹) := rfl
  rw [e1, ← h.κ_conj k (h.norm _ k'.2 _ (h.ι_mem v)), lmap_apply]
  congr 1
  simp only [Subgroup.coe_mul, _root_.mul_inv_rev]
  group

theorem lmap_one : h.lmap 1 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  rw [lmap_apply, LinearMap.id_apply]
  simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one]
  exact h.κ_ι v

@[expose] noncomputable def rep : K →* GL (Fin 8) (ZMod 2) where
  toFun k := ⟨LinearMap.toMatrix' (h.lmap k), LinearMap.toMatrix' (h.lmap k⁻¹), by
      rw [← LinearMap.toMatrix'_comp, ← h.lmap_mul, mul_inv_cancel, h.lmap_one,
        LinearMap.toMatrix'_id], by
      rw [← LinearMap.toMatrix'_comp, ← h.lmap_mul, inv_mul_cancel, h.lmap_one,
        LinearMap.toMatrix'_id]⟩
  map_one' := Units.ext (by
    simp only [Units.val_one]
    rw [h.lmap_one, LinearMap.toMatrix'_id])
  map_mul' k k' := Units.ext (by
    simp only [Units.val_mul]
    rw [h.lmap_mul, LinearMap.toMatrix'_comp])

theorem coe_rep (k : K) : ((h.rep k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
    LinearMap.toMatrix' (h.lmap k) := rfl

theorem κ_conj_rep (k : K) {a : G} (ha : a ∈ A) :
    κ ((k : G) * a * (k : G)⁻¹) =
      ((h.rep k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ κ a := by
  rw [coe_rep, LinearMap.toMatrix'_mulVec, h.κ_conj k ha]

end CoordHyp

end CFSG.EvenSmallLie.UnitarySix.Child5
