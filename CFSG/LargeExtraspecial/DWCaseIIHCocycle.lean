module

public import CFSG.LargeExtraspecial.DWCaseIIHScalar
public import CFSG.LargeExtraspecial.DWCaseIIHData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.GroupTheory.GLnTwoSplitting
open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def conjE (g : V ≃ₗ[ZMod 2] V) (X : Module.End (ZMod 2) V) :
    Module.End (ZMod 2) V :=
  (g : V →ₗ[ZMod 2] V) ∘ₗ X ∘ₗ (g.symm : V →ₗ[ZMod 2] V)

theorem conjE_apply (g : V ≃ₗ[ZMod 2] V) (X : Module.End (ZMod 2) V) (x : V) :
    conjE g X x = g (X (g.symm x)) := rfl

theorem conjE_add (g : V ≃ₗ[ZMod 2] V) (X Y : Module.End (ZMod 2) V) :
    conjE g (X + Y) = conjE g X + conjE g Y := by
  ext x
  simp [conjE_apply]

theorem conjE_zero (g : V ≃ₗ[ZMod 2] V) : conjE g (0 : Module.End (ZMod 2) V) = 0 := by
  ext x
  simp [conjE_apply]

theorem conjE_smul_one (g : V ≃ₗ[ZMod 2] V) (a : ZMod 2) :
    conjE g (a • (1 : Module.End (ZMod 2) V)) = a • 1 := by
  ext x
  simp [conjE_apply]

theorem conjE_one (X : Module.End (ZMod 2) V) : conjE 1 X = X := rfl

theorem conjE_mul (g h : V ≃ₗ[ZMod 2] V) (X : Module.End (ZMod 2) V) :
    conjE (g * h) X = conjE g (conjE h X) := rfl

structure IsSpCocycle (ω : BilinForm (ZMod 2) V) {L : Type*} [Group L]
    (ρ : L →* (V ≃ₗ[ZMod 2] V)) (δ : L → Module.End (ZMod 2) V) : Prop where
  isometry : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y
  transvection : ∀ v, ∃ g, ∀ x, ρ g x = x + ω x v • v
  alt : ∀ g, IsAltEnd ω (δ g)
  cocycle : ∀ g h, δ (g * h) = δ g + conjE (ρ g) (δ h)
  ker : ∀ g, ρ g = 1 → δ g = 0

namespace IsSpCocycle

variable {ω : BilinForm (ZMod 2) V} {L : Type*} [Group L] {ρ : L →* (V ≃ₗ[ZMod 2] V)}
  {δ : L → Module.End (ZMod 2) V} (H : IsSpCocycle ω ρ δ)
include H

theorem congr {g g' : L} (h : ρ g = ρ g') : δ g = δ g' := by
  have h1 : ρ (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := H.cocycle g (g⁻¹ * g')
  rw [mul_inv_cancel_left, H.ker _ h1, conjE_zero, add_zero] at h2
  exact h2.symm

@[expose] noncomputable def lift (v : V) : L := (H.transvection v).choose

theorem lift_apply (v x : V) : ρ (H.lift v) x = tv ω v x := (H.transvection v).choose_spec x

@[expose] noncomputable def tvVal (v : V) : Module.End (ZMod 2) V := δ (H.lift v)

theorem tvVal_eq (v : V) : H.tvVal v = δ (H.lift v) := rfl

theorem lift_symm_apply (hω : ω.IsAlt) (v x : V) : (ρ (H.lift v)).symm x = tv ω v x := by
  rw [LinearEquiv.symm_apply_eq, H.lift_apply, tv_tv ω hω]

theorem conjE_lift_apply (hω : ω.IsAlt) (v : V) (X : Module.End (ZMod 2) V) (x : V) :
    conjE (ρ (H.lift v)) X x = tv ω v (X (tv ω v x)) := by
  rw [conjE_apply, H.lift_symm_apply hω, H.lift_apply]

theorem conjE_lift (hω : ω.IsAlt) (v : V) {X : Module.End (ZMod 2) V} (hX : IsAltEnd ω X) :
    conjE (ρ (H.lift v)) X = X + sw ω v (X v) := by
  ext x
  rw [H.conjE_lift_apply hω, tv_comp_comp_tv hω hX]
  rfl

theorem sw_tvVal_self (hω : ω.IsAlt) (v : V) : sw ω v (H.tvVal v v) = 0 := by
  have h1 : ρ (H.lift v * H.lift v) = 1 := by
    ext x
    rw [map_mul, LinearEquiv.mul_apply, H.lift_apply, H.lift_apply, tv_tv ω hω]
    rfl
  have h2 := H.cocycle (H.lift v) (H.lift v)
  rw [H.ker _ h1, H.conjE_lift hω v (H.alt _)] at h2
  rw [tvVal_eq]
  have h3 : sw ω v (δ (H.lift v) v) =
      δ (H.lift v) + (δ (H.lift v) + sw ω v (δ (H.lift v) v)) := by
    abel_two
  rw [h3]
  exact h2.symm

theorem sw_tvVal_comm (hω : ω.IsAlt) {u v : V} (huv : ω u v = 0) :
    sw ω u (H.tvVal v u) = sw ω v (H.tvVal u v) := by
  have h1 : ρ (H.lift u * H.lift v) = ρ (H.lift v * H.lift u) := by
    ext x
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, H.lift_apply,
      H.lift_apply, H.lift_apply, H.lift_apply, tv_comm hω huv]
  have h2 := H.congr h1
  rw [H.cocycle, H.cocycle, H.conjE_lift hω u (H.alt _), H.conjE_lift hω v (H.alt _)] at h2
  rw [tvVal_eq, tvVal_eq]
  have h3 : sw ω u (δ (H.lift v) u) = δ (H.lift u) + (δ (H.lift v) + sw ω u (δ (H.lift v) u)) +
      (δ (H.lift u) + δ (H.lift v)) := by
    abel_two
  rw [h3, h2]
  abel_two

theorem tvVal_add_apply (hω : ω.IsAlt) {u v : V} (huv : ω u v = 1) (x : V) :
    H.tvVal (u + v) x = H.tvVal u x +
      tv ω u (H.tvVal v (tv ω u x) + tv ω v (H.tvVal u (tv ω v (tv ω u x)))) := by
  have h1 : ρ (H.lift u * (H.lift v * H.lift u)) = ρ (H.lift (u + v)) := by
    ext y
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, H.lift_apply,
      H.lift_apply, H.lift_apply, H.lift_apply, tv_tv_tv hω huv]
  have h2 := H.congr h1
  rw [H.cocycle, H.cocycle] at h2
  rw [tvVal_eq, tvVal_eq, tvVal_eq, ← h2, LinearMap.add_apply, H.conjE_lift_apply hω,
    LinearMap.add_apply, H.conjE_lift_apply hω]

theorem lift_four (hω : ω.IsAlt) {a b c : V} (hab : ω a b = 0) (hac : ω a c = 0)
    (hbc : ω b c = 0) :
    ρ (H.lift a * (H.lift b * (H.lift c * H.lift (a + b + c)))) =
      ρ (H.lift (a + c) * (H.lift (b + c) * H.lift (a + b))) := by
  ext x
  simp only [map_mul, LinearEquiv.mul_apply, H.lift_apply]
  exact tv_four hω hab hac hbc x

variable [FiniteDimensional (ZMod 2) V]

theorem tvVal_mem_span (hω : ω.IsAlt) (hnd : ω.Nondegenerate) {u v : V} (huv : ω u v = 0) :
    H.tvVal v u ∈ span (ZMod 2) {u, v} := by
  by_cases hu : u ∈ span (ZMod 2) {v}
  · rcases mem_span_singleton_iff_zmod_two.mp hu with rfl | rfl
    · rw [map_zero]
      exact zero_mem _
    · rw [Set.pair_eq_singleton]
      by_cases hv : u = 0
      · rw [hv, map_zero]
        exact zero_mem _
      · exact mem_span_of_sw_eq_zero hω hnd hv (H.sw_tvVal_self hω u)
  · exact mem_span_pair_of_sw_eq_sw hω hnd hu (H.sw_tvVal_comm hω huv)

theorem exists_tvData (hω : ω.IsAlt) (hnd : ω.Nondegenerate) (h4 : 4 ≤ finrank (ZMod 2) V) :
    ∃ (α : V → ZMod 2) (e : V → V), TvData ω H.tvVal α e := by
  classical
  have hex : ∀ v : V, v ≠ 0 → ∃ (a : ZMod 2) (e : V), H.tvVal v = a • 1 + sw ω v e :=
    fun v hv => exists_eq_smul_one_add_sw hω hnd h4 hv (H.alt _) fun u huv =>
      H.tvVal_mem_span hω hnd huv
  choose! α e he using hex
  refine ⟨α, fun v => if v = 0 then 0 else e v, ⟨by simp, fun v hv => ?_, ?_, ?_⟩⟩
  · simp only [hv, ↓reduceIte]
    exact he v hv
  · intro u v huv
    by_cases hu : u = 0
    · simp [hu]
    by_cases hv : v = 0
    · simp [hv]
    by_cases huv' : u = v
    · rw [huv']
    simp only [hu, hv, ↓reduceIte]
    have h1 := H.sw_tvVal_comm hω huv
    have hvu : ω v u = 0 := by rw [bilin_comm_of_isAlt hω, huv]
    rw [he v hv, he u hu] at h1
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, sw_apply, huv,
      hvu, zero_smul, add_zero, sw_add_right, sw_smul_right, sw_self, smul_zero, zero_add] at h1
    rw [sw_comm ω v u] at h1
    have h2 : (ω u (e v) + ω v (e u)) • sw ω u v = 0 := by
      rw [add_smul, h1, ZModModule.add_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact zmod_two_eq_of_add_eq_zero h3
    · rcases mem_span_singleton_iff_zmod_two.mp (mem_span_of_sw_eq_zero hω hnd hu h3) with h4 | h4
      · exact absurd h4 hv
      · exact absurd h4.symm huv'
  · exact fun u v huv x => H.tvVal_add_apply hω huv x

end IsSpCocycle

end CFSG.LargeExtraspecial.DW
