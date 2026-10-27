module

public import CFSG.LargeExtraspecial.S4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap

theorem mem_span_cl_iff {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {w v : V} :
    v ∈ (ZMod 2) ∙ w ↔ v = 0 ∨ v = w := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem coe_mul_apply (x y : S.O) (v : S.Qt) :
    ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) :=
  rfl

theorem apply_inv_apply_O (x : S.O) (v : S.Qt) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
  rw [← coe_mul_apply, mul_inv_cancel]
  rfl

theorem inv_apply_apply_O (x : S.O) (v : S.Qt) :
    ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
  rw [← coe_mul_apply, inv_mul_cancel]
  rfl

theorem mem_fixSub_Lbar_mul_iff (h : S.M) {v : S.Qt} :
    v ∈ fixSub S (S.Lbar ((h : G) * g)) ↔
      (((S.ρ h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ fixSub S (S.Lbar g) := by
  rw [mem_fixSub, mem_fixSub]
  constructor
  · intro hv x hx
    have := hv _ (conj_mem_Lbar_mul S h hx)
    simp only [coe_mul_apply] at this
    have h2 := congrArg (((S.ρ h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) this
    rwa [inv_apply_apply_O] at h2
  · intro hv x hx
    have := hv _ ((mem_Lbar_mul_iff S h g).mp hx)
    simp only [coe_mul_apply, apply_inv_apply_O] at this
    exact (LinearEquiv.injective _ this)

variable (H : Hyp4 S g)
include H

theorem fixSub_Lbar_mul (h : S.M) :
    fixSub S (S.Lbar ((h : G) * g)) = (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
  ext v
  rw [mem_fixSub_Lbar_mul_iff, H.fixSub_eq, mem_span_cl_iff, mem_span_cl_iff,
    ← ρ_cl_conj_z S h H.conj_mem]
  constructor
  · rintro (h0 | h1)
    · left
      have := congrArg ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h0
      rwa [map_zero, apply_inv_apply_O] at this
    · right
      have := congrArg ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
      rwa [apply_inv_apply_O] at this
  · rintro (rfl | rfl)
    · exact Or.inl (map_zero _)
    · exact Or.inr (inv_apply_apply_O _ _)

theorem cl_mem_fixSub (h : S.M) :
    S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ fixSub S (S.Lbar ((h : G) * g)) := by
  rw [fixSub_Lbar_mul H]
  exact Submodule.mem_span_singleton_self _

theorem eq_cl_of_mem_fixSub (h : S.M) {v : S.Qt} (hv : v ∈ fixSub S (S.Lbar ((h : G) * g)))
    (hv0 : v ≠ 0) : v = S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
  rw [fixSub_Lbar_mul H, mem_span_cl_iff] at hv
  exact hv.resolve_left hv0

theorem cl_conj_ne_zero (h : S.M) : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ≠ 0 :=
  cl_conj_z_ne_zero S (conj_mem_QG' S h.2 H.conj_mem) (conj_ne_z' S h.2 H.conj_ne)

theorem cl_eq_of_Lbar_eq {h k : S.M} (e : S.Lbar ((h : G) * g) = S.Lbar ((k : G) * g)) :
    S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  have hmem := cl_mem_fixSub H h
  rw [e] at hmem
  exact eq_cl_of_mem_fixSub H k hmem (cl_conj_ne_zero H h)

theorem cl_mem_of_invariant (h : S.M) {U : Submodule (ZMod 2) S.Qt} (hU : U ≠ ⊥)
    (hinv : ∀ x ∈ S.Lbar ((h : G) * g), ∀ u ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) :
    S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ U := by
  obtain ⟨u, huU, hu0, hfix⟩ := exists_fixed_of_isPGroup S
    (isPGroup_Lbar S (conj_mem_QG' S h.2 H.conj_mem)) hinv hU
  rw [← eq_cl_of_mem_fixSub H h hfix hu0]
  exact huU

theorem cl_a_mem_of_invariant {U : Submodule (ZMod 2) S.Qt} (hU : U ≠ ⊥)
    (hinv : ∀ x ∈ S.Lbar g, ∀ u ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) :
    S.cl (g * S.z * g⁻¹) ∈ U := by
  have := cl_mem_of_invariant H 1 hU (by simpa using hinv)
  simpa using this

theorem Vt_le_of_invariant {t : S.O} {U : Submodule (ZMod 2) S.Qt} (hU : U ≠ ⊥)
    (hinv : ∀ x ∈ Rbar S g t, ∀ u ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) :
    Vt S g t ≤ U := by
  rw [Vt, Submodule.span_le]
  rintro _ ⟨h, ht, rfl⟩
  exact cl_mem_of_invariant H h hU fun x hx => hinv x (Lbar_mul_le_Rbar ht hx)

omit H in
@[expose] def orbit (S : Setting G) (g : G) (t : S.O) : Set S.Qt :=
  {v | ∃ x ∈ Rbar S g t, v = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))}

omit H in
theorem cl_a_mem_orbit {t : S.O} : S.cl (g * S.z * g⁻¹) ∈ orbit S g t :=
  ⟨1, one_mem _, rfl⟩

omit H in
theorem apply_mem_orbit {t x : S.O} (hx : x ∈ Rbar S g t) {v : S.Qt} (hv : v ∈ orbit S g t) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ orbit S g t := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨x * y, mul_mem hx hy, rfl⟩

omit H in
theorem orbit_subset_Vt {t : S.O} (ht : t ∈ S.Lbar g) (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    orbit S g t ⊆ Vt S g t := by
  rintro _ ⟨x, hx, rfl⟩
  exact apply_mem_Vt_of_mem_Rbar haQ hx (cl_a_mem_Vt ht)

theorem Vt_eq_span_orbit {t : S.O} (ht : t ∈ S.Lbar g) :
    Vt S g t = Submodule.span (ZMod 2) (orbit S g t) := by
  refine le_antisymm (Vt_le_of_invariant H ?_ fun x hx u hu => ?_)
    (Submodule.span_le.mpr (orbit_subset_Vt ht H.conj_mem))
  · intro h0
    have : S.cl (g * S.z * g⁻¹) ∈ Submodule.span (ZMod 2) (orbit S g t) :=
      Submodule.subset_span cl_a_mem_orbit
    rw [h0, Submodule.mem_bot] at this
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne this
  · induction hu using Submodule.span_induction with
    | mem v hv => exact Submodule.subset_span (apply_mem_orbit hx hv)
    | zero => simp
    | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
    | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu

theorem Vt_ne_bot {t : S.O} (ht : t ∈ S.Lbar g) : Vt S g t ≠ ⊥ := by
  intro h0
  have := cl_a_mem_Vt (S := S) ht
  rw [h0, Submodule.mem_bot] at this
  exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne this

theorem fix_of_mem_normalizer {x : S.O} (hx : x ∈ normalizer (S.Lbar g : Set S.O)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  have hmem : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈ fixSub S (S.Lbar g) := by
    intro y hy
    have hy' : x⁻¹ * y * x ∈ S.Lbar g := by
      have := (mem_normalizer_iff.mp (inv_mem hx) y).mp hy
      simpa using this
    have hfixA : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
      rw [H.fixSub_eq]
      exact Submodule.mem_span_singleton_self _
    have h1 := hfixA _ hy'
    simp only [coe_mul_apply] at h1
    have h2 := congrArg (x : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    rwa [apply_inv_apply_O] at h2
  rw [H.fixSub_eq, mem_span_cl_iff] at hmem
  rcases hmem with h0 | h1
  · exact absurd ((LinearEquiv.map_eq_zero_iff _).mp h0) (cl_conj_z_ne_zero S H.conj_mem H.conj_ne)
  · exact h1

theorem fix_of_mem_normalizer_mul (h : S.M) {x : S.O}
    (hx : x ∈ normalizer (S.Lbar ((h : G) * g) : Set S.O)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
  have hmem : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) ∈
      fixSub S (S.Lbar ((h : G) * g)) := by
    intro w hw
    have hw' : x⁻¹ * w * x ∈ S.Lbar ((h : G) * g) := by
      have := (mem_normalizer_iff.mp (inv_mem hx) w).mp hw
      simpa using this
    have h1 := cl_mem_fixSub H h _ hw'
    simp only [coe_mul_apply] at h1
    have h2 := congrArg (x : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    rwa [apply_inv_apply_O] at h2
  refine eq_cl_of_mem_fixSub H h hmem ?_
  rw [Ne, LinearEquiv.map_eq_zero_iff]
  exact cl_conj_ne_zero H h

omit H in
theorem Lbar_apply_sub_mem_span (haQ : g * S.z * g⁻¹ ∈ S.QG) {x : G}
    (hx : x ∈ S.QG ⊓ S.Qa g) {s : S.O} (hs : s ∈ S.Lbar g) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) - S.cl x ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨y, hy, rfl⟩ := (mem_Lbar S).mp hs
  rw [S.ρ_cl y hx.1]
  rcases (S.conjBy g).mul_comm_or hy.1 hx.2 with h1 | h1
  · rw [h1, mul_inv_cancel_right, sub_self]
    exact Submodule.zero_mem _
  · have e : (y : G) * x * (y : G)⁻¹ = g * S.z * g⁻¹ * x := by
      rw [h1]
      change (S.conjBy g).z * (x * y) * (y : G)⁻¹ = (S.conjBy g).z * x
      group
    rw [e, S.cl_mul haQ hx.1, add_sub_cancel_right]
    exact Submodule.mem_span_singleton_self _

end CFSG.LargeExtraspecial.S4
