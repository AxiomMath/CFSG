module

public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Group

variable {G M : Type*} [Group G] [Group M]

private theorem commutatorElement_mul_left {a z : G} (hz : z ∈ Subgroup.center G) (b : G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : z * b = b * z := (Subgroup.mem_center_iff.mp hz b).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutatorElement_mul_right (a : G) {b z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hza : z * a⁻¹ = a⁻¹ * z := (Subgroup.mem_center_iff.mp hz a⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hza]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_top_of_range_le_map [Group.IsPerfect G] (φ : G →* M)
    (hker : φ.ker ≤ Subgroup.center G) {R : Subgroup G} (hR : φ.range ≤ R.map φ) : R = ⊤ := by
  have key : ∀ g : G, ∃ r ∈ R, ∃ z ∈ Subgroup.center G, g = r * z := by
    intro g
    obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.mp (hR (MonoidHom.mem_range.mpr ⟨g, rfl⟩))
    refine ⟨r, hr, r⁻¹ * g, hker ?_, (mul_inv_cancel_left r g).symm⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrg, inv_mul_cancel]
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := G), commutator_def,
    Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨r₁, hr₁, z₁, hz₁, rfl⟩ := key g₁
  obtain ⟨r₂, hr₂, z₂, hz₂, rfl⟩ := key g₂
  rw [commutatorElement_mul_left hz₁, commutatorElement_mul_right r₁ hz₂, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hr₁ hr₂) (inv_mem hr₁)) (inv_mem hr₂)

end Group

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

namespace HypFrame

variable (F : HypFrame Q n) {R : Subgroup (spinGroup Q)}

private theorem eichler_mem_map (hlong : ∀ {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K),
    F.longRoot hij s t (.ofAdd c) ∈ R) {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    eichler Q (F.vec j t) (c • F.vec i s) ∈ R.map (spinAction Q) :=
  Subgroup.mem_map.mpr ⟨_, hlong hij s t c, F.spinAction_longRoot_eq_eichler hij s t c⟩

variable
  (hlong : ∀ {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K), F.longRoot hij s t (.ofAdd c) ∈ R)
  (hperp : ∀ (i : Fin n) (s : Bool) (v : V), (∀ k r, polar Q v (F.vec k r) = 0) →
    eichler Q (F.vec i s) v ∈ R.map (spinAction Q))
  (hrest : ∀ v : V, (∀ k r, polar Q v (F.vec k r) = 0) → Q v = 0 → v = 0)
include hlong hperp hrest

omit hrest in
theorem rootGroup_vec_le_map_spinAction (i : Fin n) (s : Bool) :
    rootGroup Q (F.vec i s) ≤ R.map (spinAction Q) :=
  F.rootGroup_vec_le (F.eichler_mem_map hlong) hperp i s

theorem elementaryGroup_le_map_spinAction : elementaryGroup Q ≤ R.map (spinAction Q) :=
  F.elementaryGroup_le (F.eichler_mem_map hlong) hperp hrest

theorem exists_mem_spinAction_eq_vec (hn : 2 ≤ n) (j : Fin n) (r : Bool) {v : V} (hv : Q v = 0)
    (hv0 : v ≠ 0) : ∃ x ∈ R, spinAction Q x v = F.vec j r := by
  obtain ⟨g, hg, h⟩ :=
    F.exists_mem_apply_eq_vec (F.eichler_mem_map hlong) hperp hrest hn j r hv hv0
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  exact ⟨x, hx, h⟩

theorem exists_mem_spinAction_eq (hn : 2 ≤ n) {x y : V} (hx : Q x = 0) (hy : Q y = 0)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) : ∃ g ∈ R, spinAction Q g x = y := by
  obtain ⟨g, hg, h⟩ :=
    F.exists_mem_apply_eq (F.eichler_mem_map hlong) hperp hrest hn hx hy hx0 hy0
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  exact ⟨a, ha, h⟩

theorem eq_top_of_longRoot_mem [Group.IsPerfect (spinGroup Q)]
    (hrange : (spinAction Q).range ≤ elementaryGroup Q) : R = ⊤ :=
  eq_top_of_range_le_map (spinAction Q) (ker_spinAction_le_center Q)
    (hrange.trans (F.elementaryGroup_le_map_spinAction hlong hperp hrest))

omit hperp hrest in
theorem eq_top_of_longRoot_mem_of_eq_zero [Group.IsPerfect (spinGroup Q)]
    (h0 : ∀ v : V, (∀ k r, polar Q v (F.vec k r) = 0) → v = 0)
    (hrange : (spinAction Q).range ≤ elementaryGroup Q) : R = ⊤ := by
  refine F.eq_top_of_longRoot_mem hlong (fun i s v hv => ?_) (fun v hv _ => h0 v hv) hrange
  rw [h0 v hv, eichler_zero_right]
  exact one_mem _

end HypFrame

namespace OddFrame

variable (F : OddFrame Q n) {R : Subgroup (spinGroup Q)}

private theorem eichler_perp_mem_map
    (hshort : ∀ (i : Fin n) (s : Bool) (c : K), F.shortRoot i s (.ofAdd c) ∈ R)
    (hz : ∀ v : V, (∀ k r, polar Q v (F.vec k r) = 0) → ∃ c : K, v = c • F.z) (i : Fin n)
    (s : Bool) (v : V) (hv : ∀ k r, polar Q v (F.vec k r) = 0) :
    eichler Q (F.vec i s) v ∈ R.map (spinAction Q) := by
  obtain ⟨c, rfl⟩ := hz v hv
  exact Subgroup.mem_map.mpr ⟨_, hshort i s c, F.spinAction_shortRoot_eq_eichler i s c⟩

private theorem eq_zero_of_perp
    (hz : ∀ v : V, (∀ k r, polar Q v (F.vec k r) = 0) → ∃ c : K, v = c • F.z) (v : V)
    (hv : ∀ k r, polar Q v (F.vec k r) = 0) (hQ : Q v = 0) : v = 0 := by
  obtain ⟨c, rfl⟩ := hz v hv
  rw [QuadraticMap.map_smul, F.map_z, smul_eq_mul, mul_one, mul_self_eq_zero] at hQ
  rw [hQ, zero_smul]

variable
  (hlong : ∀ {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K), F.longRoot hij s t (.ofAdd c) ∈ R)
  (hshort : ∀ (i : Fin n) (s : Bool) (c : K), F.shortRoot i s (.ofAdd c) ∈ R)
  (hz : ∀ v : V, (∀ k r, polar Q v (F.vec k r) = 0) → ∃ c : K, v = c • F.z)
include hlong hshort hz

theorem elementaryGroup_le_map_spinAction : elementaryGroup Q ≤ R.map (spinAction Q) :=
  F.toHypFrame.elementaryGroup_le_map_spinAction hlong (F.eichler_perp_mem_map hshort hz)
    (F.eq_zero_of_perp hz)

theorem exists_mem_spinAction_eq_vec (hn : 2 ≤ n) (j : Fin n) (r : Bool) {v : V} (hv : Q v = 0)
    (hv0 : v ≠ 0) : ∃ x ∈ R, spinAction Q x v = F.vec j r :=
  F.toHypFrame.exists_mem_spinAction_eq_vec hlong (F.eichler_perp_mem_map hshort hz)
    (F.eq_zero_of_perp hz) hn j r hv hv0

theorem exists_mem_spinAction_eq (hn : 2 ≤ n) {x y : V} (hx : Q x = 0) (hy : Q y = 0)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) : ∃ g ∈ R, spinAction Q g x = y :=
  F.toHypFrame.exists_mem_spinAction_eq hlong (F.eichler_perp_mem_map hshort hz)
    (F.eq_zero_of_perp hz) hn hx hy hx0 hy0

theorem eq_top_of_root_mem [Group.IsPerfect (spinGroup Q)]
    (hrange : (spinAction Q).range ≤ elementaryGroup Q) : R = ⊤ :=
  F.toHypFrame.eq_top_of_longRoot_mem hlong (F.eichler_perp_mem_map hshort hz)
    (F.eq_zero_of_perp hz) hrange

end OddFrame

end CFSG.LieType.Universal.Spin
