module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LieType.SeitzGeneration

namespace HyperBlocks

section Blocks

variable {K V Y : Type*} [Field K] [AddCommGroup V] [Module K V] [Group Y]
  (ρ : Y →* Module.End K V)

@[expose] def fixSub (F : Subgroup Y) : Submodule K V where
  carrier := {v | ∀ f ∈ F, ρ f v = v}
  add_mem' := fun {a b} ha hb f hf => by rw [map_add, ha f hf, hb f hf]
  zero_mem' := fun f _ => by simp
  smul_mem' := fun c v hv f hf => by rw [map_smul, hv f hf]

@[expose] def stabVec (v : V) : Subgroup Y where
  carrier := {y | ρ y v = v}
  mul_mem' := fun {a b} ha hb => by
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply]
    exact (congrArg (ρ a) hb).trans ha
  one_mem' := by show ρ 1 v = v; simp
  inv_mem' := fun {a} ha => by
    show ρ a⁻¹ v = v
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [show ρ a v = v from ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

@[expose] noncomputable def sumOp (A : Subgroup Y) [Fintype A] : Module.End K V :=
  ∑ a : A, ρ (a : Y)

variable (A : Subgroup Y) [Fintype A]

theorem sumOp_mul {a : Y} (ha : a ∈ A) : sumOp ρ A * ρ a = sumOp ρ A := by
  unfold sumOp
  rw [Finset.sum_mul]
  have : ∀ x : A, ρ (x : Y) * ρ a = ρ ((x * ⟨a, ha⟩ : A) : Y) := fun x => by
    rw [← map_mul]; rfl
  simp_rw [this]
  exact Fintype.sum_equiv (Equiv.mulRight (⟨a, ha⟩ : A)) _ _ (fun x => rfl)

theorem mul_sumOp {a : Y} (ha : a ∈ A) : ρ a * sumOp ρ A = sumOp ρ A := by
  unfold sumOp
  rw [Finset.mul_sum]
  have : ∀ x : A, ρ a * ρ (x : Y) = ρ ((⟨a, ha⟩ * x : A) : Y) := fun x => by
    rw [← map_mul]; rfl
  simp_rw [this]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨a, ha⟩ : A)) _ _ (fun x => rfl)

theorem sumOp_mem_fixSub (v : V) : sumOp ρ A v ∈ fixSub ρ A := fun a ha => by
  have := congrArg (fun T : Module.End K V => T v) (mul_sumOp ρ A ha)
  simpa using this

theorem sumOp_apply_of_fix {v : V} (hv : v ∈ fixSub ρ A) :
    sumOp ρ A v = (Fintype.card A : K) • v := by
  unfold sumOp
  rw [LinearMap.sum_apply]
  have : ∀ x : A, ρ (x : Y) v = v := fun x => hv x x.2
  rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_const, Finset.card_univ,
    Nat.cast_smul_eq_nsmul]

@[expose] noncomputable def block (F : Subgroup Y) : Submodule K V :=
  fixSub ρ F ⊓ LinearMap.ker (sumOp ρ A)

variable {A} (hK : ((Fintype.card A : ℕ) : K) ≠ 0)
include hK

theorem fixSub_inf_block (F : Subgroup Y) : fixSub ρ A ⊓ block ρ A F = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hv, -, hv2⟩
  have h := sumOp_apply_of_fix ρ A hv
  rw [LinearMap.mem_ker.mp hv2] at h
  have h2 := congrArg (fun w => ((Fintype.card A : ℕ) : K)⁻¹ • w) h.symm
  simpa [smul_smul, inv_mul_cancel₀ hK] using h2

theorem fixSub_eq_sup {F : Subgroup Y} (hFA : F ≤ A) :
    fixSub ρ F = fixSub ρ A ⊔ block ρ A F := by
  have hle : fixSub ρ A ≤ fixSub ρ F := fun v hv f hf => hv f (hFA hf)
  refine le_antisymm (fun v hv => ?_) (sup_le hle inf_le_left)
  rw [Submodule.mem_sup]
  set c : K := (Fintype.card A : K) with hc
  have hSv : sumOp ρ A v ∈ fixSub ρ A := sumOp_mem_fixSub ρ A v
  refine ⟨c⁻¹ • sumOp ρ A v, Submodule.smul_mem _ _ hSv, v - c⁻¹ • sumOp ρ A v, ⟨?_, ?_⟩,
    by simp⟩
  · exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ (hle hSv))
  · refine LinearMap.mem_ker.mpr ?_
    rw [map_sub, map_smul, sumOp_apply_of_fix ρ A hSv, smul_smul, inv_mul_cancel₀ hK, one_smul,
      sub_self]

theorem block_fixed_eq_zero {F : Subgroup Y} {x : Y}
    (hgen : F ⊔ Subgroup.zpowers x = A) {v : V} (hv : v ∈ block ρ A F) (hx : ρ x v = v) :
    v = 0 := by
  have hxs : Subgroup.zpowers x ≤ stabVec ρ v := by
    rw [Subgroup.zpowers_le]; exact hx
  have hA : A ≤ stabVec ρ v := hgen ▸ sup_le hv.1 hxs
  have : v ∈ fixSub ρ A ⊓ block ρ A F := ⟨hA, hv⟩
  rw [fixSub_inf_block ρ hK F] at this
  exact this

theorem block_inf_block {F F' : Subgroup Y} (hgen : F ⊔ F' = A) :
    block ρ A F ⊓ block ρ A F' = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hv, hv'⟩
  have hA : A ≤ stabVec ρ v := hgen ▸ sup_le hv.1 hv'.1
  have : v ∈ fixSub ρ A ⊓ block ρ A F := ⟨hA, hv⟩
  rw [fixSub_inf_block ρ hK F] at this
  exact this

omit hK in
theorem block_invariant {F : Subgroup Y} (hFA : F ≤ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {a : Y} (ha : a ∈ A) {v : V}
    (hv : v ∈ block ρ A F) : ρ a v ∈ block ρ A F := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have h1 : ρ f (ρ a v) = ρ (f * a) v := by rw [map_mul, Module.End.mul_apply]
    rw [h1, hcomm f (hFA hf) a ha, map_mul, Module.End.mul_apply, hv.1 f hf]
  · refine LinearMap.mem_ker.mpr ?_
    rw [← Module.End.mul_apply, sumOp_mul ρ A ha]
    exact LinearMap.mem_ker.mp hv.2

omit hK in
theorem sumOp_adjoint (ω : V →ₗ[K] V →ₗ[K] K) (hω : ∀ g : Y, ∀ x y, ω (ρ g x) (ρ g y) = ω x y)
    (B : Subgroup Y) [Fintype B] (x y : V) : ω (sumOp ρ B x) y = ω x (sumOp ρ B y) := by
  unfold sumOp
  simp only [LinearMap.sum_apply, map_sum]
  have h : ∀ a : B, ω (ρ (a : Y) x) y = ω x (ρ ((a⁻¹ : B) : Y) y) := fun a => by
    have := hω (a : Y) x (ρ ((a⁻¹ : B) : Y) y)
    rw [← this, ← Module.End.mul_apply, ← map_mul]
    simp
  simp_rw [h]
  exact Fintype.sum_equiv (Equiv.inv B) _ _ (fun a => rfl)

theorem block_orthogonal (ω : V →ₗ[K] V →ₗ[K] K)
    (hω : ∀ g : Y, ∀ x y, ω (ρ g x) (ρ g y) = ω x y)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {F F' : Subgroup Y} [Fintype F] (hFA : F ≤ A)
    (hF'A : F' ≤ A) (hgen : F ⊔ F' = A) (hKF : ((Fintype.card F : ℕ) : K) ≠ 0) {v w : V}
    (hv : v ∈ block ρ A F) (hw : w ∈ block ρ A F') : ω v w = 0 := by
  have hcF : ∀ f' ∈ F', ρ f' * sumOp ρ F = sumOp ρ F * ρ f' := fun f' hf' => by
    unfold sumOp
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← map_mul, ← map_mul, hcomm f' (hF'A hf') f (hFA f.2)]
  have hu : sumOp ρ F w = 0 := by
    have h1 : sumOp ρ F w ∈ fixSub ρ A := by
      have hA : A ≤ stabVec ρ (sumOp ρ F w) := by
        rw [← hgen]
        refine sup_le (sumOp_mem_fixSub ρ F w) (fun f' hf' => ?_)
        show ρ f' (sumOp ρ F w) = sumOp ρ F w
        rw [← Module.End.mul_apply, hcF f' hf', Module.End.mul_apply, hw.1 f' hf']
      exact hA
    have h2 : sumOp ρ A (sumOp ρ F w) = 0 := by
      have hSS : sumOp ρ A * sumOp ρ F = (Fintype.card F : K) • sumOp ρ A := by
        unfold sumOp
        rw [Finset.mul_sum]
        have : ∀ f : F, sumOp ρ A * ρ (f : Y) = sumOp ρ A := fun f => sumOp_mul ρ A (hFA f.2)
        unfold sumOp at this
        simp_rw [this]
        simp [Nat.cast_smul_eq_nsmul]
      rw [← Module.End.mul_apply, hSS, LinearMap.smul_apply, LinearMap.mem_ker.mp hw.2, smul_zero]
    have h3 := sumOp_apply_of_fix ρ A h1
    rw [h2] at h3
    have h4 := congrArg (fun z => ((Fintype.card A : ℕ) : K)⁻¹ • z) h3.symm
    simpa [smul_smul, inv_mul_cancel₀ hK] using h4
  have hv' : sumOp ρ F v = (Fintype.card F : K) • v := sumOp_apply_of_fix ρ F hv.1
  have h5 : ω (sumOp ρ F v) w = ω v (sumOp ρ F w) := sumOp_adjoint ρ ω hω F v w
  rw [hv', hu, map_zero, LinearMap.map_smul] at h5
  simp only [LinearMap.smul_apply, smul_eq_mul] at h5
  exact (mul_eq_zero.mp h5).resolve_left hKF

end Blocks

section Index

variable {Y : Type*} [Group Y] {p : ℕ}

theorem sup_eq_of_relIndex_prime (hp : p.Prime) {A F G : Subgroup Y} (hFA : F ≤ A) (hGA : G ≤ A)
    (hF : F.relIndex A = p) (hFG : ¬ G ≤ F) : F ⊔ G = A := by
  have hup : F ⊔ G ≤ A := sup_le hFA hGA
  have hmul := Subgroup.relIndex_mul_relIndex F (F ⊔ G) A le_sup_left hup
  rw [hF] at hmul
  rcases (Nat.dvd_prime hp).mp (Dvd.intro _ hmul) with h | h
  · exact absurd (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h)) hFG
  · rw [h] at hmul
    have h2 : (F ⊔ G).relIndex A = 1 := by
      have := hp.pos
      nlinarith [hmul]
    exact le_antisymm hup (Subgroup.relIndex_eq_one.mp h2)

theorem sup_eq_of_ne_relIndex_prime (hp : p.Prime) {A F F' : Subgroup Y} (hFA : F ≤ A)
    (hF'A : F' ≤ A) (hF : F.relIndex A = p) (hF' : F'.relIndex A = p) (hne : F ≠ F') :
    F ⊔ F' = A := by
  refine sup_eq_of_relIndex_prime hp hFA hF'A hF fun hle => hne ?_
  have hmul := Subgroup.relIndex_mul_relIndex F' F A hle hFA
  rw [hF, hF'] at hmul
  have h2 : F'.relIndex F = 1 := by
    have := hp.pos
    nlinarith [hmul]
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hle

theorem sup_zpowers_eq (hp : p.Prime) {A F : Subgroup Y} {x : Y} (hFA : F ≤ A)
    (hF : F.relIndex A = p) (hx : x ∈ A) (hxF : x ∉ F) : F ⊔ Subgroup.zpowers x = A :=
  sup_eq_of_relIndex_prime hp hFA (by rwa [Subgroup.zpowers_le]) hF
    (fun h => hxF (h (Subgroup.mem_zpowers x)))

end Index

end HyperBlocks

end CFSG.LieType.SeitzGeneration
