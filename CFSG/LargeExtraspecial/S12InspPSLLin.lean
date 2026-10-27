module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial.S12InspPSL

open Module Submodule CFSG.ComponentClassification.OutcomeLocal

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := zmod2_eq_zero_or_one a

theorem zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 :=
  (zmod2_eq_zero_or_one a).resolve_left h

theorem mem_span_singleton_iff {a v : V} : v ∈ span (ZMod 2) {a} ↔ v = 0 ∨ v = a := by
  constructor
  · intro h
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp h
    rcases zmod2_eq_zero_or_one r with rfl | rfl
    · simp
    · simp
  · rintro (rfl | rfl)
    · exact zero_mem _
    · exact mem_span_singleton_self _

theorem mem_span_pair_iff {a b v : V} :
    v ∈ span (ZMod 2) {a, b} ↔ v = 0 ∨ v = a ∨ v = b ∨ v = a + b := by
  constructor
  · intro h
    obtain ⟨r, s, rfl⟩ := mem_span_pair.mp h
    rcases zmod2_eq_zero_or_one r with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one s with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact zero_mem _
    · exact subset_span (by simp)
    · exact subset_span (by simp)
    · exact add_mem (subset_span (by simp)) (subset_span (by simp))

theorem exists_functional {U : Submodule (ZMod 2) V} {v : V} (hv : v ∉ U) :
    ∃ ψ : V →ₗ[ZMod 2] ZMod 2, (∀ u ∈ U, ψ u = 0) ∧ ψ v = 1 := by
  obtain ⟨f, hf, hU⟩ := exists_le_ker_of_notMem hv
  exact ⟨f, fun u hu => hU hu, zmod2_eq_one_of_ne_zero hf⟩

theorem smul_add_smul_self (r : ZMod 2) (v : V) : r • v + r • v = 0 := zmod2_add_self _

theorem self_add_self (v : V) : v + v = 0 := zmod2_add_self v

theorem sub_eq_add' (v w : V) : v - w = v + w := by rw [sub_eq_add_neg, zmod2_neg]

theorem tv_mul_tv_apply {φ ψ : Dual (ZMod 2) V} {a b : V} (h : φ a = 0) (h' : ψ b = 0) (w : V) :
    ((tv φ a h * tv ψ b h' : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w =
      w + ψ w • b + (φ w + ψ w * φ b) • a := by
  change (tv φ a h : V →ₗ[ZMod 2] V) ((tv ψ b h' : V →ₗ[ZMod 2] V) w) = _
  rw [tv_apply, tv_apply, map_add, map_smul, smul_eq_mul, add_smul, mul_comm (ψ w)]

theorem tv_mul_tv_apply_left {φ ψ : Dual (ZMod 2) V} {a b : V} (h : φ a = 0) (h' : ψ b = 0)
    (w : V) :
    φ (((tv φ a h * tv ψ b h' : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w) =
      φ w + ψ w * φ b := by
  rw [tv_mul_tv_apply, map_add, map_add, map_smul, map_smul, h, smul_eq_mul, smul_eq_mul,
    mul_zero, add_zero]

theorem tv_mul_tv_apply_right {φ ψ : Dual (ZMod 2) V} {a b : V} (h : φ a = 0) (h' : ψ b = 0)
    (w : V) :
    ψ (((tv φ a h * tv ψ b h' : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w) =
      ψ w + (φ w + ψ w * φ b) * ψ a := by
  rw [tv_mul_tv_apply, map_add, map_add, map_smul, map_smul, h', smul_eq_mul, smul_eq_mul,
    mul_zero, add_zero]

theorem tv_mul_tv_pow_six {φ ψ : Dual (ZMod 2) V} {a b : V} (h : φ a = 0) (h' : ψ b = 0)
    (hs : φ b = ψ a) : (tv φ a h * tv ψ b h') ^ 6 = 1 := by
  set T := tv φ a h * tv ψ b h' with hT
  have hTw := tv_mul_tv_apply h h'
  have hTl := tv_mul_tv_apply_left h h'
  have hTr := tv_mul_tv_apply_right h h'
  rw [← hT] at hTw hTl hTr
  rcases zmod2_eq_zero_or_one (φ b) with h0 | h1
  ·
    have hs0 : ψ a = 0 := hs ▸ h0
    have h2 : T ^ 2 = 1 := by
      refine tv_ext fun w => ?_
      rw [pow_two]
      change (T : V →ₗ[ZMod 2] V) ((T : V →ₗ[ZMod 2] V) w) = w
      rw [hTw ((T : V →ₗ[ZMod 2] V) w), hTl, hTr, hTw w, h0, hs0]
      simp only [mul_zero, add_zero]
      calc w + ψ w • b + φ w • a + ψ w • b + φ w • a
          = w + (ψ w • b + ψ w • b) + (φ w • a + φ w • a) := by abel
        _ = w := by rw [smul_add_smul_self, smul_add_smul_self, add_zero, add_zero]
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, h2, one_pow]
  ·
    have hs1 : ψ a = 1 := hs ▸ h1
    have h3 : T ^ 3 = 1 := by
      refine tv_ext fun w => ?_
      rw [pow_three]
      change (T : V →ₗ[ZMod 2] V) ((T : V →ₗ[ZMod 2] V) ((T : V →ₗ[ZMod 2] V) w)) = w
      have e1 : ∀ v : V, φ ((T : V →ₗ[ZMod 2] V) v) = φ v + ψ v := fun v => by
        rw [hTl, h1, mul_one]
      have e2 : ∀ v : V, ψ ((T : V →ₗ[ZMod 2] V) v) = φ v := fun v => by
        rw [hTr, h1, hs1, mul_one, mul_one, add_comm (φ v) (ψ v), ← add_assoc,
          zmod2_scalar_add_self, zero_add]
      have e3 : ∀ v : V, (T : V →ₗ[ZMod 2] V) v = v + ψ v • b + (φ v + ψ v) • a := fun v => by
        rw [hTw, h1, mul_one]
      rw [e3 ((T : V →ₗ[ZMod 2] V) ((T : V →ₗ[ZMod 2] V) w)), e1 ((T : V →ₗ[ZMod 2] V) w),
        e2 ((T : V →ₗ[ZMod 2] V) w), e3 ((T : V →ₗ[ZMod 2] V) w), e1 w, e2 w, e3 w]
      generalize φ w = p
      generalize ψ w = r
      rcases zmod2_eq_zero_or_one p with rfl | rfl <;>
        rcases zmod2_eq_zero_or_one r with rfl | rfl <;>
        simp only [zero_add, add_zero, zero_smul, one_smul,
          show (1 : ZMod 2) + 1 = 0 from rfl] <;>
        abel_nf <;> simp [two_zsmul, zmod2_add_self]
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h3, one_pow]

end CFSG.LargeExtraspecial.S12InspPSL
