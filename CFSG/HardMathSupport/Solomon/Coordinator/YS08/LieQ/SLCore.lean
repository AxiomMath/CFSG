module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.SLRigid

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.LieType.ChevTwo.OppCl

theorem rigidSLCore : RigidSLCore := by
  intro F _ _ V _ _ _ W hW0 hWtop r hr m hm hrm hcomm
  obtain ⟨hradd, σ, hσ⟩ := hr
  have hr0 : r 0 = 0 := by
    have h := hradd 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  obtain ⟨u, hu⟩ : ∃ u : V, u ∉ W := by
    by_contra h
    push Not at h
    exact hWtop (eq_top_iff.2 fun x _ => h x)
  obtain ⟨φ₀, hφ₀u, hφ₀W⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu inferInstance
  have hφ₀ : ∀ x ∈ W, φ₀ x = 0 := fun x hx => by
    have : φ₀ x ∈ W.map φ₀ := ⟨x, hx, rfl⟩
    rw [hφ₀W] at this
    simpa using this
  set v₀ : V := (φ₀ u)⁻¹ • u with hv₀def
  have hv₀ : φ₀ v₀ = 1 := by
    rw [hv₀def, map_smul, smul_eq_mul, inv_mul_cancel₀ hφ₀u]
  set l : F := φ₀ (r v₀) with hl
  have h1 : ∀ w ∈ W, r w = l • w := by
    intro w hw
    have h := hcomm w φ₀ hw hφ₀ v₀
    rw [hv₀, one_smul, hradd] at h
    exact add_left_cancel h
  obtain ⟨w₁, hw₁, hw₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hl0 : l ≠ 0 := by
    intro h0
    apply hw₁0
    have := h1 w₁ hw₁
    rw [h0, zero_smul] at this
    exact r.injective (this.trans hr0.symm)
  have h2 : ∀ φ : V →ₗ[F] F, (∀ x ∈ W, φ x = 0) → ∀ v, φ (r v) = σ (φ v) * l := by
    intro φ hφ v
    have h := hcomm w₁ φ hw₁ hφ v
    rw [hradd, hσ, h1 w₁ hw₁, smul_smul] at h
    have h' := add_left_cancel h
    have : (σ (φ v) * l - φ (r v)) • w₁ = 0 := by
      rw [sub_smul, h', sub_self]
    rcases smul_eq_zero.1 this with h0 | h0
    · exact (sub_eq_zero.1 h0).symm
    · exact absurd h0 hw₁0
  have hσid : ∀ c : F, σ c = c := by
    intro c
    have hc := h2 (c • φ₀) (fun x hx => by rw [LinearMap.smul_apply, hφ₀ x hx, smul_zero]) v₀
    have hc' : c * l = σ c * l := by
      simpa [LinearMap.smul_apply, hv₀, hl] using hc
    exact (mul_right_cancel₀ hl0 hc').symm
  have h3 : ∀ v, r v - l • v ∈ W := by
    intro v
    by_contra hv
    obtain ⟨φ, hφv, hφW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
    have hφ : ∀ x ∈ W, φ x = 0 := fun x hx => by
      have : φ x ∈ W.map φ := ⟨x, hx, rfl⟩
      rw [hφW] at this
      simpa using this
    apply hφv
    have hrv := h2 φ hφ v
    have hsub : r v - l • v = r v + (-(l • v)) := sub_eq_add_neg _ _
    rw [map_sub, hrv, hσid, map_smul, smul_eq_mul]
    ring
  have hrsmul : ∀ (c : F) (v : V), r (c • v) = c • r v := fun c v => by rw [hσ, hσid]
  have hrN : ∀ v, r (r v - l • v) = l • (r v - l • v) := fun v => h1 _ (h3 v)
  have hsplit : ∀ v, r v = l • v + (r v - l • v) := fun v => by abel
  have hpow : ∀ k : ℕ, ∀ v, (r ^ (k + 1)) v =
      l ^ (k + 1) • v + ((((k + 1 : ℕ) : F)) * l ^ k) • (r v - l • v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', Equiv.Perm.mul_apply, ih v, hradd, hrsmul, hrsmul, hrN v]
      nth_rewrite 1 [hsplit v]
      push_cast
      module
  obtain ⟨j, hj⟩ := hm
  have hm1 : (((2 * j + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [show (2 : F) = 0 from CharP.ofNat_eq_zero F 2, zero_mul, zero_add]
  have hone : ∀ v, v = l ^ (2 * j + 1) • v + (l ^ (2 * j)) • (r v - l • v) := by
    intro v
    have := hpow (2 * j) v
    rw [← hj, hrm, hj, hm1, one_mul, Equiv.Perm.one_apply] at this
    exact this
  have hlm : l ^ (2 * j + 1) = 1 := by
    have := hone w₁
    rw [h1 w₁ hw₁, sub_self, smul_zero, add_zero] at this
    have h' : (1 - l ^ (2 * j + 1)) • w₁ = 0 := by
      rw [sub_smul, one_smul, ← this, sub_self]
    rcases smul_eq_zero.1 h' with h0 | h0
    · exact (sub_eq_zero.1 h0).symm
    · exact absurd h0 hw₁0
  refine ⟨l, fun v => ?_⟩
  have := hone v
  rw [hlm, one_smul] at this
  have h' : l ^ (2 * j) • (r v - l • v) = 0 := by
    have := congrArg (fun x => x - v) this
    simpa using this.symm
  rcases smul_eq_zero.1 h' with h0 | h0
  · exact absurd (pow_eq_zero_iff'.1 h0).1 hl0
  · exact sub_eq_zero.1 h0

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
