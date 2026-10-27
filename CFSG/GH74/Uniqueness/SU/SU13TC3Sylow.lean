module

public import CFSG.GH74.Uniqueness.SU.SU13TB0Syl

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G]

theorem centralizes_of_normalizes_zpowers {s g : G} (hs : orderOf s = 3)
    (hg : g ∈ normalizer (zpowers s : Set G)) (hodd : Odd (orderOf g)) : g * s = s * g := by
  have hs3 : s ^ 3 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hsinv : s ^ 2 = s⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]; exact hs3
  have hmem : g * s * g⁻¹ ∈ zpowers s := (mem_normalizer_iff.mp hg s).mp (mem_zpowers s)
  obtain ⟨k, hk⟩ := hmem
  have hk' : g * s * g⁻¹ = s ^ (k % 3) := by
    have := zpow_mod_orderOf s k
    rw [hs] at this
    rw [← hk]
    simpa using this.symm
  have hs1 : s ≠ 1 := by
    intro h; rw [h, orderOf_one] at hs; omega
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hk'
    apply hs1
    have : s = g⁻¹ * 1 * g := by rw [← hk']; group
    simpa using this
  · rw [h1, zpow_one] at hk'
    calc g * s = (g * s * g⁻¹) * g := by group
      _ = s * g := by rw [hk']
  · rw [h2] at hk'
    have hk2 : g * s * g⁻¹ = s⁻¹ := by
      rw [hk']
      have : s ^ (2 : ℤ) = s ^ 2 := by norm_cast
      rw [this, hsinv]
    have hg2 : (g * g) * s = s * (g * g) := by
      have h3 : g * s⁻¹ * g⁻¹ = s := by
        calc g * s⁻¹ * g⁻¹ = (g * s * g⁻¹)⁻¹ := by group
          _ = s := by rw [hk2, inv_inv]
      calc g * g * s = g * (g * s * g⁻¹) * g := by group
        _ = g * s⁻¹ * g := by rw [hk2]
        _ = (g * s⁻¹ * g⁻¹) * g * g := by group
        _ = s * (g * g) := by rw [h3]; group
    obtain ⟨m, hm⟩ := hodd
    have hgm : g = (g * g) ^ (m + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf g + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have hc : Commute (g * g) s := hg2
    have := (hc.pow_left (m + 1)).eq
    rw [← hgm] at this
    exact this

@[expose] def TT (W D : Subgroup G) (hD : ∀ d ∈ D, ∀ w ∈ W, d * w * d⁻¹ ∈ W) : Subgroup G where
  carrier := {x | ∃ w ∈ W, ∃ d ∈ D, x = w * d}
  one_mem' := ⟨1, W.one_mem, 1, D.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨w, hw, d, hd, rfl⟩ ⟨w', hw', d', hd', rfl⟩
    refine ⟨w * (d * w' * d⁻¹), W.mul_mem hw (hD d hd w' hw'), d * d', D.mul_mem hd hd', ?_⟩
    group
  inv_mem' := by
    rintro _ ⟨w, hw, d, hd, rfl⟩
    refine ⟨d⁻¹ * w⁻¹ * d, ?_, d⁻¹, D.inv_mem hd, ?_⟩
    · have := hD d⁻¹ (D.inv_mem hd) w⁻¹ (W.inv_mem hw)
      simpa using this
    · group

theorem le_TT {W D : Subgroup G} (hD : ∀ d ∈ D, ∀ w ∈ W, d * w * d⁻¹ ∈ W) : W ≤ TT W D hD :=
  fun w hw => ⟨w, hw, 1, D.one_mem, by simp⟩

theorem le_TT' {W D : Subgroup G} (hD : ∀ d ∈ D, ∀ w ∈ W, d * w * d⁻¹ ∈ W) : D ≤ TT W D hD :=
  fun d hd => ⟨1, W.one_mem, d, hd, by simp⟩

theorem mem_normalizer_of_center {T P : Subgroup G} (hPc : ∀ x ∈ P, ∀ y ∈ T, x * y = y * x)
    (hPT : P ≤ T) (hZ : ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x ∈ P) {g : G}
    (hg : g ∈ normalizer (T : Set G)) : g ∈ normalizer (P : Set G) := by
  have key : ∀ {g : G}, g ∈ normalizer (T : Set G) → ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g hg x hx
    refine hZ _ ((mem_normalizer_iff.mp hg x).mp (hPT hx)) (fun y hy => ?_)
    have hy' : g⁻¹ * y * g ∈ T := by
      have := (mem_normalizer_iff.mp (inv_mem hg) y).mp hy
      simpa [mul_assoc] using this
    have := hPc x hx _ hy'
    calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [this]
      _ = y * (g * x * g⁻¹) := by group
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key hg x, fun hx => ?_⟩
  have := key (inv_mem hg) _ hx
  simpa [mul_assoc] using this

end CFSG.GH74.Uniqueness.SU.SU13
