module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Def
public import CFSG.GH74.KGroups.Generic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GH74.KGroups

theorem l34g_c6_of_autModel {K : Type} [Group K] {G : Type} [Group G] (M : AutModel K G)
    (h : ∀ τ ∈ M.A, τ ^ 2 = 1 → ∀ y ∈ M.P, ∀ u ∈ M.P, y ^ 2 = 1 → y ≠ 1 → u ^ 3 = 1 → u ≠ 1 →
      y * u = u * y → τ * y = y * τ → τ * u = u * τ → τ = 1 ∨ τ = y) :
    L34GC6 K := by
  intro σ hσ y u hy hu hyu hσy hσu
  have hσ2 : σ ^ 2 = 1 := by rw [pow_two]; exact hσ
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hu3 : u ^ 3 = 1 := hu ▸ pow_orderOf_eq_one u
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    omega
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    omega
  have hcomm : ∀ x : K, σ x = x → (M.Φ σ : G) * (M.e x : G) = (M.e x : G) * (M.Φ σ : G) := by
    intro x hx
    have h1 := M.spec σ x
    rw [hx] at h1
    calc (M.Φ σ : G) * (M.e x : G)
        = (M.Φ σ : G) * (M.e x : G) * (M.Φ σ : G)⁻¹ * (M.Φ σ : G) := by group
      _ = (M.e x : G) * (M.Φ σ : G) := by rw [← h1]
  have key := h (M.Φ σ : G) (M.Φ σ).2 (by rw [← M.Φ_pow, hσ2, M.Φ_one]) (M.e y : G) (M.e y).2
    (M.e u : G) (M.e u).2
    (by rw [← Subgroup.coe_pow, ← map_pow, hy2, map_one, Subgroup.coe_one])
    (fun h1 => hy1 (M.e.injective (Subtype.ext (by rw [map_one]; exact h1))))
    (by rw [← Subgroup.coe_pow, ← map_pow, hu3, map_one, Subgroup.coe_one])
    (fun h1 => hu1 (M.e.injective (Subtype.ext (by rw [map_one]; exact h1))))
    (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hyu])
    (hcomm y hσy) (hcomm u hσu)
  rcases key with h1 | h1
  · exact Or.inl (M.Φ_eq_one.1 h1)
  · refine Or.inr (MulEquiv.ext fun x => ?_)
    rw [MulAut.conj_apply]
    apply M.e.injective
    apply Subtype.ext
    have h2 := M.spec σ x
    rw [h1] at h2
    rw [h2]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

end CFSG.OddStandard.SmallF3.Omega
