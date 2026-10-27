module

public import CFSG.LargeExtraspecial.AS35ZSDisj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap
open CFSG.Blueprint.Fischer (K)

namespace ZSHyp

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem L_apply_eq_self {m : ℕ} {ρ : PG (m + 2) →* (V ≃ₗ[ZMod 2] V)} (h : ZSHyp (m + 2) q ρ)
    {l : SUid frob (m + 2)} (hl : l ∈ L m) {v : V} (hv : v ∈ lineA ρ (v₀ m)) :
    rs ρ l v = v := by
  induction hl using Subgroup.closure_induction generalizing v with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact h.apply_eq_self_of_perp v₀_ne_zero herm_v₀_v₀ hw.1 hw.2.1 hw.2.2.1 hv
  | one => simp
  | mul x y _ _ ihx ihy =>
    rw [map_mul, LinearEquiv.mul_apply, ihy hv, ihx hv]
  | inv x hxL ihx =>
    have hxv : x⁻¹ • v₀ m = v₀ m := smul_v₀_of_mem_L (Subgroup.inv_mem (L m) hxL)
    have hw : rs ρ x⁻¹ v ∈ lineA ρ (v₀ m) := by
      have := apply_mem_lineA (ρ := ρ) x⁻¹ (herm_v₀_v₀ (n := m)) hv
      rwa [hxv] at this
    calc rs ρ x⁻¹ v = rs ρ x (rs ρ x⁻¹ v) := (ihx hw).symm
      _ = v := by
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl

theorem sq_mem_L {m : ℕ} (hm : 2 ≤ m) {g : SUid frob (m + 2)} (hg : g • v₀ m = v₀ m) :
    g ^ 2 ∈ L m := by
  rcases eq_or_ne m 3 with rfl | h3
  · exact sq_mem_L_of_mem_Stab hm sq_mem_T_three hg
  · exact Subgroup.pow_mem _ (mem_L_of_mem_Stab hm h3 hg) 2

theorem sq_apply_eq_self_of_fix {ρ : PG n →* (V ≃ₗ[ZMod 2] V)} (h : ZSHyp n q ρ)
    {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0) {g : SUid frob n} (hg : g • x = x)
    {v : V} (hv : v ∈ lineA ρ x) : rs ρ (g ^ 2) v = v := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := h.four_le; omega⟩
  obtain ⟨k, -, hk⟩ := exists_mem_T_smul_eq_of_iso isUnitaryInvolution_frob h.three_le hx0 hx
    v₀_ne_zero herm_v₀_v₀
  have hg' : (k * g * k⁻¹) • v₀ m = v₀ m := by
    rw [mul_smul, mul_smul, ← hk, inv_smul_smul, hg]
  have hL := sq_mem_L (by have := h.four_le; omega) hg'
  have hkv : rs ρ k v ∈ lineA ρ (v₀ m) := by
    have := apply_mem_lineA (ρ := ρ) k hx hv
    rwa [hk] at this
  have e := h.L_apply_eq_self hL hkv
  have e2 : (k * g * k⁻¹) ^ 2 = k * g ^ 2 * k⁻¹ := by rw [_root_.sq, _root_.sq]; group
  rw [e2, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    ← LinearEquiv.mul_apply (rs ρ k⁻¹), ← map_mul, inv_mul_cancel, map_one] at e
  exact (rs ρ k).injective e

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS
