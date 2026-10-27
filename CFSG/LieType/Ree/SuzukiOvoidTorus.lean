module

public import CFSG.LieType.Ree.SuzukiLocalData
public import CFSG.LieType.Ree.SuzukiTorusIdentities

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint Matrix
open scoped LinearAlgebra.Projectivization

variable (a : ℕ) {K : Type} [Field K]

theorem suzuki_smul_mk_eq (g : suzukiGroup a K) {x y : Fin 4 → K} (hx : x ≠ 0) (hy : y ≠ 0)
    (c : Kˣ) (h : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x = c • y) :
    g • Projectivization.mk K x hx = Projectivization.mk K y hy := by
  rw [Subgroup.smul_def, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  exact ⟨c, h.symm⟩

theorem suzukiN_smul [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (μ u v : K) :
    suzukiN a (μ * u) (μ ^ (2 ^ (a + 1) + 1) * v) = μ ^ (2 ^ (a + 1) + 2) * suzukiN a u v := by
  obtain ⟨-, -, hθθ⟩ := suzuki_frob_data a hK
  have hμ : (μ ^ (2 ^ (a + 1) + 1)) ^ 2 ^ (a + 1) = μ ^ 2 * μ ^ 2 ^ (a + 1) := by
    rw [← pow_mul, add_mul, one_mul, pow_add, pow_mul, hθθ]
  rw [suzukiN, suzukiN, mul_pow, mul_pow, hμ]
  ring

theorem suzuki_ovoid_torus_action
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ)
    (u v : K) :
    suzukiDElt a K l • suzukiInfty K = suzukiInfty K ∧
      suzukiDElt a K l • suzukiLine a K u v =
        suzukiLine a K ((l : K)⁻¹ * u) (((l : K) ^ (2 ^ (a + 1) + 1))⁻¹ * v) := by
  have hx : (l : K) ≠ 0 := l.ne_zero
  have hm : (l : K) ^ 2 ^ a ≠ 0 := pow_ne_zero _ hx
  refine ⟨suzuki_smul_mk_eq a _ _ _ (l ^ (-1 - (2 ^ a : ℤ))) ?_,
    suzuki_smul_mk_eq a _ _ _ (l ^ (1 + (2 ^ a : ℤ))) ?_⟩
  · rw [coe_suzukiDElt, suzukiD]
    ext i
    fin_cases i <;> simp [mulVec_diagonal, Units.smul_def]
  · have hN := suzukiN_smul a hK (l : K)⁻¹ u v
    rw [inv_pow] at hN
    rw [hN, coe_suzukiDElt, suzukiD_eq]
    have h1 : ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) = (l : K) * (l : K) ^ 2 ^ a := by
      rw [_root_.zpow_add, zpow_one, zpow_two_pow_eq]
      simp
    ext i
    fin_cases i <;> simp [mulVec_diagonal, h1, Units.smul_def, pow_add]
    all_goals field_simp
    all_goals ring

end CFSG.LieType.Ree
