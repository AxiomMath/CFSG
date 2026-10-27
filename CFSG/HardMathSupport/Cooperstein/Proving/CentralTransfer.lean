module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Transfer

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Cooperstein.Proving

theorem pow_index_eq_one_of_central_of_perfect {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] (B : Subgroup H) (hB : ∀ x y : B, x * y = y * x)
    {z : H} (hz : z ∈ Subgroup.center H) :
    z ^ B.index = 1 := by
  classical
  let _ : CommGroup B := { (inferInstance : Group B) with mul_comm := hB }
  let f : H →* B := MonoidHom.transfer (MonoidHom.id B)
  have hcomm : ∀ x y : H, f (⁅x, y⁆ : H) = 1 := by
    intro x y
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hker : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    exact MonoidHom.mem_ker.mpr (hcomm a b)
  have hc : (⊤ : Subgroup H) = ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ :=
    (Group.IsPerfect.commutator_eq_top (G := H)).symm
  have htop : (⊤ : Subgroup H) ≤ f.ker := by
    rw [hc]
    exact hker
  have hf1 : f z = 1 := MonoidHom.mem_ker.mp (htop (Subgroup.mem_top z))
  have key : ∀ (k : ℕ) (g₀ : H), g₀⁻¹ * z ^ k * g₀ ∈ B → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center H := Subgroup.pow_mem _ hz k
    rw [Subgroup.mem_center_iff] at hzk
    rw [mul_assoc, ← hzk g₀, inv_mul_cancel_left]
  have hVz := MonoidHom.transfer_eq_pow (MonoidHom.id B) z key
  have h3 := congrArg Subtype.val (hVz.symm.trans hf1)
  simpa using h3

end CFSG.HardMathSupport.Cooperstein.Proving

end
