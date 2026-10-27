module

public import CFSG.LargeExtraspecial.S14SMKTransBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module QuadraticMap CFSG.Open CFSG.Fischer CFSG.SmithE
  CFSG.LargeExtraspecial.SMod20 CFSG.RankThree.OrthogonalInvolutions CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Fischer.Native

theorem mem_UA_of_fix {π : Equiv.Perm (Fin 693)}
    (hπ : π ∈ normalizer (T46 : Set (Equiv.Perm (Fin 693)))) {j : ℕ} (hj : j < 891)
    (hfix : ∀ p ∈ wPlane j, π p = p) : π ∈ UA j := by
  have hpol := isPolarAut_of_mem_normalizer hπ
  have hU := autPerm_mem_UAloc_of_commute hj (normAut π hπ) fun u hu => by
    rw [autPerm_normAut]
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      have hp' : p ∈ wPlane j := by
        rw [wPlane_eq_planeSet hj, ← planePoints_eq_planeSet hj]
        exact hp
      have e := hpol.mul_tvP_mul_inv p
      rw [hfix p hp'] at e
      calc π * tvP p = π * tvP p * π⁻¹ * π := by group
        _ = tvP p * π := by rw [e]
    | one => simp
    | mul x y _ _ hx hy =>
      calc π * (x * y) = π * x * y := by group
        _ = x * (π * y) := by rw [hx]; group
        _ = x * y * π := by rw [hy]; group
    | inv x _ hx =>
      calc π * x⁻¹ = x⁻¹ * (x * π) * x⁻¹ := by group
        _ = x⁻¹ * π := by rw [← hx]; group
  rw [autPerm_normAut, UAloc_eq_UA hj] at hU
  exact hU

variable {A : SMod20.V ≃ₗ[ZMod 2] SMod20.V} {π : Equiv.Perm (Fin 693)}

end CFSG.LargeExtraspecial.S14.SMK
