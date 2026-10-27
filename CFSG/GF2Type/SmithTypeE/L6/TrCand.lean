module

public import CFSG.GF2Type.SmithTypeE.L6.IdAutCent
public import CFSG.GF2Type.SmithTypeE.L6.TrBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup Module QuadraticMap CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod
  CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
open CFSG.LargeExtraspecial.SMod20 (V decode decode_xor decode_zero bit)

attribute [local irreducible] tvIdxTab tvTab tvImg tvList planePtsArr flagArr wtArr maskArr annArr

section Fix

theorem mem_UA_of_fix {π : Equiv.Perm (Fin 1953)}
    (hπ : π ∈ normalizer (T6 : Set (Equiv.Perm (Fin 1953)))) {j : ℕ} (hj : j < 1395)
    (hfix : ∀ p ∈ wPlane j, π p = p) : π ∈ UA j := by
  have hπ' : IsTvAut π := isTvAut_of_mem_normalizer hπ
  have hU := autPerm_mem_UA_of_commute hj (normAut π hπ) fun u hu => by
    rw [autPerm_normAut]
    change u ∈ Subgroup.closure (tvP '' wPlane j) at hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      have e := hπ' p
      rw [hfix p hp] at e
      calc tvP p * π = π * tvP p * π⁻¹ * π := by rw [e]
        _ = π * tvP p := by group
    | one => simp
    | mul x y _ _ hx hy =>
      calc x * y * π = x * (y * π) := by group
        _ = x * (π * y) := by rw [hy]
        _ = (x * π) * y := by group
        _ = (π * x) * y := by rw [hx]
        _ = π * (x * y) := by group
    | inv x _ hx =>
      calc x⁻¹ * π = x⁻¹ * (π * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * π) * x⁻¹ := by rw [hx]
        _ = π * x⁻¹ := by group
  rw [autPerm_normAut] at hU
  exact hU

end Fix

theorem image_wPlane_eq_of_subset {i j : ℕ} (hi : i < 1395) (hj : j < 1395)
    {π : Equiv.Perm (Fin 1953)} (h : ∀ p ∈ wPlane i, π p ∈ wPlane j) :
    ⇑π '' wPlane i = wPlane j := by
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨p, hp, rfl⟩
    exact h p hp
  · rw [Set.ncard_image_of_injective _ π.injective, ncard_wPlane hi, ncard_wPlane hj]
  · exact wPlane_finite j

theorem planePtsArr_size {i : ℕ} (hi : i < 1395) : planePtsArr[i]!.size = 49 := by
  rw [planePtsArr_get hi, ← card_planeSet_eq]
  exact card_planeSet hi

theorem exists_planePtsArr_of_mem {i : ℕ} (hi : i < 1395) {p : Fin 1953} (hp : p ∈ wPlane i) :
    ∃ k < 49, (planePtsArr[i]!)[k]! = p.val := by
  have hp' : p.val ∈ planePtsArr[i]! := by
    rw [planePtsArr_get hi]
    exact mem_planePts.2 ⟨p.2, (mem_wPlane.1 hp)⟩
  obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.1 hp'
  refine ⟨k, by rwa [planePtsArr_size hi] at hk, ?_⟩
  rw [getElem!_pos _ k hk]
  exact hke

end CFSG.GF2Type.SmithTypeE.L6
