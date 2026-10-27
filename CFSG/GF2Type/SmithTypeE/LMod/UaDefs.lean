module

public import CFSG.GF2Type.SmithTypeE.LMod.T6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open scoped Pointwise

section Defs


@[expose] def wPlane (i : ℕ) : Set (Fin 1953) := ↑(planeSet i)

theorem mem_wPlane {i : ℕ} {a : Fin 1953} : a ∈ wPlane i ↔ inPlane i a.val = true := by
  simp [wPlane, mem_planeSet]

theorem wPlane_finite (i : ℕ) : (wPlane i).Finite := Finset.finite_toSet _

theorem ncard_wPlane {i : ℕ} (hi : i < 1395) : (wPlane i).ncard = 49 := by
  rw [wPlane, Set.ncard_coe_finset, card_planeSet hi]

theorem wPlane_injective {i j : ℕ} (hi : i < 1395) (hj : j < 1395) (h : wPlane i = wPlane j) :
    i = j :=
  planeSet_injective hi hj (Finset.coe_injective h)

theorem image_coe_finset (g : Equiv.Perm (Fin 1953)) (s : Finset (Fin 1953)) :
    ⇑g '' (s : Set (Fin 1953)) = ↑(s.map g.toEmbedding) :=
  (Finset.coe_map g.toEmbedding s).symm

@[expose] def UA (i : ℕ) : Subgroup (Equiv.Perm (Fin 1953)) :=
  Subgroup.closure (tvP '' wPlane i)

@[expose] def PA (i : ℕ) : Subgroup (Equiv.Perm (Fin 1953)) :=
  T6 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane i)

theorem mem_stabilizer_wPlane {i : ℕ} {g : Equiv.Perm (Fin 1953)} :
    g ∈ MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane i) ↔ ⇑g '' wPlane i = wPlane i := by
  rw [MulAction.mem_stabilizer_iff]
  exact Iff.rfl

theorem mem_PA {i : ℕ} {g : Equiv.Perm (Fin 1953)} :
    g ∈ PA i ↔ g ∈ T6 ∧ ⇑g '' wPlane i = wPlane i := by
  rw [PA, Subgroup.mem_inf, mem_stabilizer_wPlane]

theorem tvP_mem_UA {i : ℕ} {p : Fin 1953} (hp : p ∈ wPlane i) : tvP p ∈ UA i :=
  Subgroup.subset_closure ⟨p, hp, rfl⟩

theorem UA_le_T6 {i : ℕ} : UA i ≤ T6 := by
  rw [UA, Subgroup.closure_le]
  rintro _ ⟨p, -, rfl⟩
  exact tvP_mem p

theorem image_wPlane_tvP {k : Fin 1953} {i : ℕ} (hi : i < 1395) :
    ⇑(tvP k) '' wPlane i = wPlane (planeImg k.val i) := by
  have h := map_planeSet_tvP k.2 hi
  rw [wPlane, wPlane, image_coe_finset, h]

theorem exists_image_wPlane {g : Equiv.Perm (Fin 1953)} (hg : g ∈ T6) {j : ℕ} (hj : j < 1395) :
    ∃ j' < 1395, ⇑g '' wPlane j = wPlane j' := by
  obtain ⟨j', hj', e⟩ := permPlanes_of_mem hg j hj
  exact ⟨j', hj', by rw [wPlane, wPlane, image_coe_finset, e]⟩

theorem image_wPlane_inv {g : Equiv.Perm (Fin 1953)} {j j' : ℕ}
    (h : ⇑g '' wPlane j = wPlane j') : ⇑g⁻¹ '' wPlane j' = wPlane j := by
  rw [← h, ← Set.image_comp]
  simp

theorem image_wPlane_smul (g : T6) (i : Fin 1395) :
    ⇑(g : Equiv.Perm (Fin 1953)) '' wPlane i.val = wPlane (g • i).val := by
  rw [wPlane, wPlane, image_coe_finset, map_planeSet_smul]

end Defs

end CFSG.GF2Type.SmithTypeE.LMod
