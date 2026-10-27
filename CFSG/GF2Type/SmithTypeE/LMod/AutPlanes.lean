module

public import CFSG.GF2Type.SmithTypeE.LMod.Aut
public import CFSG.GF2Type.SmithTypeE.LMod.UaDefs
public import Certificates.Certificate38605

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open scoped Pointwise

attribute [local irreducible] tvIdxTab tvTab tvImg tvList dualIdx

theorem swapPlanesCheck_holds : chkSwapPlanes = true :=
  Certificates.certificate38605

theorem swapPlanes_parts {i : ℕ} (hi : i < 1395) :
    dualIdx i < 1395 ∧ maskArr[dualIdx i]! = annArr[i]! ∧ annArr[dualIdx i]! = maskArr[i]! := by
  have h := swapPlanesCheck_holds
  simp only [chkSwapPlanes, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h i hi
  exact ⟨h1, h2, h3⟩

section Swap

theorem tvPair_swapIdx (k : Fin 1953) :
    tvPair (swapIdx k).val = ((tvPair k.val).2, (tvPair k.val).1) := by
  obtain ⟨a1, a2, -⟩ := tvListFacts.entry k.val k.2
  obtain ⟨b1, b2, -⟩ := tvListFacts.entry (swapIdx k).val (swapIdx k).2
  exact Prod.ext (dec6_inj b1 a2 (tvVec_swapIdx k)) (dec6_inj b2 a1 (tvForm_swapIdx k))

theorem inPlane_swapIdx {i : ℕ} (hi : i < 1395) (p : Fin 1953) :
    inPlane (dualIdx i) (swapIdx p).val = inPlane i p.val := by
  obtain ⟨-, hm, ha⟩ := swapPlanes_parts hi
  unfold inPlane
  rw [tvPair_swapIdx, hm, ha]
  simp only [Bool.and_comm]

theorem swapIdx_mem_wPlane_iff {i : ℕ} (hi : i < 1395) (p : Fin 1953) :
    swapIdx p ∈ wPlane (dualIdx i) ↔ p ∈ wPlane i := by
  rw [mem_wPlane, mem_wPlane, inPlane_swapIdx hi]

theorem image_wPlane_swapPerm {i : ℕ} (hi : i < 1395) :
    ⇑swapPerm '' wPlane i = wPlane (dualIdx i) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (swapIdx_mem_wPlane_iff hi p).2 hp
  · intro hq
    refine ⟨swapIdx q, ?_, swapIdx_swapIdx q⟩
    rw [← swapIdx_mem_wPlane_iff hi, swapIdx_swapIdx]
    exact hq

theorem exists_image_wPlane_autPerm (α : MulAut T6) {j : ℕ} (hj : j < 1395) :
    ∃ j' < 1395, ⇑(autPerm α) '' wPlane j = wPlane j' := by
  obtain ⟨A, h | h⟩ := autPerm_form α
  · rw [h]
    exact exists_image_wPlane (actPerm_mem A) hj
  · rw [h]
    obtain ⟨j', hj', e⟩ := exists_image_wPlane (actPerm_mem A) (swapPlanes_parts hj).1
    refine ⟨j', hj', ?_⟩
    rw [Equiv.Perm.coe_mul, Set.image_comp, image_wPlane_swapPerm hj, e]

theorem autPerm_planes (α : MulAut T6) {i : ℕ} (hi : i < 1395) :
    ∃ j < 1395, ∀ p : Fin 1953, p ∈ wPlane i ↔ autPerm α p ∈ wPlane j := by
  obtain ⟨j, hj, e⟩ := exists_image_wPlane_autPerm α hi
  refine ⟨j, hj, fun p => ?_⟩
  rw [← e]
  exact ((autPerm α).injective.mem_set_image).symm

theorem planes_unique {π : Equiv.Perm (Fin 1953)} {i j j' : ℕ} (hj : j < 1395) (hj' : j' < 1395)
    (h : ∀ p : Fin 1953, p ∈ wPlane i ↔ π p ∈ wPlane j)
    (h' : ∀ p : Fin 1953, p ∈ wPlane i ↔ π p ∈ wPlane j') : j = j' := by
  apply wPlane_injective hj hj'
  ext q
  rw [← π.apply_symm_apply q, ← h, ← h']

@[expose] noncomputable def autPlaneFun (α : MulAut T6) (i : Fin 1395) : Fin 1395 :=
  ⟨Classical.choose (autPerm_planes α i.2), (Classical.choose_spec (autPerm_planes α i.2)).1⟩

theorem autPlaneFun_spec (α : MulAut T6) (i : Fin 1395) (p : Fin 1953) :
    p ∈ wPlane i ↔ autPerm α p ∈ wPlane (autPlaneFun α i) :=
  (Classical.choose_spec (autPerm_planes α i.2)).2 p

theorem autPlaneFun_eq {α : MulAut T6} {i j : Fin 1395}
    (h : ∀ p : Fin 1953, p ∈ wPlane i ↔ autPerm α p ∈ wPlane j) : autPlaneFun α i = j :=
  Fin.ext (planes_unique (autPlaneFun α i).2 j.2 (autPlaneFun_spec α i) h)

theorem autPlaneFun_mul (α β : MulAut T6) (i : Fin 1395) :
    autPlaneFun (α * β) i = autPlaneFun α (autPlaneFun β i) := by
  apply autPlaneFun_eq
  intro p
  rw [map_mul, Equiv.Perm.mul_apply, autPlaneFun_spec β i, autPlaneFun_spec α]

theorem autPlaneFun_one (i : Fin 1395) : autPlaneFun 1 i = i := by
  apply autPlaneFun_eq
  intro p
  rw [map_one, Equiv.Perm.one_apply]

@[expose] noncomputable def autPlane : MulAut T6 →* Equiv.Perm (Fin 1395) where
  toFun α :=
    { toFun := autPlaneFun α
      invFun := autPlaneFun α⁻¹
      left_inv := fun i => by rw [← autPlaneFun_mul, inv_mul_cancel, autPlaneFun_one]
      right_inv := fun i => by rw [← autPlaneFun_mul, mul_inv_cancel, autPlaneFun_one] }
  map_one' := Equiv.ext autPlaneFun_one
  map_mul' α β := Equiv.ext (autPlaneFun_mul α β)

theorem autPlane_spec (α : MulAut T6) (i : Fin 1395) (p : Fin 1953) :
    p ∈ wPlane i ↔ autPerm α p ∈ wPlane (autPlane α i) :=
  autPlaneFun_spec α i p

end Swap

end CFSG.GF2Type.SmithTypeE.LMod
