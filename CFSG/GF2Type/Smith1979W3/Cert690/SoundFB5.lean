module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GF2Type.Smith1979W3.Cert690.Check

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 Module

theorem mem_involutions_iff_of_ok {D : PGLData} (h : pglInvolutionsOK D = true) {x : ℕ} :
    x ∈ D.involutions ↔ x ∈ D.elems ∧ isInvCode x = true := by
  simp only [pglInvolutionsOK, Array.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  have hiff : ∀ i (hi : i < D.elems.size),
      isInvCode D.elems[i] = D.involutions.contains D.elems[i] := fun i hi => h.1 i hi
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
    have hxE : D.elems.contains D.involutions[i] = true := h.2 i hi
    have hmem : D.involutions[i] ∈ D.elems := Array.contains_iff_mem.mp hxE
    obtain ⟨j, hj, hjeq⟩ := Array.mem_iff_getElem.mp hmem
    have hcont : D.involutions.contains D.elems[j] = true := by
      rw [hjeq]
      exact Array.contains_iff_mem.mpr (Array.mem_iff_getElem.mpr ⟨i, hi, rfl⟩)
    have h1 := hiff j hj
    rw [hcont, hjeq] at h1
    exact ⟨hmem, h1⟩
  · rintro ⟨hxE, hxI⟩
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hxE
    have h1 := hiff j hj
    rw [hxI] at h1
    exact Array.contains_iff_mem.mp h1.symm

theorem mem_outers_iff_of_ok {D : PGLData} (h : pglOutersOK D = true) {x : ℕ} :
    x ∈ D.outers ↔ x ∈ D.elems ∧ isInvCode x = true ∧ x ∉ D.elems0 := by
  simp only [pglOutersOK, Array.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  have hiff : ∀ i (hi : i < D.elems.size),
      (isInvCode D.elems[i] && !D.elems0.contains D.elems[i]) =
        D.outers.contains D.elems[i] := fun i hi => h.1 i hi
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
    have hxE : D.outers[i] ∈ D.elems :=
      Array.contains_iff_mem.mp (h.2 i hi)
    obtain ⟨j, hj, hjeq⟩ := Array.mem_iff_getElem.mp hxE
    have hxout : D.outers.contains D.elems[j] = true := by
      rw [hjeq]
      exact Array.contains_iff_mem.mpr (Array.mem_iff_getElem.mpr ⟨i, hi, rfl⟩)
    have h := hiff j hj
    rw [hxout, hjeq] at h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    refine ⟨hxE, h1, ?_⟩
    intro hmem
    have hcont : D.elems0.contains D.outers[i] = true := Array.contains_iff_mem.mpr hmem
    rw [hcont] at h2
    exact Bool.noConfusion h2
  · rintro ⟨hxE, hxI, hx0⟩
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hxE
    have h0 : D.elems0.contains D.elems[j] = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      exact hx0 (Array.contains_iff_mem.mp hc)
    have hval : (isInvCode D.elems[j] && !D.elems0.contains D.elems[j]) = true := by
      rw [hxI, h0]; rfl
    have h := hiff j hj
    rw [hval] at h
    exact Array.contains_iff_mem.mp h.symm

end CFSG.GF2Type.Smith1979W3.Cert690
