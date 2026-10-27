module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.OrderOfElement

open SemidirectProduct

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}

theorem mem_centralizer_range_inl_iff (x : G ⋊[φ] A) :
    x ∈ Subgroup.centralizer ((inl : G →* G ⋊[φ] A).range : Set (G ⋊[φ] A)) ↔
      ∀ h : G, x.left * φ x.right h = h * x.left := by
  constructor
  · intro hx h
    have h2 := congrArg SemidirectProduct.left (hx (inl h) ⟨h, rfl⟩)
    simpa [SemidirectProduct.mul_left] using h2.symm
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨h, rfl⟩
    exact SemidirectProduct.ext (by simp [SemidirectProduct.mul_left, (hx h).symm])
      (by simp [SemidirectProduct.mul_right])

theorem map_right_eq_conj_of_mem_centralizer_range_inl {x : G ⋊[φ] A}
    (hx : x ∈ Subgroup.centralizer ((inl : G →* G ⋊[φ] A).range : Set (G ⋊[φ] A))) :
    φ x.right = MulAut.conj x.left⁻¹ := by
  rw [mem_centralizer_range_inl_iff] at hx
  ext h
  simp only [MulAut.conj_apply, inv_inv]
  rw [mul_assoc, ← hx h, inv_mul_cancel_left]

theorem map_right_eq_one_of_mem_centralizer_range_inl
    (hcop : (Nat.card G).Coprime (Nat.card A)) {x : G ⋊[φ] A}
    (hx : x ∈ Subgroup.centralizer ((inl : G →* G ⋊[φ] A).range : Set (G ⋊[φ] A))) :
    φ x.right = 1 := by
  have hA : orderOf (φ x.right) ∣ Nat.card A :=
    (orderOf_map_dvd φ x.right).trans (orderOf_dvd_natCard _)
  have hG : orderOf (φ x.right) ∣ Nat.card G := by
    rw [map_right_eq_conj_of_mem_centralizer_range_inl hx]
    exact (orderOf_map_dvd MulAut.conj _).trans (orderOf_dvd_natCard _)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hG hA)

theorem right_eq_one_of_mem_centralizer_range_inl
    (hcop : (Nat.card G).Coprime (Nat.card A)) (hφ : Function.Injective φ) {x : G ⋊[φ] A}
    (hx : x ∈ Subgroup.centralizer ((inl : G →* G ⋊[φ] A).range : Set (G ⋊[φ] A))) :
    x.right = 1 :=
  hφ (by rw [map_right_eq_one_of_mem_centralizer_range_inl hcop hx, map_one])

theorem left_mem_center_of_mem_centralizer_range_inl
    (hcop : (Nat.card G).Coprime (Nat.card A)) (hφ : Function.Injective φ) {x : G ⋊[φ] A}
    (hx : x ∈ Subgroup.centralizer ((inl : G →* G ⋊[φ] A).range : Set (G ⋊[φ] A))) :
    x.left ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h := (mem_centralizer_range_inl_iff x).mp hx g
  rw [right_eq_one_of_mem_centralizer_range_inl hcop hφ hx, map_one] at h
  simpa using h.symm

theorem centralizer_range_inl (hcop : (Nat.card G).Coprime (Nat.card A))
    (hφ : Function.Injective φ) :
    Subgroup.centralizer ((inl : G →* G ⋊[φ] A).range : Set (G ⋊[φ] A)) =
      (Subgroup.center G).map (inl : G →* G ⋊[φ] A) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨x.left, left_mem_center_of_mem_centralizer_range_inl hcop hφ hx,
      SemidirectProduct.ext (by simp)
        (by simp [right_eq_one_of_mem_centralizer_range_inl hcop hφ hx])⟩
  · rintro ⟨g, hg, rfl⟩
    rw [mem_centralizer_range_inl_iff]
    intro h
    rw [Subgroup.mem_center_iff] at hg
    simp [hg h]

theorem mem_centralizer_range_inl_iff_of_coprime (hcop : (Nat.card G).Coprime (Nat.card A))
    (hφ : Function.Injective φ) (x : G ⋊[φ] A) :
    x ∈ Subgroup.centralizer ((inl : G →* G ⋊[φ] A).range : Set (G ⋊[φ] A)) ↔
      x.left ∈ Subgroup.center G ∧ x.right = 1 := by
  constructor
  · intro hx
    exact ⟨left_mem_center_of_mem_centralizer_range_inl hcop hφ hx,
      right_eq_one_of_mem_centralizer_range_inl hcop hφ hx⟩
  · rintro ⟨h1, h2⟩
    rw [mem_centralizer_range_inl_iff]
    intro h
    rw [h2, map_one]
    simpa using (Subgroup.mem_center_iff.mp h1 h).symm

theorem centralizer_range_inl_le_range_inl (hcop : (Nat.card G).Coprime (Nat.card A))
    (hφ : Function.Injective φ) :
    Subgroup.centralizer ((inl : G →* G ⋊[φ] A).range : Set (G ⋊[φ] A)) ≤
      (inl : G →* G ⋊[φ] A).range := by
  rw [centralizer_range_inl hcop hφ]
  exact Subgroup.map_le_range _ _

end

end CFSG.FeitThompson
