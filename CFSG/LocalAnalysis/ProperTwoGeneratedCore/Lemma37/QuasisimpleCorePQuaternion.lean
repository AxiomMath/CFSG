module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

section QuaternionEight

open QuaternionGroup

theorem quaternionEight_mul_self_cases :
    ∀ x : QuaternionGroup 2, x * x = 1 ∨ x * x = a 2 := by
  decide

theorem quaternionEight_eq_of_mul_self :
    ∀ x : QuaternionGroup 2, x * x = 1 → x = 1 ∨ x = a 2 := by
  decide

theorem quaternionEight_anticomm :
    ∀ x y : QuaternionGroup 2, x * x = a 2 → y * y = a 2 → y ≠ x → y ≠ x * a 2 →
      x * y = y * x * a 2 := by
  decide

theorem quaternionEight_enum :
    ∀ x y w : QuaternionGroup 2, x * x = a 2 → y * y = a 2 → y ≠ x → y ≠ x * a 2 →
      (w = 1 ∨ w = a 2 ∨ w = x ∨ w = x * a 2 ∨ w = y ∨ w = y * a 2 ∨ w = x * y ∨
        w = x * y * a 2) := by
  decide

variable {G : Type*} [Group G] {Q : Subgroup G} (φ : Q ≃* QuaternionGroup 2) {e : G}
  (he : e ∈ Q) (he2 : orderOf e = 2)
include φ he he2

theorem quaternion_map_eq : φ ⟨e, he⟩ = a 2 := by
  have hee : (⟨e, he⟩ : Q) * ⟨e, he⟩ = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, ← he2, pow_orderOf_eq_one]; rfl)
  have he1 : (⟨e, he⟩ : Q) ≠ 1 := fun h => by
    rw [show e = 1 from congrArg Subtype.val h, orderOf_one] at he2
    exact absurd he2 (by decide)
  rcases quaternionEight_eq_of_mul_self (φ ⟨e, he⟩) (by rw [← map_mul, hee, map_one]) with h | h
  · exact absurd (φ.injective (h.trans (map_one φ).symm)) he1
  · exact h

omit he he2 in
theorem quaternion_eq_iff {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    x = y ↔ φ ⟨x, hx⟩ = φ ⟨y, hy⟩ :=
  ⟨fun h => by subst h; rfl, fun h => congrArg Subtype.val (φ.injective h)⟩

omit he he2 in
theorem quaternion_map_mul {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    φ ⟨x * y, Q.mul_mem hx hy⟩ = φ ⟨x, hx⟩ * φ ⟨y, hy⟩ := by
  rw [← map_mul]
  rfl

theorem quaternion_mul_self {x : G} (hx : x ∈ Q) : x * x = 1 ∨ x * x = e := by
  rcases quaternionEight_mul_self_cases (φ ⟨x, hx⟩) with h | h
  · left
    have h1 : (⟨x * x, Q.mul_mem hx hx⟩ : Q) = 1 := by
      apply φ.injective
      rw [quaternion_map_mul φ hx hx, h, map_one]
    exact congrArg Subtype.val h1
  · right
    rw [quaternion_eq_iff φ (Q.mul_mem hx hx) he, quaternion_map_mul φ hx hx, h,
      quaternion_map_eq φ he he2]

theorem quaternion_eq_of_mul_self {x : G} (hx : x ∈ Q) (h : x * x = 1) : x = 1 ∨ x = e := by
  have h1 : φ ⟨x, hx⟩ * φ ⟨x, hx⟩ = 1 := by
    rw [← quaternion_map_mul φ hx hx, ← map_one φ]
    exact congrArg φ (Subtype.ext h)
  rcases quaternionEight_eq_of_mul_self _ h1 with h2 | h2
  · left
    exact congrArg Subtype.val (φ.injective (h2.trans (map_one φ).symm))
  · right
    rw [quaternion_eq_iff φ hx he, h2, quaternion_map_eq φ he he2]

theorem quaternion_mul_self_of_ne {x : G} (hx : x ∈ Q) (hx1 : x ≠ 1) (hxe : x ≠ e) :
    x * x = e := by
  rcases quaternion_mul_self φ he he2 hx with h | h
  · rcases quaternion_eq_of_mul_self φ he he2 hx h with h' | h'
    · exact absurd h' hx1
    · exact absurd h' hxe
  · exact h

theorem quaternion_map_mul_self {x : G} (hx : x ∈ Q) (hxx : x * x = e) :
    φ ⟨x, hx⟩ * φ ⟨x, hx⟩ = a 2 := by
  rw [← quaternion_map_mul φ hx hx, ← quaternion_map_eq φ he he2]
  exact congrArg φ (Subtype.ext hxx)

theorem quaternion_map_ne {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) (hyx : y ≠ x) (hyxe : y ≠ x * e) :
    φ ⟨y, hy⟩ ≠ φ ⟨x, hx⟩ ∧ φ ⟨y, hy⟩ ≠ φ ⟨x, hx⟩ * a 2 := by
  refine ⟨fun h => hyx ((quaternion_eq_iff φ hy hx).mpr h), fun h => hyxe ?_⟩
  rw [quaternion_eq_iff φ hy (Q.mul_mem hx he), quaternion_map_mul φ hx he,
    quaternion_map_eq φ he he2]
  exact h

theorem quaternion_anticomm {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) (hxx : x * x = e)
    (hyy : y * y = e) (hyx : y ≠ x) (hyxe : y ≠ x * e) : x * y = y * x * e := by
  have hne := quaternion_map_ne φ he he2 hx hy hyx hyxe
  have h := quaternionEight_anticomm (φ ⟨x, hx⟩) (φ ⟨y, hy⟩)
    (quaternion_map_mul_self φ he he2 hx hxx) (quaternion_map_mul_self φ he he2 hy hyy)
    hne.1 hne.2
  rw [quaternion_eq_iff φ (Q.mul_mem hx hy) (Q.mul_mem (Q.mul_mem hy hx) he),
    quaternion_map_mul φ hx hy, quaternion_map_mul φ (Q.mul_mem hy hx) he,
    quaternion_map_mul φ hy hx, quaternion_map_eq φ he he2]
  exact h

theorem quaternion_enum {x y w : G} (hx : x ∈ Q) (hy : y ∈ Q) (hw : w ∈ Q) (hxx : x * x = e)
    (hyy : y * y = e) (hyx : y ≠ x) (hyxe : y ≠ x * e) :
    w = 1 ∨ w = e ∨ w = x ∨ w = x * e ∨ w = y ∨ w = y * e ∨ w = x * y ∨ w = x * y * e := by
  have hmap := quaternion_map_eq φ he he2
  have hne := quaternion_map_ne φ he he2 hx hy hyx hyxe
  have hxy := Q.mul_mem hx hy
  rcases quaternionEight_enum (φ ⟨x, hx⟩) (φ ⟨y, hy⟩) (φ ⟨w, hw⟩)
    (quaternion_map_mul_self φ he he2 hx hxx) (quaternion_map_mul_self φ he he2 hy hyy)
    hne.1 hne.2 with h | h | h | h | h | h | h | h
  · exact Or.inl ((quaternion_eq_iff φ hw Q.one_mem).mpr (h.trans (map_one φ).symm))
  · exact Or.inr (Or.inl ((quaternion_eq_iff φ hw he).mpr (h.trans hmap.symm)))
  · exact Or.inr (Or.inr (Or.inl ((quaternion_eq_iff φ hw hx).mpr h)))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ((quaternion_eq_iff φ hw (Q.mul_mem hx he)).mpr ?_))))
    rw [quaternion_map_mul φ hx he, hmap]
    exact h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((quaternion_eq_iff φ hw hy).mpr h)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((quaternion_eq_iff φ hw (Q.mul_mem hy he)).mpr ?_))))))
    rw [quaternion_map_mul φ hy he, hmap]
    exact h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((quaternion_eq_iff φ hw hxy).mpr ?_)))))))
    rw [quaternion_map_mul φ hx hy]
    exact h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((quaternion_eq_iff φ hw (Q.mul_mem hxy he)).mpr ?_)))))))
    rw [quaternion_map_mul φ hxy he, quaternion_map_mul φ hx hy, hmap]
    exact h

theorem quaternion_exists_pair :
    ∃ x ∈ Q, ∃ y ∈ Q, x * x = e ∧ y * y = e ∧ y ≠ x ∧ y ≠ x * e := by
  have hmap := quaternion_map_eq φ he he2
  set x : Q := φ.symm (a 1)
  set y : Q := φ.symm (xa 0)
  have hx : φ x = a 1 := φ.apply_symm_apply _
  have hy : φ y = xa 0 := φ.apply_symm_apply _
  refine ⟨x, x.2, y, y.2, ?_, ?_, ?_, ?_⟩
  · rw [quaternion_eq_iff φ (Q.mul_mem x.2 x.2) he, quaternion_map_mul φ x.2 x.2, hmap]
    change φ x * φ x = a 2
    rw [hx]
    decide
  · rw [quaternion_eq_iff φ (Q.mul_mem y.2 y.2) he, quaternion_map_mul φ y.2 y.2, hmap]
    change φ y * φ y = a 2
    rw [hy]
    decide
  · rw [Ne, quaternion_eq_iff φ y.2 x.2]
    change ¬ φ y = φ x
    rw [hx, hy]
    decide
  · rw [Ne, quaternion_eq_iff φ y.2 (Q.mul_mem x.2 he), quaternion_map_mul φ x.2 he, hmap]
    change ¬ φ y = φ x * a 2
    rw [hx, hy]
    decide

end QuaternionEight

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
