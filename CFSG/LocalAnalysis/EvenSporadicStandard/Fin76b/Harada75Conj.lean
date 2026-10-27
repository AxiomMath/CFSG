module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75R5

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Conj

variable {S : Type} [Group S]

@[expose] def conjSub (t : S) (A : Subgroup S) : Subgroup S where
  carrier := {x | t⁻¹ * x * t ∈ A}
  mul_mem' := by
    intro x y hx hy
    have : t⁻¹ * (x * y) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t) := by group
    show t⁻¹ * (x * y) * t ∈ A
    rw [this]
    exact A.mul_mem hx hy
  one_mem' := by
    show t⁻¹ * 1 * t ∈ A
    rw [mul_one, inv_mul_cancel]
    exact A.one_mem
  inv_mem' := by
    intro x hx
    have : t⁻¹ * x⁻¹ * t = (t⁻¹ * x * t)⁻¹ := by group
    show t⁻¹ * x⁻¹ * t ∈ A
    rw [this]
    exact A.inv_mem hx

theorem mem_conjSub {t : S} {A : Subgroup S} {x : S} : x ∈ conjSub t A ↔ t⁻¹ * x * t ∈ A :=
  Iff.rfl

theorem mem_conjSub_iff {t : S} {A : Subgroup S} {x : S} :
    x ∈ conjSub t A ↔ ∃ a ∈ A, x = t * a * t⁻¹ := by
  constructor
  · intro h
    exact ⟨t⁻¹ * x * t, h, by group⟩
  · rintro ⟨a, ha, rfl⟩
    show t⁻¹ * (t * a * t⁻¹) * t ∈ A
    have : t⁻¹ * (t * a * t⁻¹) * t = a := by group
    rw [this]
    exact ha

theorem conj_mem_conjSub {t : S} {A : Subgroup S} {a : S} (ha : a ∈ A) :
    t * a * t⁻¹ ∈ conjSub t A :=
  mem_conjSub_iff.mpr ⟨a, ha, rfl⟩

theorem card_conjSub (t : S) (A : Subgroup S) : Nat.card (conjSub t A) = Nat.card A := by
  refine Nat.card_congr
    { toFun := fun x => ⟨t⁻¹ * x.1 * t, x.2⟩
      invFun := fun a => ⟨t * a.1 * t⁻¹, conj_mem_conjSub a.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }

theorem isElemAbelian_conjSub (t : S) {A : Subgroup S} (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 (conjSub t A) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have hx : t⁻¹ * x.1 * t ∈ A := x.2
    have hy : t⁻¹ * y.1 * t ∈ A := y.2
    have h := IsElemAbelian.comm_of_mem hA hx hy
    show x.1 * y.1 = y.1 * x.1
    have h2 : t⁻¹ * (x.1 * y.1) * t = t⁻¹ * (y.1 * x.1) * t := by
      calc t⁻¹ * (x.1 * y.1) * t = (t⁻¹ * x.1 * t) * (t⁻¹ * y.1 * t) := by group
        _ = (t⁻¹ * y.1 * t) * (t⁻¹ * x.1 * t) := h
        _ = t⁻¹ * (y.1 * x.1) * t := by group
    simpa using h2
  · have hx' : t⁻¹ * x * t ∈ A := hx
    have h := IsElemAbelian.sq_eq_one hA hx'
    have h2 : t⁻¹ * (x * x) * t = 1 := by
      calc t⁻¹ * (x * x) * t = (t⁻¹ * x * t) * (t⁻¹ * x * t) := by group
        _ = 1 := h
    rw [pow_two]
    have h3 : x * x = 1 := by
      have := congrArg (fun y => t * y * t⁻¹) h2
      simpa [mul_assoc] using this
    exact h3

theorem centralizer_conjSub_le (t : S) {A : Subgroup S}
    (hCA : Subgroup.centralizer (A : Set S) ≤ A) :
    Subgroup.centralizer ((conjSub t A : Subgroup S) : Set S) ≤ conjSub t A := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  show t⁻¹ * x * t ∈ A
  apply hCA
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : (t * a * t⁻¹) * x = x * (t * a * t⁻¹) := hx _ (conj_mem_conjSub ha)
  have h2 : a * (t⁻¹ * x * t) = (t⁻¹ * x * t) * a := by
    calc a * (t⁻¹ * x * t) = t⁻¹ * ((t * a * t⁻¹) * x) * t := by group
      _ = t⁻¹ * (x * (t * a * t⁻¹)) * t := by rw [h1]
      _ = (t⁻¹ * x * t) * a := by group
  exact h2

theorem conjSub_eq_iff {t : S} {A : Subgroup S} :
    conjSub t A = A ↔ t ∈ Subgroup.normalizer (A : Set S) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have : t * x * t⁻¹ ∈ A ↔ t * x * t⁻¹ ∈ conjSub t A := by rw [h]
    rw [this, mem_conjSub]
    have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
    rw [e]
  · intro h
    ext x
    rw [mem_conjSub]
    have := h (t⁻¹ * x * t)
    have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rw [e] at this
    exact this

theorem card_inf_conjSub (t : S) (A : Subgroup S) {E : Subgroup S} (hEn : E.Normal) [Finite S] :
    Nat.card (conjSub t A ⊓ E : Subgroup S) = Nat.card (A ⊓ E : Subgroup S) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨t⁻¹ * x.1 * t, x.2.1, by
        have := hEn.conj_mem x.1 x.2.2 t⁻¹
        simpa using this⟩
      invFun := fun a => ⟨t * a.1 * t⁻¹, conj_mem_conjSub a.2.1, hEn.conj_mem a.1 a.2.2 t⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }

end Conj

end CFSG.EvenSporadicStandard.Fin76b
