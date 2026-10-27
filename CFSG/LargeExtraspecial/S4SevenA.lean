module

public import CFSG.LargeExtraspecial.S4SevenN0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap

theorem mem_normalizer_of_conj_le {X : Type*} [Group X] [Finite X] {P : Subgroup X} {y : X}
    (h : ∀ p ∈ P, y * p * y⁻¹ ∈ P) : y ∈ normalizer (P : Set X) := by
  let f : P → P := fun p => ⟨y * p * y⁻¹, h p p.2⟩
  have hf : Function.Injective f := fun p q hpq => by
    have h1 : y * (p : X) * y⁻¹ = y * q * y⁻¹ := congrArg Subtype.val hpq
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hs := Finite.injective_iff_surjective.mp hf
  rw [mem_normalizer_iff]
  intro p
  refine ⟨fun hp => h p hp, fun hp => ?_⟩
  obtain ⟨q, hq⟩ := hs ⟨_, hp⟩
  have : y * q * y⁻¹ = y * p * y⁻¹ := congrArg Subtype.val hq
  have hqp : (q : X) = p := by simpa using this
  rw [← hqp]
  exact q.2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Lbar_conj_eq_of_conj_mem (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) {k : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hconj : ∀ y ∈ S.Lbar ((k : G) * g), ∀ l ∈ S.Lbar g, ∃ l' ∈ S.Lbar g,
      l'⁻¹ * (y * l * y⁻¹) ∈ N0bar S g t) :
    S.Lbar ((k : G) * g) = S.Lbar g := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  refine Lbar_conj_eq_of_le_normalizer H C ht fun y hy => mem_normalizer_of_conj_le ?_
  have hyR := Lbar_mul_le_Rbar htk hy
  let P : Subgroup S.O :=
    { carrier := {p | y * p * y⁻¹ ∈ S.Lbar g ⊔ N0bar S g t}
      mul_mem' := by
        intro p q hp hq
        change y * p * y⁻¹ ∈ S.Lbar g ⊔ N0bar S g t at hp
        change y * q * y⁻¹ ∈ S.Lbar g ⊔ N0bar S g t at hq
        change y * (p * q) * y⁻¹ ∈ S.Lbar g ⊔ N0bar S g t
        rw [show y * (p * q) * y⁻¹ = (y * p * y⁻¹) * (y * q * y⁻¹) by group]
        exact mul_mem hp hq
      one_mem' := by
        change y * 1 * y⁻¹ ∈ S.Lbar g ⊔ N0bar S g t
        rw [mul_one, mul_inv_cancel]
        exact one_mem _
      inv_mem' := by
        intro p hp
        change y * p * y⁻¹ ∈ S.Lbar g ⊔ N0bar S g t at hp
        change y * p⁻¹ * y⁻¹ ∈ S.Lbar g ⊔ N0bar S g t
        rw [show y * p⁻¹ * y⁻¹ = (y * p * y⁻¹)⁻¹ by group]
        exact inv_mem hp }
  have hle : S.Lbar g ⊔ N0bar S g t ≤ P := by
    refine sup_le (fun l hl => ?_) (fun n hn => ?_)
    · obtain ⟨l', hl', hn'⟩ := hconj y hy l hl
      change y * l * y⁻¹ ∈ S.Lbar g ⊔ N0bar S g t
      rw [show y * l * y⁻¹ = l' * (l'⁻¹ * (y * l * y⁻¹)) by group]
      exact mul_mem (mem_sup_left hl') (mem_sup_right hn')
    · exact mem_sup_right (conj_mem_N0bar H.conj_mem hyR hn)
  exact fun p hp => (hle hp : y * p * y⁻¹ ∈ S.Lbar g ⊔ N0bar S g t)

end CFSG.LargeExtraspecial.S4
