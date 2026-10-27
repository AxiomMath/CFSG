module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup Matrix

variable {G : Type} [Group G] {L S A B Aa : Subgroup G} {z b : G}

theorem conj_mem_sup_zpowers_of_conj_eq_mul {n b' : G} (hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A)
    (hb' : ∃ a ∈ A, n * b' * n⁻¹ = b' * a) {y : G} (hy : y ∈ A ⊔ zpowers b') :
    n * y * n⁻¹ ∈ A ⊔ zpowers b' := by
  have h1 : (A ⊔ zpowers b').map (MulAut.conj n).toMonoidHom ≤ A ⊔ zpowers b' := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.mem_sup_left (hnA a ha)
    · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      obtain ⟨a, ha, h⟩ := hb'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers b'))
        (Subgroup.mem_sup_left ha)
  simpa using h1 ⟨y, hy, rfl⟩

section Finite

variable [Finite G]

@[expose] def normInL (L A : Subgroup G) : Subgroup G where
  carrier := {n | n ∈ L ∧ ∀ x ∈ A, n * x * n⁻¹ ∈ A}
  mul_mem' := fun {a b} ha hb => ⟨L.mul_mem ha.1 hb.1, fun x hx => by
    have e : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact ha.2 _ (hb.2 x hx)⟩
  one_mem' := ⟨L.one_mem, fun x hx => by simpa using hx⟩
  inv_mem' := fun {a} ha => ⟨L.inv_mem ha.1, fun x hx => by
    rw [inv_inv]
    exact conj_inv_mem_of_conj_mem ha.2 hx⟩

theorem mem_normInL {n : G} : n ∈ normInL L A ↔ n ∈ L ∧ ∀ x ∈ A, n * x * n⁻¹ ∈ A := Iff.rfl

variable {c : G → (Fin 4 → ZMod 2)}

end Finite

end CFSG.EvenSporadicStandard.ThStd
