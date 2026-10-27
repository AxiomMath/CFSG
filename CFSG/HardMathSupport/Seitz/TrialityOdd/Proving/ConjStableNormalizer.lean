module

public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

theorem map_conj_eq_of_generators_stable {Y : Type*} [Group Y]
    (L : Subgroup Y) [Finite L] (P : Set Y) (hgen : Subgroup.closure P = L)
    (g : Y) (hP : ∀ x ∈ P, g * x * g⁻¹ ∈ P) :
    L.map (MulAut.conj g).toMonoidHom = L := by
  have hle : L.map (MulAut.conj g).toMonoidHom ≤ L := by
    rw [← hgen, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.subset_closure (hP x hx)
  have hcard : Nat.card L ≤ Nat.card (L.map (MulAut.conj g).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem exists_generator_conj_not_mem {Y : Type*} [Group Y]
    (L : Subgroup Y) [Finite L] (P : Set Y) (hgen : Subgroup.closure P = L)
    (g : Y) (hg : L.map (MulAut.conj g).toMonoidHom ≠ L) :
    ∃ x ∈ P, g * x * g⁻¹ ∉ P := by
  by_contra hcon
  apply hg
  apply map_conj_eq_of_generators_stable L P hgen g
  intro x hx
  by_contra hx'
  exact hcon ⟨x, hx, hx'⟩

theorem exists_generator_conj_not_mem_of_not_normalizes {Y : Type*} [Group Y]
    (L : Subgroup Y) [Finite L] (P : Set Y) (hgen : Subgroup.closure P = L)
    (g : Y) (hg : g ∉ Subgroup.normalizer (L : Set Y)) :
    ∃ x ∈ P, g * x * g⁻¹ ∉ P :=
  exists_generator_conj_not_mem L P hgen g
    (fun h => hg (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h))

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
