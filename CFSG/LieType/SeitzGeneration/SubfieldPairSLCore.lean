module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxLinear

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP CFSG.LinearGroups
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

variable {n : ℕ} {K : Type} [Field K] {k : Subfield K}

theorem map_conj_slSub_le (A : GL (Fin n) K)
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j) (c : K), c ∈ k →
      slConjugation n K A (SpecialLinearGroup.transvection hij c) ∈ slSub n k) :
    (slSub n k).map (slConjugation n K A).toMonoidHom ≤ slSub n k := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨g₀, rfl⟩ := hy
  have hmem : g₀ ∈ Subgroup.closure (elementarySet n k) := by
    rw [special_linear_elementary_generation]
    trivial
  refine Subgroup.closure_induction
    (p := fun g _ => slConjugation n K A (SpecialLinearGroup.map k.subtype g) ∈ slSub n k)
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨i, j, hij, c, rfl⟩
    rw [SpecialLinearGroup.map_transvection]
    exact hroot i j hij c c.2
  · rw [map_one, map_one]
    exact (slSub n k).one_mem
  · intro x y _ _ hx hy
    rw [map_mul, map_mul]
    exact (slSub n k).mul_mem hx hy
  · intro x _ hx
    rw [map_inv, map_inv]
    exact (slSub n k).inv_mem hx

theorem map_conj_slSub_eq [Finite K] (A : GL (Fin n) K)
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j) (c : K), c ∈ k →
      slConjugation n K A (SpecialLinearGroup.transvection hij c) ∈ slSub n k) :
    (slSub n k).map (slConjugation n K A).toMonoidHom = slSub n k :=
  Subgroup.eq_of_le_of_card_ge (map_conj_slSub_le A hroot)
    (Subgroup.card_map_of_injective (slConjugation n K A).injective).ge

end CFSG.LieType.SeitzGeneration
