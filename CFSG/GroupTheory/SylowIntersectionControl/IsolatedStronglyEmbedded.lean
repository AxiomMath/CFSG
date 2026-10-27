module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
import CFSG.GroupTheory.SylowIntersectionControl.Generation

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools
open scoped Pointwise

variable {X : Type*} [Group X]

private theorem isSylowOf_top_ise {p : ℕ} (P : Sylow p X) : IsSylowOf p (P : Subgroup X) ⊤ := by
  refine ⟨P.subtype le_top, ?_⟩
  rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_top_eq]

theorem ControlsSylowIntersections.nonempty_of_not_isPIsolatedOver {X : Type*} [Group X]
    [Finite X] {p : ℕ} [Fact p.Prime] {𝓕 : Set (Subgroup X)}
    (h : ControlsSylowIntersections p 𝓕 ⊤) (hiso : ¬ IsPIsolatedOver p (⊤ : Subgroup X) ⊥)
    (hO : ∀ P : Subgroup X, P.Normal → IsPGroup p P → P = ⊥) (hp : p ∣ Nat.card X) :
    𝓕.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := X)
  have hP : IsSylowOf p (P : Subgroup X) ⊤ := isSylowOf_top_ise P
  have hnormset : IsNormalSetIn (∅ : Set (Subgroup X)) ⊤ := by
    refine ⟨fun X hX => absurd hX (by simp), fun X hX => absurd hX (by simp)⟩
  have hprod := ControlsSylowIntersections.mul_normalizer_eq hnormset h hiso hP
  have hN : Subgroup.normalizer (P : Set X) = ⊤ := by
    simpa [sylowMembers] using hprod
  have hnormal : (P : Subgroup X).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    simpa using hN
  exact (Sylow.ne_bot_of_dvd_card P hp) (hO (P : Subgroup X) hnormal P.isPGroup')

end CFSG.GroupTheory
