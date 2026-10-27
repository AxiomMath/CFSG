module

public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose, instance_reducible] def hypPairsAction (E : Subgroup (V ≃ₗ[K] V))
    (hE : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) :
    MulAction E {x : V × V // Q x.1 = 0 ∧ Q x.2 = 0 ∧ polar Q x.1 x.2 = 1} where
  smul g x := ⟨((g : V ≃ₗ[K] V) x.1.1, (g : V ≃ₗ[K] V) x.1.2), by
    obtain ⟨h1, h2, h3⟩ := x.2
    have hg := hE g.2
    exact ⟨by rw [map_of_mem hg]; exact h1, by rw [map_of_mem hg]; exact h2,
      by rw [polar_map_of_mem hg]; exact h3⟩⟩
  one_smul x := Subtype.ext (Prod.ext rfl rfl)
  mul_smul g h x := Subtype.ext (Prod.ext rfl rfl)

theorem exists_fixed_hypPair {p : ℕ} [Fact p.Prime] {E : Subgroup (V ≃ₗ[K] V)}
    (hE : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hp : ∀ x ∈ E, x ^ p = 1)
    (hcard : ¬ p ∣ Nat.card {x : V × V // Q x.1 = 0 ∧ Q x.2 = 0 ∧ polar Q x.1 x.2 = 1}) :
    ∃ P : HypPair Q, ∀ g ∈ E, g P.e = P.e ∧ g P.f = P.f := by
  let _ := hypPairsAction E hE
  have hpg : IsPGroup p E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hp x x.2)⟩
  obtain ⟨x, hx⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card
    {x : V × V // Q x.1 = 0 ∧ Q x.2 = 0 ∧ polar Q x.1 x.2 = 1} hcard
  refine ⟨⟨x.1.1, x.1.2, x.2.1, x.2.2.1, x.2.2.2⟩, fun g hg => ?_⟩
  have h := MulAction.mem_fixedPoints.mp hx ⟨g, hg⟩
  exact ⟨congrArg (fun y => y.1.1) h, congrArg (fun y => y.1.2) h⟩

end CFSG.ClassicalGroups.Orthogonal
