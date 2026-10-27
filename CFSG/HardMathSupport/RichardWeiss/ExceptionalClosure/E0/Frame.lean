module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Shape
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.PiFrame

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm

variable {N : ℕ} {W : Type*} [AddCommGroup W] {M : Type*} [Group M]

structure E0Frame (θ : M →* Perm (Fin N)) (ρ : M →* AddMonoid.End W) (U : AddSubgroup W)
    (π : U →+ altHeart N) (L S : Subgroup M) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (Y : AddSubgroup W) : Prop where
  F : PiFrame θ ρ U π L S
  shape : E0Shape P ω Δ₀
  hN : 10 ≤ N
  even : Even N
  img : ∀ σ : Perm (Fin N), (∃ s ∈ S, θ s = σ) ↔ σ ∈ E0grp P ω Δ₀
  kerS : ∀ m : M, θ m = 1 → m ∈ S
  lK : ∀ l ∈ L, ∀ u : U, π u = 0 → ρ l u = u
  hY1 : ∀ s ∈ S, ∀ u : U, ρ s u - u ∈ Y
  hY2 : ∀ m : M, (∀ s ∈ S, m * s * m⁻¹ ∈ S) → ∀ y ∈ Y, ρ m y ∈ Y

variable {θ : M →* Perm (Fin N)} {ρ : M →* AddMonoid.End W} {U : AddSubgroup W}
  {π : U →+ altHeart N} {L S : Subgroup M} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
  {Δ₀ : Finset (Fin N)} {Y : AddSubgroup W}

namespace E0Frame

theorem rho_eq (E : E0Frame θ ρ U π L S P ω Δ₀ Y) {m n : M} (h : θ m = θ n) : ρ m = ρ n := by
  have h1 : θ (m⁻¹ * n) = 1 := by rw [map_mul, map_inv, h]; simp
  have h2 := E.F.ker _ h1
  have : n = m * (m⁻¹ * n) := by group
  rw [this, map_mul, h2, mul_one]

@[expose] def Det (E : E0Frame θ ρ U π L S P ω Δ₀ Y) (y : W) (x : Fin N) : Prop :=
  ∃ (t : M) (ht : t ∈ S), θ t = swap x (ω x) ∧ π ⟨ρ t y - y, E.F.sTriv t ht y⟩ ≠ 0

end E0Frame

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
