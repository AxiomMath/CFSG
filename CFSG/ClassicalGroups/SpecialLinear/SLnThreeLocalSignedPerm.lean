module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.ClassicalGroups.ThreeLocalSignedPerm

variable {G : Type*} [Group G]

@[expose] def Realizes (c : Multiplicative (Fin 3 → ZMod 3) →* G) (g : G)
    (α : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3)) : Prop :=
  ∀ v : Multiplicative (Fin 3 → ZMod 3),
    g * c v * g⁻¹ = c (Multiplicative.ofAdd (α (Multiplicative.toAdd v)))

variable {c : Multiplicative (Fin 3 → ZMod 3) →* G}

theorem Realizes.one : Realizes c 1 fun v => v := by
  intro v
  simp

theorem Realizes.congr {g : G} {α β : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3)}
    (h : ∀ v, α v = β v) (hg : Realizes c g α) : Realizes c g β := by
  intro v
  rw [hg v, h]

theorem Realizes.mul {g g' : G} {α β : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3)}
    (hg : Realizes c g α) (hg' : Realizes c g' β) : Realizes c (g * g') fun v => α (β v) := by
  intro v
  have h1 := hg' v
  have h2 := hg (Multiplicative.ofAdd (β (Multiplicative.toAdd v)))
  calc g * g' * c v * (g * g')⁻¹ = g * (g' * c v * g'⁻¹) * g⁻¹ := by
        simp only [mul_inv_rev, mul_assoc]
    _ = g * c (Multiplicative.ofAdd (β (Multiplicative.toAdd v))) * g⁻¹ := by rw [h1]
    _ = _ := by rw [h2]; rfl

theorem exists_realizes_perm
    (hswap : ∀ x y : Fin 3, x ≠ y → ∃ g : G, Realizes c g fun v i => v (Equiv.swap x y i))
    (σ : Equiv.Perm (Fin 3)) : ∃ g : G, Realizes c g fun v i => v (σ i) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, Realizes.one⟩
  | swap_mul f x y hxy ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨g', hg'⟩ := hswap x y hxy
    exact ⟨g * g', (hg.mul hg').congr fun v => by funext i; simp⟩

theorem exists_realizes_sign
    (hneg : ∀ j : Fin 3, ∃ g : G, Realizes c g fun v i => if i = j then -v i else v i)
    (s : Finset (Fin 3)) :
    ∃ g : G, Realizes c g fun v i => if i ∈ s then -v i else v i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Realizes.one.congr fun v => by funext i; simp⟩
  | insert j s hj ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨g', hg'⟩ := hneg j
    refine ⟨g' * g, (hg'.mul hg).congr fun v => ?_⟩
    funext i
    by_cases hij : i = j
    · subst hij
      simp [hj]
    · simp [hij]

theorem exists_realizes_signedPerm
    (hswap : ∀ x y : Fin 3, x ≠ y → ∃ g : G, Realizes c g fun v i => v (Equiv.swap x y i))
    (hneg : ∀ j : Fin 3, ∃ g : G, Realizes c g fun v i => if i = j then -v i else v i)
    (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) (hε : ∀ i, ε i ≠ 0) :
    ∃ g : G, Realizes c g fun v i => ε i * v (σ i) := by
  classical
  obtain ⟨g₁, hg₁⟩ := exists_realizes_perm hswap σ
  obtain ⟨g₂, hg₂⟩ := exists_realizes_sign hneg (Finset.univ.filter fun i => ε i ≠ 1)
  refine ⟨g₂ * g₁, (hg₂.mul hg₁).congr fun v => ?_⟩
  funext i
  have hi : ε i = 1 ∨ ε i = 2 := by
    have := hε i
    revert this; generalize ε i = e; revert e; decide
  rcases hi with h | h
  · simp [h]
  · have h' : ε i ≠ 1 := by rw [h]; decide
    have h2 : (2 : ZMod 3) = -1 := by decide
    have h3 : (-1 : ZMod 3) ≠ 1 := by decide
    simp [h, h', h2, h3]

theorem exists_conj_signedPerm
    (hswap : ∀ x y : Fin 3, x ≠ y → ∃ g : G, Realizes c g fun v i => v (Equiv.swap x y i))
    (hneg : ∀ j : Fin 3, ∃ g : G, Realizes c g fun v i => if i = j then -v i else v i)
    (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) (hε : ∀ i, ε i ≠ 0) :
    ∃ g : G, ∀ v : Multiplicative (Fin 3 → ZMod 3),
      g * c v * g⁻¹ = c (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) :=
  exists_realizes_signedPerm hswap hneg σ ε hε

end CFSG.ClassicalGroups.ThreeLocalSignedPerm
