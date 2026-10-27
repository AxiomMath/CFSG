module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

private def sec4F_conjPerm (T : Subgroup G) (X : Set G)
    (hX : ∀ g ∈ T, ∀ e ∈ X, g * e * g⁻¹ ∈ X) (g : ↥T) : Equiv.Perm ↥X where
  toFun e := ⟨(g : G) * (e : G) * (g : G)⁻¹, hX (g : G) g.2 (e : G) e.2⟩
  invFun e := ⟨(g : G)⁻¹ * (e : G) * (g : G), by
    simpa using hX (g : G)⁻¹ (T.inv_mem g.2) (e : G) e.2⟩
  left_inv e := by
    apply Subtype.ext
    change (g : G)⁻¹ * ((g : G) * (e : G) * (g : G)⁻¹) * (g : G) = (e : G)
    group
  right_inv e := by
    apply Subtype.ext
    change (g : G) * ((g : G)⁻¹ * (e : G) * (g : G)) * (g : G)⁻¹ = (e : G)
    group

private def sec4F_conjHom (T : Subgroup G) (X : Set G)
    (hX : ∀ g ∈ T, ∀ e ∈ X, g * e * g⁻¹ ∈ X) : ↥T →* Equiv.Perm ↥X where
  toFun := sec4F_conjPerm T X hX
  map_one' := by
    apply Equiv.ext
    intro e
    apply Subtype.ext
    change (1 : G) * (e : G) * (1 : G)⁻¹ = (e : G)
    group
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro e
    apply Subtype.ext
    change ((g : G) * (h : G)) * (e : G) * ((g : G) * (h : G))⁻¹
      = (g : G) * ((h : G) * (e : G) * (h : G)⁻¹) * (g : G)⁻¹
    group

theorem sec4F_sign_hom (T : Subgroup G) (X : Set G) (hXf : X.Finite)
    (hX : ∀ g ∈ T, ∀ e ∈ X, g * e * g⁻¹ ∈ X) :
    ∃ ψ : ↥T →* ℤˣ, ∀ (g : G) (hg : g ∈ T) (a b : G), a ∈ X → b ∈ X → a ≠ b →
      g * a * g⁻¹ = b → g * b * g⁻¹ = a →
        (∀ e ∈ X, e ≠ a → e ≠ b → g * e * g⁻¹ = e) → ψ ⟨g, hg⟩ = -1 := by
  classical
  haveI : Finite ↥X := hXf
  haveI : Fintype ↥X := Fintype.ofFinite ↥X
  refine ⟨Equiv.Perm.sign.comp (sec4F_conjHom T X hX), ?_⟩
  intro g hg a b ha hb hab h1 h2 hfix
  have hπ : sec4F_conjHom T X hX ⟨g, hg⟩ = Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩ := by
    apply Equiv.ext
    intro e
    by_cases hea : e = ⟨a, ha⟩
    · rw [hea, Equiv.swap_apply_left]
      apply Subtype.ext
      exact h1
    · by_cases heb : e = ⟨b, hb⟩
      · rw [heb, Equiv.swap_apply_right]
        apply Subtype.ext
        exact h2
      · rw [Equiv.swap_apply_of_ne_of_ne hea heb]
        apply Subtype.ext
        exact hfix (e : G) e.2 (fun h => hea (Subtype.ext h))
          (fun h => heb (Subtype.ext h))
  have hne : (⟨a, ha⟩ : ↥X) ≠ ⟨b, hb⟩ := fun h => hab (Subtype.ext_iff.mp h)
  rw [MonoidHom.comp_apply, hπ]
  exact Equiv.Perm.sign_swap hne

end CFSG.OddStandard.SmallF3.Omega
