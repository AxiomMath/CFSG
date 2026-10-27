module

public import CFSG.Open.AschbacherComponentTypeTheorem5MilestoneDefs

public section

namespace CFSG.GH74.E2.Box

open CFSG.Open

@[expose] def AschbacherTheorem5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G]
    (D : Subgroup G) (r : ℕ) (_hr : 1 ≤ r)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (_hdistinct : Function.Injective Abar)
    (_hsemisimple : ∀ i, aschbacherThm5IsSemisimple (Abar i))
    (_hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x)
    (_hgen : ⨆ i, Abar i = ⊤)
    (_hperm : ∀ h ∈ Subgroup.normalizer (D : Set G), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j))
    (_hi : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ Subgroup.center G →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) →
      g ∈ Subgroup.normalizer (D : Set G))
    (_hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) →
      g ∈ Subgroup.normalizer (D : Set G))
    (_hH : Subgroup.normalizer (D : Set G) ≠ ⊤),
    r = 1 ∨
      (r = 2 ∧ ∀ i j : Fin r, i ≠ j →
        (∀ d ∈ D, ∃ a ∈ aschbacherThm5Preimage D (Abar i),
          ∃ b ∈ aschbacherThm5Preimage D (Abar j), d = a * b) ∧
        pRank 2 (aschbacherThm5Preimage D (Abar i)) = 1 ∧
        ∀ a₁ ∈ aschbacherThm5Preimage D (Abar i), ∀ a₂ ∈ aschbacherThm5Preimage D (Abar j),
          orderOf a₁ = 2 → orderOf a₂ = 2 → a₁ * a₂ = a₂ * a₁ →
          aschbacherThm5Centralizes (aschbacherThm5Core D)
            (aschbacherThm5Preimage D (Abar i)) a₁ →
          aschbacherThm5Centralizes (aschbacherThm5Core D)
            (aschbacherThm5Preimage D (Abar j)) a₂ →
          a₁ = a₂ ∨ a₁ * a₂ ∈ Subgroup.center G)

end CFSG.GH74.E2.Box
