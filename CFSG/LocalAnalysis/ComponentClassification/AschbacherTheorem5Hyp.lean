module

public import CFSG.Open.AschbacherComponentTypeTheorem5MilestoneDefs

public section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5

structure Hyp61 (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) : Prop where
  hr : 1 ≤ r
  hdistinct : Function.Injective Abar
  hsemisimple : ∀ i, aschbacherThm5IsSemisimple (Abar i)
  hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x
  hgen : ⨆ i, Abar i = ⊤
  hperm : ∀ h ∈ Subgroup.normalizer (D : Set G), ∀ i, ∃ j,
    (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
      aschbacherThm5Preimage D (Abar j)
  hi : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ Subgroup.center G →
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
      (g⁻¹ * t * g) →
    g ∈ Subgroup.normalizer (D : Set G)
  hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
    X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
    (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
      a = x * o) →
    g ∈ Subgroup.normalizer (D : Set G)

@[expose] def Conclusion (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) : Prop :=
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

theorem milestone_of
    (h : ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
      (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)),
      Hyp61 G D r Abar → Subgroup.normalizer (D : Set G) ≠ ⊤ → Conclusion G D r Abar)
    (G : Type) [Group G] [Finite G]
    (D : Subgroup G) (r : ℕ) (hr : 1 ≤ r)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hdistinct : Function.Injective Abar)
    (hsemisimple : ∀ i, aschbacherThm5IsSemisimple (Abar i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x)
    (hgen : ⨆ i, Abar i = ⊤)
    (hperm : ∀ h ∈ Subgroup.normalizer (D : Set G), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j))
    (hi : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ Subgroup.center G →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) →
      g ∈ Subgroup.normalizer (D : Set G))
    (hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) →
      g ∈ Subgroup.normalizer (D : Set G))
    (hH : Subgroup.normalizer (D : Set G) ≠ ⊤) :
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
          a₁ = a₂ ∨ a₁ * a₂ ∈ Subgroup.center G) :=
  h G D r Abar ⟨hr, hdistinct, hsemisimple, hcomm, hgen, hperm, hi, hii⟩ hH

structure Counterexample (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) : Prop where
  hyp : Hyp61 G D r Abar
  proper : Subgroup.normalizer (D : Set G) ≠ ⊤
  center : Subgroup.center G = ⊥
  fails : ¬ Conclusion G D r Abar

end CFSG.ComponentClassification.AschbacherTheorem5
