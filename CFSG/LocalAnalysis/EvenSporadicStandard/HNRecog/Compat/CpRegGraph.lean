module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

theorem cp_graphIso_of_injective_regular {V W : Type} [Finite V] [Finite W]
    (Γ₁ : SimpleGraph V) (Γ₂ : SimpleGraph W) (φ : V → W) (hinj : Function.Injective φ)
    (hadj : ∀ u v, Γ₁.Adj u v → Γ₂.Adj (φ u) (φ v)) (hcard : Nat.card V = Nat.card W) (d : ℕ)
    (hd₁ : ∀ v, Nat.card {u // Γ₁.Adj v u} = d) (hd₂ : ∀ w, Nat.card {u // Γ₂.Adj w u} = d) :
    Nonempty (Γ₁ ≃g Γ₂) := by
  classical
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le hcard.ge
  have hreflect : ∀ u v, Γ₂.Adj (φ u) (φ v) → Γ₁.Adj u v := by
    intro u v huv
    let f : {x // Γ₁.Adj u x} → {y // Γ₂.Adj (φ u) y} :=
      fun x => ⟨φ x, hadj u x x.2⟩
    have hfinj : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (hinj (congrArg Subtype.val hxy))
    have hle : Nat.card {y // Γ₂.Adj (φ u) y} ≤ Nat.card {x // Γ₁.Adj u x} := by
      rw [hd₁ u, hd₂ (φ u)]
    have hfbij : Function.Bijective f := hfinj.bijective_of_nat_card_le hle
    obtain ⟨x, hx⟩ := hfbij.2 ⟨φ v, huv⟩
    have hxv : x.1 = v := hinj (congrArg Subtype.val hx)
    rw [← hxv]
    exact x.2
  exact ⟨{ toEquiv := Equiv.ofBijective φ hbij
           map_rel_iff' := fun {a b} =>
             ⟨fun h => hreflect a b h, fun h => hadj a b h⟩ }⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
