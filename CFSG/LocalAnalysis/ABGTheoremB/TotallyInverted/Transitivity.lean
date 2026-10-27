module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.TransitivityCounterexample

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open Sec10

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem transitivity (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (homni : Omnibus Δ) (h92 : NotPGroupP σ r) (hQ : QGroupFourFusion G)
    (hD : DGroupFourFusion G) : Transitivity σ r := by
  intro R₁ hR₁ U hU V hV hR₁U hR₁V
  suffices h : ∀ n : ℕ, ∀ U V : Subgroup G, mu σ U V = n →
      U ∈ maximals (signalizersPerm ⊤ σ.T σ.C r) →
      V ∈ maximals (signalizersPerm ⊤ σ.T σ.C r) → R₁ ≤ U → R₁ ≤ V → Good σ r U V from
    h _ U V rfl hU hV hR₁U hR₁V
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro U V hn hU hV hR₁U hR₁V
    by_contra hbad
    exact false_of_minimal hσ hF Δ homni h92 hQ hD hR₁ hU hV hR₁U hR₁V hbad
      fun U' hU' V' hV' h1 h2 hlt => IH _ (hn ▸ hlt) U' V' rfl hU' hV' h1 h2

end CFSG.ABGTheoremB.TotallyInverted
