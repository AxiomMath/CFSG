module

public import CFSG.LocalAnalysis.ABGTheoremB.CorollaryV61
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data

public section

namespace CFSG.ABGTheoremB

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

theorem hypIV7_of_exceptional {r : ℕ} (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON)
    (hexc : σ.Exceptional r) (hti : ¬ σ.TotallyInverted r) : σ.HypIV7 r :=
  ⟨hr, hdiv, not_not.mp hti, hexc⟩

theorem notTotallyInvertedOrdinary_of_stages (h₁ : ∀ r : ℕ, σ.HypIV7 r → r = σ.p)
    (h₂ : ¬ σ.HypIV7 σ.p) : σ.NotTotallyInvertedOrdinary := by
  intro r hr hdiv hti
  by_contra hexc
  have h := σ.hypIV7_of_exceptional hr hdiv hexc hti
  exact h₂ (h₁ r h ▸ h)

theorem theoremBStar_of_stages (h₁ : ∀ r : ℕ, σ.HypIV7 r → r = σ.p) (h₂ : ¬ σ.HypIV7 σ.p)
    (h₃ : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → σ.Exceptional r → ¬ σ.TotallyInverted r) :
    σ.TheoremBStar := by
  intro r hr hdiv
  by_contra hexc
  exact hexc (σ.notTotallyInvertedOrdinary_of_stages h₁ h₂ r hr hdiv (h₃ r hr hdiv hexc))

end Setting

end CFSG.ABGTheoremB
