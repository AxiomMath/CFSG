module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Frontier

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def GS81Step10Input : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data) (v : H),
    d.Stage7 v → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f) →
      Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 p f → 3 < p ^ f →
      layerIn (centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H)) = ⊥ →
      ∃ (z₀ : H) (J₀ : Subgroup H), orderOf z₀ = 2 ∧ z₀ ∈ J₀ ∧
        Open.IsSubnormal J₀ (centralizer ({z₀} : Set H)) ∧
        (∃ S : Sylow 2 J₀, ∃ r : ℕ, 3 ≤ r ∧
          Nonempty ((S : Subgroup J₀) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
        Open.classicalInvolutionWitness J₀

end CFSG.ComponentClassification.GSThmB
