module

public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem commutator_twistedE6RootGroup_eq_top
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    commutator (twistedE6RootGroup K σ) = ⊤ := by
  have hperf : ⁅twistedE6RootGroup K σ, twistedE6RootGroup K σ⁆ =
      twistedE6RootGroup K σ :=
    (CFSG.LieType.Chevalley.finite_fixed_root_group_perfect TwistTag.E6 hℓ hf K hK
      σ.toRingHom hσ).1
  exact (Subgroup.isPerfect_iff.mpr hperf).commutator_eq_top

end CFSG.LieType.Chevalley

end
