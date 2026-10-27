module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvCore
public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

theorem bmInv_orderOf_map {S S' : Type*} [Group S] [Group S'] (φ : S ≃* S') {s : S} {n : ℕ}
    (hs : orderOf s = n) : orderOf (φ s) = n := by
  rw [MulEquiv.orderOf_eq]
  exact hs

theorem bmInv_false_of_hatSix_of_mulEquiv {S S' : Type*} [Group S] [Group S'] (φ : S ≃* S')
    {s : S} {K : Subgroup S} (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set S)))
    (h : IsHatSix ↥K)
    (H : ∀ K' : Subgroup S', IsComponentOf K' (Subgroup.centralizer ({φ s} : Set S')) →
      IsHatSix ↥K' → False) : False :=
  H _ (bmInv_isComponentOf_map φ hK)
    (bmInv_hat_of_mulEquiv (K.equivMapOfInjective φ.toMonoidHom φ.injective) h)

theorem bmInv_false_of_hat_of_mulEquiv {S S' : Type*} [Group S] [Group S'] (φ : S ≃* S')
    {s : S} {K : Subgroup S} (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set S)))
    (h : IsHatSix ↥K ∨ IsHatON ↥K)
    (H : ∀ K' : Subgroup S', IsComponentOf K' (Subgroup.centralizer ({φ s} : Set S')) →
      IsHatSix ↥K' ∨ IsHatON ↥K' → False) : False := by
  refine H _ (bmInv_isComponentOf_map φ hK) ?_
  have e := K.equivMapOfInjective φ.toMonoidHom φ.injective
  rcases h with h | h
  · exact Or.inl (bmInv_hat_of_mulEquiv e h)
  · exact Or.inr (bmInv_hat_of_mulEquiv e h)

end CFSG.HardMathSupport.Solomon.Coordinator
