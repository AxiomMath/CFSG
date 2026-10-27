module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617
public import CFSG.GH74.GLS.C3.Layer1.Th2P617B

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

@[expose] def B_prop617_obs_ne : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      pRank 2 ↥(T ⊓ CxK x K) ≤ 2 → ¬ (Nat.card ↥(T ⊓ CxK x K) = 4 ∧ T < S) →
        ∀ B : Subgroup G, IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B →
          ∀ (b : G) (J : Subgroup G), Th2.Obs.Obstr52 B b J → J ≠ K → b ≠ x → False

theorem b_prop617_obs_of_ne (h : B_prop617_obs_ne) : B_prop617_obs := by
  intro G _ _ hG x y K T S hs h7 hQ2 hnc B hB b J hobs
  exact h G hG x y K T S hs h7 hQ2 hnc B hB b J hobs (hobs.ne_K hG hs h7 hB)
    (hobs.ne_x hG hs h7 hB)

end CFSG.GH74.GLS
