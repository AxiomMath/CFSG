module

public import CFSG.GH74.GLS.Stage4.T2P56Core
public import CFSG.GH74.GLS.Stage4.T2TSingEq

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank

theorem ch6T2Prop56Eq_of_layer (hL : SDWreathedLayer)
    (hL3 : LU.Local.L3Cover) : Ch6T2Prop56Eq := by
  intro G _ _ hStd hr Gs _ q hAt h99 hn z K₁ K₂ F₁ F₂ _ _ t hSet hRem p hNum N u hz hK₁ hK₂ hq₁ hq₂
    hSec hq3
  have h5 : 5 ≤ q := hSet.five
  refine ⟨fun y hyH hyz hyp hyodd hya => ?_, fun y hyH hyz hyp hyodd hya => ?_⟩
  · exact exists_J_core hL hL3 hStd hSet hRem hNum h5 hz hK₁ hK₂ hq₁ hq₂ hSec hyH hyz hyp hyodd hya
  · have hqq : N.q₁ = N.q₂ := by rw [hq₁, hq₂]
    exact exists_J_core (N := N.swap) hL hL3 hStd (hSet.swap rfl) hRem.swap hNum h5 hz hK₂ hK₁ hq₂ hq₁
      (hSec.swap hqq) hyH hyz hyp hyodd hya

@[expose] def ThreeCaseJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G)
    (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
    Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t → ∀ p : ℕ, Ch6NumD p q₁ q₂ → q₂ = 3 →
      ∀ (N : T2N3 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
        Ch6Sec5 N u → ∀ y ∈ N.H ⊓ N.K₁, y ∉ Subgroup.zpowers N.z → (orderOf y).Prime →
          Odd (orderOf y) → N.a * y * N.a⁻¹ = y →
            ∃ J : Subgroup G, J ≤ centralizer ({y} : Set G) ∧ K₂ ≤ J ∧
              (IsSLnEps 3 ↥J 1 q₂ ∨ IsLnEps 3 ↥J 1 q₂)

theorem ch6T2Prop56Gt_of_layer (hL : SDWreathedLayer)
    (hL3 : LU.Local.L3Cover) (hThree : ThreeCaseJ) : Ch6T2Prop56Gt := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn hlt z K₁ K₂ F₁ F₂ _ _ t hSet hRem p hNum N u hz hK₁ hK₂
    hq₁ hq₂ hSec y hyH hyz hyp hyodd hya
  by_cases h3 : q₂ = 3
  · exact hThree G hStd Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem p hNum h3 N u hz hK₁ hK₂ hq₁ hq₂ hSec y hyH
      hyz hyp hyodd hya
  · have hq₂3 : 3 ≤ q₂ := by
      have := hSec.loc.q₂_ge
      rw [hq₂] at this
      exact this
    have h5 : 5 ≤ q₂ := by
      rcases hSet.odd₂ with ⟨k, hk⟩
      omega
    exact exists_J_core hL hL3 hStd hSet hRem hNum h5 hz hK₁ hK₂ hq₁ hq₂ hSec hyH hyz hyp hyodd hya

end CFSG.GH74.GLS.Stage4.Rest
