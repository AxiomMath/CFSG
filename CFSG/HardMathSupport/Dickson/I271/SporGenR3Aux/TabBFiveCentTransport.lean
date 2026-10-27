module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentSeven
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentRes

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Blueprint CFSG.Monster.B.Pinned CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section Transport


theorem tabBFiveACard_of_B433
    {y : CFSG.YGroups.B433} (hy : orderOf y = 5)
    (h7 : 7 ∣ Nat.card (Subgroup.centralizer ({y} : Set CFSG.YGroups.B433)))
    (hlt : Nat.card (Subgroup.centralizer ({y} : Set CFSG.YGroups.B433)) < 665280000) :
    TabBFiveACard := by
  obtain ⟨θ⟩ := CFSG.Monster.Existence.nonempty_B433_mulEquiv_nativeB
  have hθ : orderOf (θ y) = 5 := by rw [MulEquiv.orderOf_eq]; exact hy
  have hC : Nat.card (Subgroup.centralizer ({θ y} : Set NativeSporadic.B)) =
      Nat.card (Subgroup.centralizer ({y} : Set CFSG.YGroups.B433)) := by
    refine (Nat.card_congr (Equiv.subtypeEquiv θ.toEquiv fun x => ?_)).symm
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    rw [← map_mul, ← map_mul, θ.injective.eq_iff]
  obtain ⟨c, hc, g, h | h⟩ := tabBFive_hconj (θ y) hθ
  · exfalso
    apply TabMFive.not_seven_dvd_card_centralizer_zFive
    rw [← hC, ← h, TabMSeven.card_centralizer_conj,
      TabMFive.centralizer_pow_eq_of_five orderOf_zFive hc] at h7
    exact h7
  · have e := TabMSeven.card_centralizer_conj g (sFiveA ^ c)
    rw [h, TabMFive.centralizer_pow_eq_of_five orderOf_sFiveA hc, hC] at e
    show Nat.card ↥(Subgroup.centralizer ({sFiveA} : Set NativeSporadic.B)) < 665280000
    rw [← e]
    exact hlt

end Transport

end CFSG.HardMathSupport.Dickson.I271

end
