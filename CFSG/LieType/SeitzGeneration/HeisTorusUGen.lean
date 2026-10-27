module

public import CFSG.LieType.SeitzGeneration.HeisTorusU85
public import CFSG.LieType.SeitzGeneration.HeisTorusU86
public import CFSG.LieType.SeitzGeneration.HeisTorusU88
public import CFSG.LieType.SeitzGeneration.HeisTorusU87

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem ug_fermat_small {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : r.Prime) (h5 : 5 ≤ r)
    (h17 : r < 17) (hq : ℓ ^ f + 1 = r) : ℓ = 2 ∧ f = 2 := by
  have hℓ2 := hℓ.two_le
  have hle : ℓ ≤ ℓ ^ f := Nat.le_self_pow (by omega) ℓ
  have hℓ16 : ℓ ≤ 15 := by omega
  have hf16 : f < 16 := by
    have : f < ℓ ^ f := Nat.lt_pow_self (by omega)
    omega
  interval_cases r <;> norm_num at hr <;> interval_cases ℓ <;> norm_num at hℓ <;>
    interval_cases f <;> simp_all

theorem torusFourierGenU_of_prime
    (h : UnitaryFieldData ℓ f K) {r : ℕ} [Fact r.Prime] (hr : 5 ≤ r) (hrq : r ∣ ℓ ^ f + 1) :
    TorusFourierGenU h r := by
  intro ζ hζ H hHU hT hTw
  apply eq_unitarySU_of_fixer h hr hrq hζ H hHU hT hTw
  by_cases hne : ℓ ^ f + 1 = r
  · by_cases h17 : 17 ≤ r
    · exact exists_fixer_of_fermat h h17 hne hζ H hT hTw
    · obtain ⟨rfl, rfl⟩ := ug_fermat_small h.prime h.one_le Fact.out hr (by omega) hne
      have hr5 : r = 5 := by omega
      subst hr5
      exact exists_fixer_five_four h hζ H hT hTw
  · exact exists_fixer_of_ne h hr hrq hne hζ H hT hTw

end CFSG.LieType.SeitzGeneration
