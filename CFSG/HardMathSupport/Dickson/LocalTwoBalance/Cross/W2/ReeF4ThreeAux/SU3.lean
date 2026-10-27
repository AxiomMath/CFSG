module

public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Unitary CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {f : ℕ} {K : Type} [Field K] [Finite K]

theorem su3_pair_ne (hf : 2 ≤ f) : (3, 2 ^ f) ≠ (3, 2) := fun h => by
  have h2 : 2 ^ f = 2 := (Prod.mk.inj h).2
  have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem su3_isQuasisimple (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    CFSG.IsQuasisimple (unitarySU 2 f K 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isQuasisimple_statedSU_of_card (p := 2) (f := f) hK le_rfl (su3_pair_ne hf)).1

theorem unitaryFieldData_two (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    UnitaryFieldData 2 f K :=
  ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩

theorem pow_three_eq_one_of_mem_center_su3 (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {z : unitarySU 2 f K 3} (hz : z ∈ Subgroup.center (unitarySU 2 f K 3)) : z ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := unitaryFieldData_two (by omega) hK
  have hZ := (isQuasisimple_statedSU_of_card (p := 2) (f := f) hK le_rfl (su3_pair_ne hf)).2
  rw [hZ, ← unitaryScalars_eq h (by norm_num)] at hz
  have hcard : Nat.card (unitaryScalars h 3) ∣ 3 := by
    rw [card_unitaryScalars h (by norm_num)]
    exact Nat.gcd_dvd_left _ _
  have h1 : orderOf (⟨z, hz⟩ : unitaryScalars h 3) ∣ 3 := (orderOf_dvd_natCard _).trans hcard
  have h2 : (⟨z, hz⟩ : unitaryScalars h 3) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
  exact congrArg (fun w : unitaryScalars h 3 => (w : unitarySU 2 f K 3)) h2

theorem card_su3 (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card (unitarySU 2 f K 3) = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) :=
  card_unitarySU_three (unitaryFieldData_two hf hK)

theorem two_pow_dvd_card_su3 (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    2 ^ (3 * f) ∣ Nat.card (unitarySU 2 f K 3) := by
  rw [card_su3 hf hK, mul_assoc, ← pow_mul, mul_comm f 3]
  exact dvd_mul_right _ _

theorem three_dvd_card_su3 {a : ℕ} (hf : f = 2 * a + 1) (hK : Nat.card K = (2 ^ f) ^ 2) :
    3 ∣ Nat.card (unitarySU 2 f K 3) := by
  rw [card_su3 (by omega) hK]
  refine Dvd.dvd.mul_left ?_ _
  subst hf
  have h4 : (2 ^ (2 * a + 1)) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, h4]

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux
