module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.RowB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.EvenSporadicStandard.Induction.Fi

theorem factorization_two_pow_mul_odd (k : ℕ) {m : ℕ} (hm : Odd m) :
    (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hm
    omega
  have h2 : ¬ 2 ∣ m := by
    intro h
    obtain ⟨j, hj⟩ := hm
    omega
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd h2, add_zero]

theorem factorization_two_card_J :
    (4089470473293004800 : ℕ).factorization 2 = 18 := by
  rw [show (4089470473293004800 : ℕ) = 2 ^ 18 * 15600091832325 by norm_num]
  exact factorization_two_pow_mul_odd 18 ⟨7800045916162, by norm_num⟩

theorem factorization_two_card_Fi23D :
    (129123503308800 : ℕ).factorization 2 = 18 := by
  rw [show (129123503308800 : ℕ) = 2 ^ 18 * 492567075 by norm_num]
  exact factorization_two_pow_mul_odd 18 ⟨246283537, by norm_num⟩

theorem card_sylow_J (Q : Sylow 2 CFSG.Sporadic.Fi23.J) :
    Nat.card (Q : Subgroup CFSG.Sporadic.Fi23.J) = 2 ^ 18 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity, CFSG.Sporadic.Fi23.card_J, factorization_two_card_J]

theorem card_sylow_Fi23D (S : Sylow 2 Fi23D) :
    Nat.card (S : Subgroup Fi23D) = 2 ^ 18 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : Nat.card Fi23D = 129123503308800 :=
    (Nat.card_congr fi23DEquiv.toEquiv).trans CFSG.Sporadic.Fi23.card_centralizer_d
  rw [Sylow.card_eq_multiplicity, hD, factorization_two_card_Fi23D]

theorem fi23D_sylow_iso (T : Sylow 2 CFSG.Sporadic.Fi23.J) :
    ∀ S : Sylow 2 Fi23D,
      Nonempty (↥(S : Subgroup Fi23D) ≃* ↥(T : Subgroup CFSG.Sporadic.Fi23.J)) := by
  intro S
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Fi23D →* CFSG.Sporadic.Fi23.J :=
    (Subgroup.centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J)).subtype.comp
      (MulEquiv.toMonoidHom fi23DEquiv)
  have hf : Function.Injective f :=
    (Subgroup.subtype_injective (Subgroup.centralizer
      ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J))).comp fi23DEquiv.injective
  have hS₁ : Nat.card ((S : Subgroup Fi23D).map f) = 2 ^ 18 := by
    rw [Subgroup.card_map_of_injective hf]
    exact card_sylow_Fi23D S
  have hp : IsPGroup 2 ((S : Subgroup Fi23D).map f) := IsPGroup.of_card (n := 18) hS₁
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup CFSG.Sporadic.Fi23.J) = 2 ^ 18 := card_sylow_J Q
  have hEq : (S : Subgroup Fi23D).map f = (Q : Subgroup CFSG.Sporadic.Fi23.J) :=
    Subgroup.eq_of_le_of_card_ge hQ (hQcard.trans hS₁.symm).le
  exact ⟨(Subgroup.equivMapOfInjective (S : Subgroup Fi23D) f hf).trans
    ((MulEquiv.subgroupCongr hEq).trans (Sylow.equiv Q T))⟩

end CFSG.EvenSporadicStandard.YS14
