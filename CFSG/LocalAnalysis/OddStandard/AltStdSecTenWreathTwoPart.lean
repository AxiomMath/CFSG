module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathInner
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathOuter
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathSylow

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup

variable {X : Type} [Group X] [Finite X] {t : X} {A K : Subgroup X}

private lemma factorization_two_20160 : (20160 : ℕ).factorization 2 = 6 := by
  have h : 20160 = 2 ^ 6 * 315 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315), add_zero]

private lemma factorization_two_20160_mul : (20160 * 20160 : ℕ).factorization 2 = 12 := by
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    factorization_two_20160]

private lemma factorization_two_720 : (720 : ℕ).factorization 2 = 4 := by
  have h : 720 = 2 ^ 4 * 45 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 45), add_zero]

private lemma factorization_two_720_mul : (720 * 720 : ℕ).factorization 2 = 8 := by
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    factorization_two_720]

theorem WreathK.factorization_two_layer_inf_centralizer_lt (hK : WreathK t A K) {s : X}
    (hs2 : s * s = 1) (hst : s * t = t * s)
    (hs : s ∉ normalizer (K : Set X) ∨ Nat.card ↥(A ⊓ centralizer ({s} : Set X)) = 720) :
    (Nat.card ↥(CFSG.layer X ⊓ centralizer ({s} : Set X))).factorization 2 <
      (Nat.card ↥(CFSG.layer X)).factorization 2 := by
  rw [WreathK.card_layer hK]
  by_cases hnorm : s ∈ normalizer (K : Set X)
  · have hA : Nat.card ↥(A ⊓ centralizer ({s} : Set X)) = 720 := by
      rcases hs with hnn | hA
      · exact absurd hnorm hnn
      · exact hA
    rw [WreathK.card_layer_inf_centralizer_commuting hK hnorm hst, hA,
      factorization_two_720_mul, factorization_two_20160_mul]
    norm_num
  · rw [WreathK.card_layer_inf_centralizer_outer hK hs2 hnorm,
      factorization_two_20160, factorization_two_20160_mul]
    norm_num

theorem WreathK.not_le_centralizer_of_two_part (hK : WreathK t A K) {s : X} (hs2 : s * s = 1)
    (hst : s * t = t * s)
    (hs : s ∉ normalizer (K : Set X) ∨ Nat.card ↥(A ⊓ centralizer ({s} : Set X)) = 720)
    {T : Subgroup X} (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) :
    ¬ T ≤ centralizer ({s} : Set X) := by
  intro hTs
  haveI : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  have hle : (Nat.card ↥(CFSG.layer X)).factorization 2 ≤
      (Nat.card ↥(CFSG.layer X ⊓ centralizer ({s} : Set X))).factorization 2 :=
    factorization_two_card_le_of_le_centralizer (E := CFSG.layer X) hT hTidx hTs
  exact absurd hle
    (not_le.mpr (WreathK.factorization_two_layer_inf_centralizer_lt hK hs2 hst hs))

end CFSG.OddStandard.AltStdSec.SwapPattern
