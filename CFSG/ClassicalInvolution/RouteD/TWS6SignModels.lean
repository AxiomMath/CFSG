module

public import CFSG.ClassicalInvolution.RouteD.TWS6Sign
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpinOdd
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusOrth
public import CFSG.ClassicalInvolution.RouteD.TwinSmallWitt
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS6

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Generic (Commutes fundamentalSubgroups modelUniv)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]


section Odd

variable {m : ℕ}

theorem signFacts_oddDatum (hp2 : p ≠ 2) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    SignFacts (fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)))
      (GaloisField p f) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hK' : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hK]
    omega
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have : Finite (spinGroup (quadOdd m (GaloisField p f))) :=
    ModelFacts.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have hG := orthGeom_sign_small (Q := quadOdd m (GaloisField p f)) (K' := GaloisField p (2 * f))
    hK hK' hodd (fun h8 => absurd h8 (by rw [finrank_odd]; omega))
  exact signFacts_of_centralQuot h4 (not_dvd_card_center_odd hp2 hm3)
    (centralQuot_odd hp2 hm3 hq) hG

theorem signFacts_odd (hp2 : p ≠ 2) (hm : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    SignFacts (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D)
      (GaloisField p f) :=
  signFacts_oddDatum hp2 hm hq

end Odd

section Minus

variable {m : ℕ}

theorem signFacts_minusDatum (hp2 : p ≠ 2) (hm : 4 ≤ m) (hq : 5 ≤ p ^ f) :
    SignFacts (fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)))
      (GaloisField p f) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hK' : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hK]
    omega
  have hf1 : 1 ≤ f := by omega
  have hadm : StatedLieAdmissible .POmegaMinus m p f := ⟨Fact.out, hf1, hm⟩
  have : Finite (spinGroup (quadMinus m (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) :=
    ModelFacts.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus (minusCoeffs_irr p f))
  have hG := orthGeom_sign_small (Q := quadMinus m (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) (K' := GaloisField p (2 * f)) hK hK' hodd (fun h8 P hP => by
    rw [finrank_minus p f m (by omega)] at h8
    obtain rfl : m = 4 := by omega
    exact RouteD.TwinSmall.false_of_pairs_minus (minusCoeffs_irr p f) hodd (by norm_num) P hP)
  exact signFacts_of_centralQuot h4 (not_dvd_card_center_minus hp2 hm)
    (Exotic.centralQuot_minus hp2 hq hadm) hG

theorem signFacts_minus (hp2 : p ≠ 2) (hm : 4 ≤ m) (hq : 5 ≤ p ^ f) :
    SignFacts (fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D)
      (GaloisField p f) :=
  signFacts_minusDatum hp2 hm hq

end Minus

section Plus

variable {m : ℕ}

theorem signFacts_plusDatum (hp2 : p ≠ 2) (hm : 4 ≤ m) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    SignFacts (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3))
      (GaloisField p f) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hK' : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hK]
    omega
  have : NeZero m := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus m (GaloisField p f))) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hsign : ∀ R₁ ∈ fundSet (quadPlus m (GaloisField p f)),
      ∀ R₂ ∈ fundSet (quadPlus m (GaloisField p f)),
      ∀ R₃ ∈ fundSet (quadPlus m (GaloisField p f)),
      ModelAdj (scalars (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f)) R₁ R₂ →
      ModelAdj (scalars (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f)) R₃ R₂ →
      Commutes R₁ R₃ → (∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₂) →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W R₂ R₃ := by
    by_cases h8 : m = 4
    · subst h8
      exact orthGeom_sign_eight (K' := GaloisField p (2 * f)) hK hK' hodd (by rw [finrank_plus])
    · exact orthGeom_sign (K' := GaloisField p (2 * f)) hK hK' hodd
        (by rw [finrank_plus]; omega)
  exact signFacts_of_centralQuot h4 (not_dvd_card_center_plus hp2 hm3)
    (centralQuot_plus hp2 hm hm3 hq) hsign

theorem signFacts_plus (hp2 : p ≠ 2) (hm : 4 ≤ m) (hq : 5 ≤ p ^ f) :
    SignFacts (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D)
      (GaloisField p f) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) (by omega : 3 ≤ m)
  rw [e]
  exact signFacts_plusDatum hp2 hm (by omega) hq

end Plus

end CFSG.ClassicalInvolution.RouteD.TWS6
