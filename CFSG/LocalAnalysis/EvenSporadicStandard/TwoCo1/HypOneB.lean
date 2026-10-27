module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneSylow
public import Certificates.Certificate24511
public import CFSG.Sporadic.Co1Block.TwoBCentBase2

public section

namespace CFSG.EvenSporadicStandard.TwoCo1.HypOne

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.ComponentClassification.M12Cover

theorem two_part_cent_B :
    32768 = 2 ^ (Nat.card (GA ⊓ Subgroup.centralizer {A₁} : Subgroup GL24)).factorization 2 := by
  rw [card_GA_cent_A₁]
  have h : (2012774400 : ℕ) = 2 ^ 15 * 61425 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  norm_num

theorem fourClassesLarge_B :
    FourClassesLarge ↥(GA ⊓ Subgroup.centralizer {A₁}) :=
  fourClassesLarge_of_sylowCheck (d₁ := twoBD1) (bidx := twoBBray) rep_A₁ A₁_mem rfl
    two_part_cent_B Certificates.certificate24511

end CFSG.EvenSporadicStandard.TwoCo1.HypOne
