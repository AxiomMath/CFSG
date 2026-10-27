module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z15
public import CFSG.RankThree.PartOne.S11c.Sec68
import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

namespace T7Z

theorem oddCenterClassical_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    OddCenterClassical := by
  intro L _ _ hL t n p f hp hp2 hq ht hmodel N hN hNodd
  have hQ : CFSG.IsQuasisimple L := ((CFSG.Foundations.SteinbergCA.quasisimple_iff L).2.2.1).mpr hL
  have hdvd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hQ hmodel
  have hexc : exceptionalOrders t n p f = (1, 1) := by
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · unfold exceptionalOrders
      split
      all_goals first | rfl | (exfalso; first | exact hp2 rfl | omega | simp_all)
  have h4 : Nat.card (Subgroup.center L) ∣ 4 := by
    rw [hexc] at hdvd
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : genericOrders .PSL 4 p f = (Nat.gcd 4 (p ^ f - 1), 1) := rfl
      rw [this] at hdvd
      have h' : Nat.card (Subgroup.center L) ∣ Nat.gcd 4 (p ^ f - 1) := by simpa using hdvd
      exact h'.trans (Nat.gcd_dvd_left _ _)
    · have : genericOrders .PSU 4 p f = (Nat.gcd 4 (p ^ f + 1), 1) := rfl
      rw [this] at hdvd
      have h' : Nat.card (Subgroup.center L) ∣ Nat.gcd 4 (p ^ f + 1) := by simpa using hdvd
      exact h'.trans (Nat.gcd_dvd_left _ _)
    · have : genericOrders .PSp 2 p f = (Nat.gcd 2 (p ^ f - 1), 1) := rfl
      rw [this] at hdvd
      have h' : Nat.card (Subgroup.center L) ∣ Nat.gcd 2 (p ^ f - 1) := by simpa using hdvd
      exact (h'.trans (Nat.gcd_dvd_left _ _)).trans (by norm_num)
  have h1 : Nat.card N ∣ Nat.card (Subgroup.center L) := Subgroup.card_dvd_of_le hN
  have h2 : Nat.card N ∣ 2 ^ 2 := by simpa using h1.trans h4
  have hcop : Nat.Coprime (Nat.card N) 2 := (Nat.coprime_two_left.mpr hNodd).symm
  have h3 : Nat.card N = 1 := (Nat.Coprime.pow_right 2 hcop).eq_one_of_dvd h2
  exact Subgroup.card_eq_one.mp h3

end T7Z

end CFSG.ClassicalInvolution.Asc77
