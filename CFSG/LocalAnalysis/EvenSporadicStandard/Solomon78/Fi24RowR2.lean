module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBCheck

public section

namespace CFSG.EvenSporadicStandard.Solomon78.Fi24Row

open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.Sporadic.Fi24 (R J JR tR xb jR jR_mem_JR)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem zpowers_involution_cases {G : Type*} [Group G] {t x : G} (htt : t * t = 1)
    (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  have hm : m = 2 * (m / 2) + m % 2 := (Int.mul_ediv_add_emod m 2).symm
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left
    rw [hm, h, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [hm, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

section Small


theorem PB_le_inf : PB ≤ JR ⊓ Subgroup.centralizer ({zR} : Set R) := by
  unfold PB centDer
  refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
    (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)

theorem zR_mem_JR : zR ∈ JR := jR_mem_JR _

theorem zR_mul_zR : zR * zR = 1 :=
  (CFSG.Sporadic.FischerOddCore.fi24U3_facts).1

end Small

section TwoB


theorem fi24_twoB_centralizer {c : R} (hc : c * c = 1)
    (hcent : ∀ y ∈ JR, y * zR = zR * y → c * y = y * c) : c = 1 ∨ c = zR := by
  have hP : c ∈ Subgroup.centralizer (PB : Set R) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : p ∈ JR ⊓ Subgroup.centralizer ({zR} : Set R) := PB_le_inf (SetLike.mem_coe.1 hp)
    have hpJ : p ∈ JR := (Subgroup.mem_inf.1 hp').1
    have hpz : p * zR = zR * p := by
      have h0 := (Subgroup.mem_inf.1 hp').2
      rw [Subgroup.mem_centralizer_singleton_iff] at h0
      exact h0
    exact (hcent p hpJ hpz).symm
  obtain ⟨-, -, -, -, -, hC⟩ := twoB_facts_checked
  exact zpowers_involution_cases zR_mul_zR (hC c hc hP)

theorem fi24_ci_r2 {z : R} (hzz : z * z = 1)
    (hc : ∀ y ∈ JR, y * zR = zR * y → z * y = y * z) : z = 1 ∨ z = zR :=
  fi24_twoB_centralizer hzz hc

theorem fi24_ol_r2 {w : R} (hwJ : w ∉ JR) (hww : w * w = 1) :
    ¬ ∀ y ∈ JR, y * zR = zR * y → y * w = w * y := by
  intro h
  rcases fi24_twoB_centralizer hww (fun y hy hyz => (h y hy hyz).symm) with h1 | h1
  · exact hwJ (h1 ▸ JR.one_mem)
  · exact hwJ (h1 ▸ zR_mem_JR)

end TwoB

end CFSG.EvenSporadicStandard.Solomon78.Fi24Row
