module

public import CFSG.ClassicalInvolution.Asc77.AscC25W1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Nine

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

section Corrected

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem cA_pair_facts (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (h4 : Nat.card ↥(cA S R R') = 4) (hcl : Subgroup.closure {a, z} = cA S R R')
    (hbad : BadElt z a) : a * a = 1 ∧ a ≠ 1 ∧ a ≠ z := by
  obtain ⟨hzA, hz2, hz1⟩ := z_facts hyp
  have haA : a ∈ cA S R R' := hcl ▸ Subgroup.subset_closure (by simp)
  have hzcard : Nat.card (Subgroup.zpowers z) ≤ 2 := by
    rw [Nat.card_zpowers]
    have h2 : z ^ 2 = 1 := by rw [pow_two]; exact hz2
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
  have hnot : a ∉ Subgroup.zpowers z := by
    intro ha
    have hle : Subgroup.closure {a, z} ≤ Subgroup.zpowers z :=
      (Subgroup.closure_le _).mpr (Set.insert_subset ha (Set.singleton_subset_iff.mpr
        (Subgroup.mem_zpowers z)))
    rw [hcl] at hle
    have := Subgroup.card_le_of_le hle
    omega
  have h1 : a ≠ 1 := fun h => hnot (h ▸ Subgroup.one_mem _)
  have hz : a ≠ z := fun h => hnot (h ▸ Subgroup.mem_zpowers a)
  refine ⟨?_, h1, hz⟩
  by_contra hne
  have hdvd : orderOf a ∣ 4 := by
    have := orderOf_dvd_natCard (⟨a, haA⟩ : ↥(cA S R R'))
    rw [h4] at this
    simpa using this
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (by simpa using hdvd : orderOf a ∣ 2 ^ 2)
  interval_cases i
  · exact h1 (orderOf_eq_one_iff.mp (by simpa using hio))
  · apply hne
    have h2 : a ^ 2 = 1 := by
      have := pow_orderOf_eq_one a
      rw [hio] at this
      simpa using this
    rw [← pow_two]; exact h2
  · have hle : Subgroup.zpowers a ≤ cA S R R' :=
      (Subgroup.zpowers_le).mpr haA
    have hcard : Nat.card (Subgroup.zpowers a) = 4 := by
      simp [Nat.card_zpowers, hio]
    have heq : Subgroup.zpowers a = cA S R R' :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h4])
    exact hbad (C25W.good_of_mem_zpowers (heq ▸ hzA))

end Corrected

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
