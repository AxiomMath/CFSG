module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFactsF1Defs
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

theorem u43OuterOdd : U43OuterOdd := by
  intro U _ _ hq htwo α hodd
  obtain ⟨-, hmodel⟩ := htwo
  haveI : Group.IsPerfect U := hq.1
  have hSC : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (U ⧸ Subgroup.center U) .PSU 4 3 1 :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
      (t := .PSU) (n := 4) (p := 3) (f := 1) (by decide) hmodel
  obtain ⟨hdvdT, -⟩ :=
    CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (T := U ⧸ Subgroup.center U) (τ := .PSU) (n := 4) (ℓ := 3) (f := 1)
      (Or.inr rfl) (by norm_num : 3 ≤ 4) Nat.prime_three (by norm_num : 1 ≤ 1) hSC
  have hdvd8T : Nat.card (Outer (U ⧸ Subgroup.center U)) ∣ 2 ^ 3 := by
    refine hdvdT.trans ?_
    have hd : CFSG.RankThree.OuterOrder.determinantParameter .PSU 4 (3 ^ 1) = 4 := by
      norm_num [CFSG.RankThree.OuterOrder.determinantParameter]
    rw [hd]
    norm_num
  have hdvdU : Nat.card (Outer U) ∣ Nat.card (Outer (U ⧸ Subgroup.center U)) :=
    Subgroup.card_dvd_of_injective
      (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom U)
      (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective U)
  have hdvd8U : Nat.card (Outer U) ∣ 2 ^ 3 := hdvdU.trans hdvd8T
  let q : Outer U :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner U) α
  have h1 : orderOf q ∣ orderOf α := by
    simpa [q] using orderOf_map_dvd
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner U)) α
  have h2 : orderOf q ∣ Nat.card (Outer U) := orderOf_dvd_natCard q
  have hoddq : Odd (orderOf q) := hodd.of_dvd_nat h1
  have hq1 : q = 1 := by
    have h3 : orderOf q ∣ 2 ^ 3 := h2.trans hdvd8U
    have hcop : Nat.Coprime (orderOf q) (2 ^ 3) :=
      (Nat.coprime_pow_right_iff (by norm_num : 0 < 3) (orderOf q) 2).mpr
        hoddq.coprime_two_right
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h3)
  have hmem : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner U :=
    (QuotientGroup.eq_one_iff
      (N := CFSG.ComponentClassification.OuterAutomorphisms.inner U) α).mp
      (by simpa [q] using hq1)
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
  exact ⟨u, hu.symm⟩

end CFSG.OddStandard.SmallF3.Omega
