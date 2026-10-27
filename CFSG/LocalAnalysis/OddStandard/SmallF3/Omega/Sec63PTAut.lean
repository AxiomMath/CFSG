module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PFact
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTQuot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTEmbed
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTInd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FactOm6PA6_of_fbar (h : Asc82FactOm6PA6Bar) : Asc82FactOm6PA6 := by
  intro G _ _ Y x V hY hx2 hxN hxC hVc hVL b hbV hb2
  have hxx : x * x = 1 := by
    have h1 := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at h1
  obtain ⟨e⟩ := sec63PT_exists_equiv_p3 hY.2
  haveI := sec63PT_nontrivial_p3
  have hcen : oddCore ↥Y ≤ center ↥Y := sec63PT_oddCore_le_center hY.1 e
  have hσσ : conjAut Y hxx hxN * conjAut Y hxx hxN = 1 := conjAut_mul_self Y hxx hxN
  obtain ⟨α, hασ, hαα⟩ := sec63PT_exists_induced_aut_quotient e hσσ
  have hσ1 : conjAut Y hxx hxN ≠ 1 := by
    intro h1
    apply hxC
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 : (conjAut Y hxx hxN ⟨y, hy⟩ : ↥Y) = ⟨y, hy⟩ := by rw [h1]; rfl
    have h3 : x * y * x⁻¹ = y := congrArg Subtype.val h2
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hα1 : α ≠ 1 := by
    intro h1
    apply hσ1
    have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥Y))).ker ≤ center ↥Y := by
      intro n hn
      have hn' : e (QuotientGroup.mk n) = 1 := hn
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hn'
      exact hcen hn'
    refine sec63PT_eq_one_of_induced_eq_one hker hY.1.1.commutator_eq_top fun a => ?_
    have h4 := hασ a
    rw [h1, MulAut.one_apply] at h4
    exact h4
  have hα2 : orderOf α = 2 := by
    refine orderOf_eq_prime ?_ hα1
    rw [pow_two]
    exact hαα
  have hF := h α (sec63PT_std_form α) hα2
  exact sec63PT_fact_of_factAt Y hxx hxN (sec63PT_factAt_of_quotient e hcen hσσ hασ hF) hVc hVL
    hbV hb2

end CFSG.OddStandard.SmallF3.Omega
