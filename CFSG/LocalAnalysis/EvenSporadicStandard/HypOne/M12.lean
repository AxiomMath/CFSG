module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fours
public import Certificates.Certificate24270

public section

namespace CFSG.EvenSporadicStandard.HypOne.M12

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.M12 := by
  obtain ⟨-, h, -⟩ := ctss_m12_automorphism_involution_centralizers_exclude_small_normal_four_groups
  refine hypothesisOne_of_centralizer_in fun J hJ u hu => ?_
  obtain ⟨hO, hN⟩ := h J hJ u hu
  exact SmallNormalFree.of_noNormalFour hO hN

theorem hasElemAbelianEight_native :
    HasElemAbelianEight NativeSporadic.M12 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hmem : ∀ w : List ℤ, evalCodes gens w ∈ NativeSporadic.M12 := fun w =>
    evalCodes_mem _ m12_gens_mem' w
  have h1 : e1 ∈ NativeSporadic.M12 := hmem wordE1
  have h2 : e2 ∈ NativeSporadic.M12 := hmem wordE2
  have h3 : e3 ∈ NativeSporadic.M12 := hmem wordE3
  exact hasElemAbelianEight_of_e8Check (a := e1) (b := e2) (c := e3) hn
    Certificates.certificate24270.1 h1 h2 h3

theorem foursGroupCondition_native :
    CFSG.EvenSmallLie.FoursGroupCondition NativeSporadic.M12 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hdata := Certificates.certificate24270.2
  have hcenter : Subgroup.center NativeSporadic.M12 = ⊥ := m12_center
  refine foursGroupCondition_of_reps [beta] ?_ ?_
  · intro φ hφ hout
    set x := autModelEquiv.symm φ with hx
    have hxe : autModelEquiv x = φ := MulEquiv.apply_symm_apply _ _
    have hxx : x * x = 1 :=
      autModelEquiv.injective (by rw [map_mul, hxe, hφ, map_one])
    have hx1 : (x : Equiv.Perm (Fin 24)) ≠ 1 := by
      intro h1
      have : x = 1 := Subtype.ext h1
      apply hout 1
      rw [← hxe, this, map_one, map_one]
    have hx2 : orderOf (x : Equiv.Perm (Fin 24)) = 2 :=
      orderOf_eq_prime (by rw [sq, ← Subgroup.coe_mul, hxx, Subgroup.coe_one]) hx1
    obtain ⟨r, hr, c, hc, hxc⟩ := autModel_involution_cover x.2 hx2
    have hinner : (x : Equiv.Perm (Fin 24)) ∈ blockGroup → False := by
      intro hmem
      obtain ⟨g, hg⟩ := mem_blockGroup_iff_iota.1 hmem
      exact hout g (by rw [← hxe, ← hg, autModelEquiv_iota])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hinner (by
        rw [hxc]
        exact autModel_conj_mem hc _ (m12_gens_memD _ (by simp)))).elim
    · exact (hinner (by
        rw [hxc]
        exact autModel_conj_mem hc _ (blockHom_mem pairs_permZ))).elim
    · refine ⟨beta, by simp, autModelEquiv ⟨c, hc⟩, ?_⟩
      have : x = ⟨c, hc⟩ * sigmaModel * ⟨c, hc⟩⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hxc)
      rw [← hxe, this, map_mul, map_mul, map_inv]
      rfl
  · intro ρ hρ
    rw [List.mem_singleton] at hρ
    subst hρ
    have hv : (((m12b * m12a * m12b⁻¹ * (beta (m12b * m12a * m12b⁻¹))⁻¹ : NativeSporadic.M12)) :
        Equiv.Perm (Fin 12)) = (m12gB * m12gA * m12gB⁻¹) * (m12bp * m12gA * m12bp⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv, beta_m12a]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, beta_m12b]
    have h2 : orderOf ((m12gB * m12gA * m12gB⁻¹) * (m12bp * m12gA * m12bp⁻¹)⁻¹) = 2 :=
      (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hdata
    refine ⟨m12b * m12a * m12b⁻¹, ?_, ?_⟩
    · apply Subtype.ext
      rw [SubgroupClass.coe_pow, hv, OneMemClass.coe_one, ← h2]
      exact pow_orderOf_eq_one _
    · rw [hcenter, Subgroup.mem_bot]
      intro h1
      have := congrArg Subtype.val h1
      rw [hv, OneMemClass.coe_one] at this
      rw [this, orderOf_one] at h2
      omega

theorem rowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .M12) :
    Finkelstein77.RowData Y := by
  obtain ⟨e⟩ := h
  have hI : HypothesisOne (Carrier .M12) := hypothesisOne_native
  exact rowData_of_hasElemAbelianEight (CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hI)
    (HasElemAbelianEight.of_mulEquiv e.symm hasElemAbelianEight_native)

theorem foursGroupCondition_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .M12) :
    CFSG.EvenSmallLie.FoursGroupCondition Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.FoursGroupCondition.of_mulEquiv e.symm foursGroupCondition_native

theorem fullRowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .M12) : FullRowData Y :=
  ⟨rowData_of_isSporadic h, foursGroupCondition_of_isSporadic h⟩

end CFSG.EvenSporadicStandard.HypOne.M12
