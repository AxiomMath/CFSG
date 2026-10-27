module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fours
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers
public import Certificates.Certificate24273

public section

namespace CFSG.EvenSporadicStandard.HypOne.J2

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.M12Cover

theorem hypothesisOne_P :
    HypothesisOne P := by
  obtain ⟨-, h, -⟩ := ctss_j2_automorphism_involution_centralizers_exclude_small_normal_four_groups
  refine hypothesisOne_of_centralizer_in fun J hJ u hu => ?_
  obtain ⟨hO, hN⟩ := h J hJ u hu
  exact SmallNormalFree.of_noNormalFour hO hN

theorem hasElemAbelianEight_P :
    HasElemAbelianEight P := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  have h := Certificates.certificate24273.1
  simp only [e8Data, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hi1, hi2⟩, hi3⟩, hm1⟩, hm2⟩, hm3⟩, h8⟩ := h
  have r1 := (CFSG.Monster.B.Co2.rep_permOfArr hi1).1
  have r2 := (CFSG.Monster.B.Co2.rep_permOfArr hi2).1
  have r3 := (CFSG.Monster.B.Co2.rep_permOfArr hi3).1
  refine hasElemAbelianEight_of_e8Check hn (a := CFSG.Monster.B.Co2.permOfArr 315 arrE1)
    (b := CFSG.Monster.B.Co2.permOfArr 315 arrE2)
    (c := CFSG.Monster.B.Co2.permOfArr 315 arrE3) ?_ ((mem_P_iff r1).1 hm1)
    ((mem_P_iff r2).1 hm2) ((mem_P_iff r3).1 hm3)
  rw [toTable_eq_arrTable r1, toTable_eq_arrTable r2, toTable_eq_arrTable r3]
  exact h8

theorem foursGroupCondition_P :
    CFSG.EvenSmallLie.FoursGroupCondition P := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hcover, -⟩ :=
    ctss_j2_automorphism_involution_centralizers_exclude_small_normal_four_groups
  have hdata := Certificates.certificate24273.2
  simp only [foursData, Bool.and_eq_true] at hdata
  obtain ⟨⟨hinv, hLP⟩, hord⟩ := hdata
  have hcenter : Subgroup.center P = ⊥ := center_P
  refine foursGroupCondition_of_reps [rConj ⟨permU, permU_mem_R⟩] ?_ ?_
  · intro φ hφ hout
    obtain ⟨x, rfl⟩ := rAutEquiv.surjective φ
    have hxx : x * x = 1 := rAutEquiv.injective (by rw [map_mul, hφ, map_one])
    have hxP : (x : Equiv.Perm (Fin 315)) ∉ P := fun hxP => hout ⟨x, hxP⟩ (by
      rw [← rConj_of_mem_P hxP]
      rfl)
    have hx2 : orderOf (x : Equiv.Perm (Fin 315)) = 2 :=
      orderOf_eq_prime (by rw [sq, ← Subgroup.coe_mul, hxx, Subgroup.coe_one])
        (fun h1 => hxP (h1 ▸ P.one_mem))
    obtain ⟨r, hr, c, hc, hxc⟩ := hcover x x.2 hx2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hxP (by
        rw [hxc]
        exact P.mul_mem (P.mul_mem hc permA_mem) (P.inv_mem hc))).elim
    · exact (hxP (by
        rw [hxc]
        exact P.mul_mem (P.mul_mem hc permTwoA_mem) (P.inv_mem hc))).elim
    · refine ⟨rConj ⟨permU, permU_mem_R⟩, by simp, rAutEquiv ⟨c, P_le_R hc⟩, ?_⟩
      have : x = ⟨c, P_le_R hc⟩ * ⟨permU, permU_mem_R⟩ * ⟨c, P_le_R hc⟩⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hxc)
      rw [this, map_mul, map_mul, map_inv]
      rfl
  · intro ρ hρ
    rw [List.mem_singleton] at hρ
    subst hρ
    obtain ⟨hr, -⟩ := CFSG.Monster.B.Co2.rep_permOfArr hinv
    have hmem : CFSG.Monster.B.Co2.permOfArr 315 arrL ∈ P := (mem_P_iff hr).1 hLP
    set l : P := ⟨CFSG.Monster.B.Co2.permOfArr 315 arrL, hmem⟩ with hl
    have hr' := (CFSG.Monster.B.Co2.rep_permOfArr hinv)
    have rl := rep_arrTable hn hr'.1
    have rli := rep_arrTable hn hr'.2
    have ru : CFSG.Sporadic.Th.Rep 315 tblU permU := rep_arrTable hn rep_permU
    have rui : CFSG.Sporadic.Th.Rep 315 tblU permU⁻¹ := by rw [permU_inv]; exact ru
    have h2 : orderOf (CFSG.Monster.B.Co2.permOfArr 315 arrL * permU *
        (CFSG.Monster.B.Co2.permOfArr 315 arrL)⁻¹ * permU⁻¹) = 2 :=
      (CFSG.Sporadic.Schreier.ordTest_iff CFSG.Sporadic.Schreier.perm_faithful
        (CFSG.Sporadic.Th.Rep.compT (CFSG.Sporadic.Th.Rep.compT (CFSG.Sporadic.Th.Rep.compT rl ru)
          rli) rui) (by norm_num)).1 hord
    have hv : (((l * (rConj ⟨permU, permU_mem_R⟩ l)⁻¹ : P)) : Equiv.Perm (Fin 315)) =
        CFSG.Monster.B.Co2.permOfArr 315 arrL * permU *
          (CFSG.Monster.B.Co2.permOfArr 315 arrL)⁻¹ * permU⁻¹ := by
      have hl' : (l : Equiv.Perm (Fin 315)) = CFSG.Monster.B.Co2.permOfArr 315 arrL := rfl
      show (l : Equiv.Perm (Fin 315)) * (permU * (l : Equiv.Perm (Fin 315)) * permU⁻¹)⁻¹ = _
      rw [hl']
      group
    refine ⟨l, ?_, ?_⟩
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
    {Y : Type} [Group Y] [Finite Y]
    (h : IsSporadic Y .J2) : Finkelstein77.RowData Y := by
  obtain ⟨e⟩ := h
  have e' : Y ≃* P := e.trans nativeEquivP
  have hI : HypothesisOne Y :=
    CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e'.symm hypothesisOne_P
  exact rowData_of_hasElemAbelianEight hI
    (HasElemAbelianEight.of_mulEquiv e'.symm hasElemAbelianEight_P)

theorem foursGroupCondition_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .J2) : CFSG.EvenSmallLie.FoursGroupCondition Y := by
  obtain ⟨e⟩ := h
  have e' : Y ≃* P := e.trans nativeEquivP
  exact CFSG.EvenSmallLie.FoursGroupCondition.of_mulEquiv e'.symm foursGroupCondition_P

theorem fullRowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .J2) : FullRowData Y :=
  ⟨rowData_of_isSporadic h, foursGroupCondition_of_isSporadic h⟩

end CFSG.EvenSporadicStandard.HypOne.J2
