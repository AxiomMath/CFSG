module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRFi23
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi24

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Sporadic.FischerOddCore
open CFSG.Sporadic.Fi24 (R J MR JR tR jR)

theorem fi24CJ_not_isPGroup_of_fi23
    {v : CFSG.Sporadic.Fi23.J} (hv : v ^ 2 = 1) {s : R}
    (hs : s = fi23ToR v ∨ s = fi23ToR v * tR) : ¬ IsPGroup 2 ↥(fi24CJ s) := by
  obtain ⟨x, m, hm, hxm, hx1⟩ :=
    exists_oddPow_of_not_isPGroup (fi23J_centralizer_not_isPGroup hv)
  have hxm' : (x : CFSG.Sporadic.Fi23.J) ^ m = 1 := by simpa using congrArg Subtype.val hxm
  set y : J := (CFSG.Sporadic.Fi24.fi23EquivM.symm (x : CFSG.Sporadic.Fi23.J) : J) with hy
  have hyR : jR y = fi23ToR (x : CFSG.Sporadic.Fi23.J) := rfl
  have hxv : (x : CFSG.Sporadic.Fi23.J) * v = v * x :=
    (mem_centralizer_singleton_iff (G := CFSG.Sporadic.Fi23.J)).mp x.2
  have hc1 : jR y * fi23ToR v = fi23ToR v * jR y := by
    rw [hyR, ← map_mul, ← map_mul, hxv]
  have hc2 : jR y * tR = tR * jR y := by
    rw [hyR]
    exact CFSG.Sporadic.Fi24.commute_tR_of_mem_MR (fi23ToR_mem _)
  have hmem : y ∈ fi24CJ s := by
    rw [mem_fi24CJ]
    rcases hs with rfl | rfl
    · exact hc1
    · calc jR y * (fi23ToR v * tR) = fi23ToR v * (jR y * tR) := by
            rw [← mul_assoc, hc1, mul_assoc]
        _ = fi23ToR v * tR * jR y := by rw [hc2, mul_assoc]
  refine not_isPGroup_of_pow (g := (⟨y, hmem⟩ : ↥(fi24CJ s))) hm ?_ ?_
  · apply Subtype.ext
    change y ^ m = 1
    apply CFSG.Sporadic.Fi24.jR_injective
    rw [map_pow, hyR, ← map_pow, hxm', map_one, map_one]
  · intro h1
    apply hx1
    have h2 : y = 1 := congrArg Subtype.val h1
    have h3 : fi23ToR (x : CFSG.Sporadic.Fi23.J) = fi23ToR 1 := by rw [← hyR, h2, map_one, map_one]
    exact Subtype.ext (fi23ToR_injective h3)

theorem fi24CJ_rep_not_isPGroup
    {s : R} (hs : s ∈ ({fi24D, fi24U2, fi24U3, tR, fi24D * tR, fi24U2 * tR, fi24U3 * tR} : Set R)) :
    ¬ IsPGroup 2 ↥(fi24CJ s) := by
  have hT : tR = fi23ToR 1 * tR := by rw [map_one, one_mul]
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fi24CJ_not_isPGroup_of_fi23 CFSG.Sporadic.Fi23.d_sq' (Or.inl rfl)
  · exact fi24CJ_not_isPGroup_of_fi23 fi23U2_facts.1 (Or.inl rfl)
  · exact fi24CJ_not_isPGroup_of_fi23 fi23U3_facts.1 (Or.inl rfl)
  · exact fi24CJ_not_isPGroup_of_fi23 (one_pow 2) (Or.inr hT)
  · exact fi24CJ_not_isPGroup_of_fi23 CFSG.Sporadic.Fi23.d_sq' (Or.inr rfl)
  · exact fi24CJ_not_isPGroup_of_fi23 fi23U2_facts.1 (Or.inr rfl)
  · exact fi24CJ_not_isPGroup_of_fi23 fi23U3_facts.1 (Or.inr rfl)

theorem sporNoTwoFix_Fi24
    : SporNoTwoFix .Fi24Prime := by
  intro Y _ _ ⟨e⟩ α hα
  have θ : Y ≃* J := e.trans CFSG.Sporadic.Fi24.fi24EquivJ
  obtain ⟨r, hr⟩ := conjJ_surjective ((θ.symm.trans α).trans θ)
  have hrx : ∀ x : Y, θ (α x) = CFSG.Sporadic.Fi24.conjJ r (θ x) := fun x => by
    rw [hr]
    show θ (α x) = θ (α (θ.symm (θ x)))
    rw [MulEquiv.symm_apply_apply]
  have hα2 : α * α = 1 := by rw [← sq, ← hα, pow_orderOf_eq_one]
  have hr2 : r * r = 1 := by
    apply CFSG.Sporadic.Fi24.conjJ_injective
    rw [map_mul, map_one, hr]
    refine MulEquiv.ext fun x => ?_
    show θ (α (θ.symm (θ (α (θ.symm x))))) = x
    rw [MulEquiv.symm_apply_apply, ← MulAut.mul_apply, hα2, MulAut.one_apply,
      MulEquiv.apply_symm_apply]
  have hr1 : r ≠ 1 := by
    rintro rfl
    have h1 : α = 1 := MulEquiv.ext fun x => θ.injective (by
      rw [hrx, map_one, MulAut.one_apply, MulAut.one_apply])
    rw [h1, orderOf_one] at hα
    exact absurd hα (by decide)
  rw [← Hin.fixSub_eq_fixedPoints]
  refine @not_isPGroup_of_mulEquiv _ _ _ (Subgroup.toGroup _) (fixSubEquivCJ θ α r hrx) ?_
  obtain ⟨s, hs, hsr⟩ := fi24_involution_class hr2 hr1
  obtain ⟨c, hc⟩ := (isConj_iff (α := R)).1 hsr
  exact @not_isPGroup_of_mulEquiv _ _ (Subgroup.toGroup _) (Subgroup.toGroup _)
    ((MulEquiv.subgroupCongr (by rw [hc])).trans (fi24CJConj c s).symm)
    (fi24CJ_rep_not_isPGroup hs)

end CFSG.ComponentClassification.HarrisLit.L33.SR
