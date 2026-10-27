module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FSixProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IDict
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IPocketL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82FactSixSix_holds : Asc82FactSixSix := by
  intro G _ _ L hL a b α β hab ha hb w c hw hc hwc
  obtain ⟨e⟩ := sec4I_exists_model hL
  obtain ⟨ya, hya, hta⟩ := (sec4I_inducesTypeSome_iff e (Or.inr (Or.inr rfl))).mp ha
  obtain ⟨yb, hyb, htb⟩ := (sec4I_inducesTypeSome_iff e (Or.inr (Or.inr rfl))).mp hb
  have hcomm : ya * yb = yb * ya := by
    have h1 : Sec4IActs e (a * b) (ya * yb) := hya.mul hyb
    have h2 : Sec4IActs e (b * a) (yb * ya) := hyb.mul hya
    rw [← hab] at h2
    exact h1.unique h2
  obtain ⟨hwL, -, hwt⟩ := (sec4I_isI4PlusIn_iff hL e).mp hw
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _ hc
  obtain ⟨yc, hyc⟩ := exists_sec4IActs e hcN
  have hyc1 : yc = 1 := (Sec4IActs.eq_one_iff hL hyc).mpr hc
  have hwy : Sec4IActs e (w * c) (((e (QuotientGroup.mk (⟨w, hwL⟩ : ↥L)) : Sec4IOmega) :
      ProjOrth Sec4IQ) * yc) := (Sec4IActs.of_mem e hwL).mul hyc
  rw [hyc1, mul_one, ← hwc] at hwy
  have hprod : ya * yb = ((e (QuotientGroup.mk (⟨w, hwL⟩ : ↥L)) : Sec4IOmega) :
      ProjOrth Sec4IQ) := (hya.mul hyb).unique hwy
  exact sec4F_sixsix_proj sec4IQ_nondegenerate sec4IQ_finrank hcomm hta htb (hprod ▸ hwt)

end CFSG.OddStandard.SmallF3.Omega
