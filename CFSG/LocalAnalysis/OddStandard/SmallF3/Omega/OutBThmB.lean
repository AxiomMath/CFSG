module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBLemB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBXsub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Thm2LConj_of_lemma36 (h36 : Asc82Lemma36) : Asc82Thm2LConj := by
  intro G _ _ t L hS hcyc hOdd ε g _ _ X hX
  have hS' : Sec3SettingLB G (g⁻¹ * t * g) (CFSG.conjugate L g) := hS.conjugate g
  have hnorm := conjugate_eq_self_of_lemma36 h36 hS'
  refine aor_twoPrimeRes_le_of_cyclic (centralizer ({g⁻¹ * t * g} : Set G)) (CFSG.conjugate L g)
    hS'.component.le ?_ ?_ X (asc82XSub_le_twoRes L (g⁻¹ * t * g) ε X hX)
  · exact fun P hP hPle => aor_cyclic_conjugate hcyc g P hP (hPle.trans inf_le_right)
  · exact fun y hy hodd => aor_oddInner_conjugate hOdd g y
      (mem_normalizer_of_conjugate_eq (hnorm y hy)) hodd

end CFSG.OddStandard.SmallF3.Omega
