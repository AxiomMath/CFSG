module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSporBase
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCo3
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcL
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuter
public import CFSG.Sporadic.Co2Schreier.Components
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.Schreier.Co1OddInner
public import CFSG.Sporadic.SmallOddCore.Co3Aut
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism
public import CFSG.Sporadic.ThSchreier.NodeInnerInvolution

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.RestrictedStd.Spor
  CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert
  CFSG.Sporadic.ThSchreier
open CFSG.Sporadic.Schreier (fixSub)

theorem noLargeAlt_McL :
    NoLargeAltComponents .McL := by
  refine ⟨fun G _ _ _ ⟨e⟩ t ht B hB => ?_, fun G _ _ _ _ ⟨e⟩ α hα2 hα B hB => ?_⟩
  · obtain ⟨θ⟩ := mcl_inner_comps e t ht B hB
    exact not_isLargeAlt_of_card_quotient (c := 20160)
      (fun m hm => lookup_factorial_div_two_ne_of_lt (by norm_num) hm)
      (by rw [Nat.card_congr θ.toEquiv, card_mclX])
  · exact not_isLargeAlt_of_card_quotient (c := 7920)
      (fun m hm => lookup_factorial_div_two_ne_of_lt (by norm_num) hm)
      (Set.mem_singleton_iff.1 (mcl_outer_comps e α hα2 hα B hB))

theorem noLargeAlt_Co1
    (hCo1 : Co1LocalComponentsInput) :
    NoLargeAltComponents .Co1 := by
  refine ⟨fun G _ _ _ ⟨e⟩ t ht B hB => ?_, fun G _ _ _ _ ⟨e⟩ α hα2 hα B hB => ?_⟩
  · exact not_isLargeAlt_of_card_quotient (c := 251596800)
      (fun m _ => lookup_factorial_div_two_ne (k := 12) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) m) (hCo1 G e t ht B hB).1
  · refine (false_of_forall_inner (s := .Co1) (fun β => ?_) e hα).elim
    obtain ⟨g, hg⟩ := Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
      Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner β
    exact ⟨g, hg.symm⟩

theorem noLargeAlt_Co2 :
    NoLargeAltComponents .Co2 := by
  refine ⟨fun G _ _ _ ⟨e⟩ t ht B hB => ?_, fun G _ _ _ _ ⟨e⟩ α hα2 hα B hB => ?_⟩
  · exact fun _ => CTI_Co2_involution_centralizers_have_no_components e t ht B hB
  · exact (false_of_forall_inner (s := .Co2)
      (mem_inner_of_mulEquiv co2PermEquiv CTUC_Co2_full_automorphisms_inner) e hα).elim

theorem noLargeAlt_Co3 :
    NoLargeAltComponents .Co3 := by
  refine ⟨fun G _ _ _ ⟨e⟩ t ht B hB => ?_, fun G _ _ _ _ ⟨e⟩ α hα2 hα B hB => ?_⟩
  · have h := co3_inner_comps e t ht B hB
    simp only [co3Orders, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact not_isLargeAlt_of_card_quotient (c := 1451520)
        (fun m _ => lookup_factorial_div_two_ne (k := 9) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m) h
    · exact not_isLargeAlt_of_card_quotient (c := 95040)
        (fun m hm => lookup_factorial_div_two_ne_of_lt (by norm_num) hm) h
  · refine (false_of_forall_inner (s := .Co3) (fun β => ?_) e hα).elim
    obtain ⟨g, hg⟩ := ctuc_co3_all_automorphisms_inner.{0}.2.1.1 β
    exact ⟨g, hg.symm⟩

theorem noLargeAlt_Th :
    NoLargeAltComponents .Th := by
  refine ⟨fun G _ _ _ hG t ht B hB => ?_, fun G _ _ _ _ ⟨e⟩ α hα2 hα B hB => ?_⟩
  · exact fun _ => compsSatisfy_of_charP
      ((ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 G hG).1 t ht).1
      (fun _ _ => False) B hB
  · refine (false_of_forall_inner (s := .Th) (fun β => ?_) e hα).elim
    have h : inner (NativeSporadic.Carrier .Th) = ⊤ := inner_Th
    rw [h]
    trivial

end CFSG.OddStandard.AltStdSec
