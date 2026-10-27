module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSporBase
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseFi23
public import CFSG.Sporadic.Schreier.LyOuter

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.RestrictedStd.Spor
  CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.FischerOddCore CFSG.Sporadic.LySchreier
open CFSG.Sporadic.Schreier (fixSub)

theorem isoInvariant_card_eq (c : ℕ) : IsoInvariant fun Y _ => Nat.card Y = c := by
  intro Y Y' _ _ e h
  rwa [Nat.card_congr e.toEquiv]

theorem noLargeAlt_Fi22
    (hFi22 : Fi22OuterComponentsInput) :
    NoLargeAltComponents .Fi22 := by
  refine ⟨fun G _ _ _ ⟨e⟩ t ht B hB => ?_, fun G _ _ _ _ hG α hα2 hα B hB => ?_⟩
  · exact not_isLargeAlt_of_card_quotient (c := 9196830720)
      (fun m _ => lookup_factorial_div_two_ne (k := 13) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) m)
      (CTI_Fi22_involution_local_components_unitary_quotient_order e t ht B hB)
  · rcases hFi22 G hG α hα2 hα B hB with h | h
    · exact not_isLargeAlt_of_card_quotient (c := 174182400)
        (fun m _ => lookup_factorial_div_two_ne (k := 11) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m) h
    · exact not_isLargeAlt_of_card_quotient (c := 1451520)
        (fun m _ => lookup_factorial_div_two_ne (k := 9) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m) h

theorem noLargeAlt_Fi23 :
    NoLargeAltComponents .Fi23 := by
  refine ⟨fun G _ _ _ ⟨e⟩ t ht B hB => ?_, fun G _ _ _ _ ⟨e⟩ α hα2 hα B hB => ?_⟩
  · have h := fi23_inner_comps e t ht B hB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact not_isLargeAlt_of_card_quotient (c := 64561751654400)
        (fun m _ => lookup_factorial_div_two_ne (k := 16) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m) h
    · exact not_isLargeAlt_of_card_quotient (c := 9196830720)
        (fun m _ => lookup_factorial_div_two_ne (k := 13) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m) h
  · refine (false_of_forall_inner (s := .Fi23) (fun β => ?_) e hα).elim
    show β ∈ inner NativeSporadic.Fi23
    rw [CTUC_Fi23_all_automorphisms_inner.1]
    trivial

theorem noLargeAlt_Fi24
    (hFi24 : Fi24primeOuterComponentsInput) :
    NoLargeAltComponents .Fi24Prime := by
  refine ⟨fun G _ _ _ ⟨e⟩ t ht B hB => ?_, fun G _ _ _ _ hG α hα2 hα B hB => ?_⟩
  · exact not_isLargeAlt_of_card_quotient (c := 64561751654400)
      (fun m _ => lookup_factorial_div_two_ne (k := 16) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) m)
      (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e t ht B
        hB).1
  · rcases hFi24 G hG α hα2 hα B hB with h | h
    · exact not_isLargeAlt_of_card_quotient (c := 4089470473293004800)
        (fun m _ => lookup_factorial_div_two_ne (k := 20) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m) h
    · exact not_isLargeAlt_of_card_quotient (c := 9196830720)
        (fun m _ => lookup_factorial_div_two_ne (k := 13) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m) h

theorem noLargeAlt_Ly
    (hLy : LyOuterTrivialInput) :
    NoLargeAltComponents .Ly := by
  refine ⟨fun G _ _ _ ⟨e⟩ t ht B hB => ?_, fun G _ _ _ _ ⟨e⟩ α hα2 hα B hB => ?_⟩
  · obtain ⟨hq, hz, ⟨eA⟩⟩ := involution_centralizers_quasisimple ⟨e⟩ t ht
    have hcardC : Nat.card (centralizer ({t} : Set G)) = 39916800 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (centralizer ({t} : Set G))),
        hz, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    exact not_isLargeAlt_of_card (c := 39916800)
      (fun m _ => lookup_factorial_div_two_ne (k := 11) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) m)
      (compsSatisfy_of_isQuasisimple hq (isoInvariant_card_eq 39916800) hcardC B hB)
  · refine (false_of_forall_inner (s := .Ly) (fun β => ?_) e hα).elim
    show β ∈ inner NativeSporadic.Ly
    rw [hLy]
    trivial

end CFSG.OddStandard.AltStdSec
