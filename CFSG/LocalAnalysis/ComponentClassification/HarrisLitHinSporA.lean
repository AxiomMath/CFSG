module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSpor
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuCase
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseMcL
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseCo3
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseFi23
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseB
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRu
public import CFSG.Sporadic.Co2Schreier.Components
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism
public import CFSG.Sporadic.ThSchreier.NodeInnerInvolution

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

section

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem hinFor_spor_M11
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .M11 := by
  refine hinFor_of_comps (fun G _ _ ⟨e⟩ t ht => ?_) (outer_of_forall_inner fun α => ?_)
  · exact (compsSatisfy_centralizer_of_mulEquiv _ (isoInvariant_card_dvd 48)
      m11_centralizerIn_comps e t ht).mono fun Y _ h => not_small_of_card_dvd
        not_isSmallOrder_dvd_48 h
  · change α ∈ inner NativeSporadic.M11
    rw [inner_eq_top_of_card_le m11_center_eq_bot' m11_mulAut_card]
    trivial

theorem hinFor_spor_M22
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .M22 := by
  refine hinFor_of_comps (fun G _ _ ⟨e⟩ t ht => ?_) (fun G _ _ _ _ ⟨e⟩ α hα2 hα => ?_)
  · exact (compsSatisfy_centralizer_of_mulEquiv _ (isoInvariant_card_dvd 384)
      m22_centralizerIn_comps e t ht).mono fun Y _ h => not_small_of_card_dvd
        not_isSmallOrder_dvd_384 h
  · refine CompsSatisfy.of_mulEquiv isoInvariant_not_small (fixSubTransportEquiv e α) ?_
    exact (m22_outer_comps _ (transportAut_mul_self e hα2)
      (transportAut_not_mem_inner e hα)).mono fun Y _ h => not_small_of_not_three h

theorem hinFor_spor_M23
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .M23 := by
  refine hinFor_of_comps (fun G _ _ ⟨e⟩ t ht => ?_) (outer_of_forall_inner fun α => ?_)
  · exact (compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd
      m23_centralizerIn_comps e t ht).mono fun Y _ h => not_small_of_not_three h
  · change α ∈ inner NativeSporadic.M23
    rw [inner_eq_top_of_card_le m23_center_eq_bot' m23_mulAut_card]
    trivial

theorem hinFor_spor_M24
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .M24 := by
  refine hinFor_of_comps (fun G _ _ ⟨e⟩ t ht => ?_) (outer_of_forall_inner fun α => ?_)
  · exact (compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd
      m24_centralizerIn_comps e t ht).mono fun Y _ h => not_small_of_not_three h
  · change α ∈ inner NativeSporadic.M24
    rw [inner_eq_top_of_card_le m24_center_eq_bot' m24_mulAut_card]
    trivial

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.RuSchreier
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem hinFor_spor_Ru
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .Ru := by
  refine hinFor_of_comps (fun G _ _ ⟨e⟩ t ht => ?_)
    (outer_of_forall_inner (mem_inner_of_mulEquiv ruEquivP mulAut_inner))
  exact (compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd ru_centralizerIn_comps
    (e.trans ruEquivP) t ht).mono fun Y _ h => not_small_of_not_three h

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.GSThmB CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem hinFor_spor_McL
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .McL := by
  refine hinFor_of_comps (fun G _ _ ⟨e⟩ t ht => ?_)
    (fun G _ _ _ _ ⟨e⟩ α hα2 hα => ?_)
  · exact (mcl_inner_comps e t ht).mono fun Y _ h => not_small_of_mclX h
  · refine (mcl_outer_comps e α hα2 hα).mono fun Y _ h => not_small_of_card_quotient ?_
    rw [Set.mem_singleton_iff.1 h]
    exact not_isSmallOrder_M11

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem hinFor_spor_Co2
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .Co2 := by
  exact hinFor_of_comps
      (fun G _ _ ⟨e⟩ t ht B hB =>
        absurd hB (CTI_Co2_involution_centralizers_have_no_components e t ht B))
      (outer_of_forall_inner
        (mem_inner_of_mulEquiv co2PermEquiv CTUC_Co2_full_automorphisms_inner))

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem hinFor_spor_Co3
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .Co3 := by
  refine hinFor_of_comps (fun G _ _ ⟨e⟩ t ht => ?_) (outer_of_forall_inner fun α => ?_)
  · exact (co3_inner_comps e t ht).mono fun Y _ h => not_small_of_mem_co3Orders h
  · obtain ⟨g, hg⟩ := ctuc_co3_all_automorphisms_inner.{0}.2.1.1 α
    exact ⟨g, hg.symm⟩

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.ThSchreier
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem hinFor_spor_Th
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .Th := by
  refine hinFor_of_comps (fun G _ _ hG t ht => ?_) (outer_of_forall_inner fun α => ?_)
  · exact compsSatisfy_of_charP
      ((ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 G hG).1 t ht).1 _
  · have h : inner (NativeSporadic.Carrier .Th) = ⊤ := inner_Th
    rw [h]
    trivial

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem hinFor_spor_Fi23
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .Fi23 := by
  refine hinFor_of_comps (fun G _ _ ⟨e⟩ t ht => ?_)
    (outer_of_forall_inner fun α => by
      show α ∈ inner NativeSporadic.Fi23
      rw [CTUC_Fi23_all_automorphisms_inner.1]
      trivial)
  refine (fi23_inner_comps e t ht).mono fun Y _ h => not_small_of_card_quotient ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h <;> rw [h]
  · exact not_isSmallOrder_Fi22
  · exact not_isSmallOrder_U62

end

section

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor

theorem hinFor_spor_B
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .B := by
  refine hinFor_of_comps (fun G _ _ ⟨e⟩ t ht K hK => ?_)
    (outer_of_forall_inner fun α => ?_)
  · obtain ⟨-, hiso, -⟩ :=
      Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ t ht K
        hK
    refine not_small_of_card_quotient ?_
    rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · rw [Nat.card_congr φ.toEquiv, LieType.Chevalley.C2E6Std.card_stdGroup]
      exact not_isSmallOrder_twoE62
    · obtain ⟨ψ⟩ := Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
      rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
        Monster.B.E6.FieldInvF4.card_groupJ]
      exact not_isSmallOrder_F42
  · have h : ∀ β : MulAut (NativeSporadic.Carrier .B),
        β ∈ inner (NativeSporadic.Carrier .B) :=
      BMCase.inner_of_mulEquiv_pinnedB NativeSporadic.B ⟨MulEquiv.refl NativeSporadic.B⟩
    exact h α

end

end CFSG.ComponentClassification.HarrisLit.Hin
