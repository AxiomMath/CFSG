module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGTools
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolution
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuCase
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseMcL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseLy
public import CFSG.Sporadic.Schreier.LyOddCoreFree

public section

namespace CFSG.ComponentClassification.FooteLit.KG

open CFSG Subgroup CFSG.ComponentClassification.RestrictedStd
  CFSG.ComponentClassification.RestrictedStd.Spor

theorem pPrimeCore_eq_bot_of_oddCore {G : Type} [Group G] {t : G}
    (h : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥) :
    pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥ := by
  rwa [(CFSG.oddCore_eq_piCore _).trans (CFSG.pPrimeCore_eq_piCore _ 2).symm] at h

theorem noFooteComponent_M22
    (G : Type) [Group G] [Finite G] (hG : Blueprint.NativeSporadic.IsSporadic G .M22) :
    NoFooteComponent G := by
  obtain ⟨e⟩ := id hG
  refine noFooteComponent_of_comps (fun t ht => pPrimeCore_eq_bot_of_oddCore
    (OddStandard.ctuc_mathieu_inner_involution_centralizer_odd_core_trivial_of_isSporadic .M22
      (Or.inr (Or.inr (Or.inl rfl))) hG t ht)) fun t ht => ?_
  exact (compsSatisfy_centralizer_of_mulEquiv _ (isoInvariant_card_dvd 384)
    m22_centralizerIn_comps e t ht).mono fun Y _ h =>
      not_small_of_card_dvd not_isSmallOrder_dvd_384 h

theorem noFooteComponent_M23
    (G : Type) [Group G] [Finite G] (hG : Blueprint.NativeSporadic.IsSporadic G .M23) :
    NoFooteComponent G := by
  obtain ⟨e⟩ := id hG
  refine noFooteComponent_of_comps (fun t ht => pPrimeCore_eq_bot_of_oddCore
    (OddStandard.ctuc_mathieu_inner_involution_centralizer_odd_core_trivial_of_isSporadic .M23
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hG t ht)) fun t ht => ?_
  exact (compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd
    m23_centralizerIn_comps e t ht).mono fun Y _ h => not_small_of_not_three h

theorem noFooteComponent_McL
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Blueprint.NativeSporadic.IsSporadic G .McL) : NoFooteComponent G := by
  obtain ⟨e⟩ := id hG
  refine noFooteComponent_of_comps' (fun hna t ht =>
    pPrimeCore_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_McL hna hG t ht)
    fun t ht => ?_
  exact (mcl_inner_comps e t ht).mono fun Y _ h => not_small_of_mclX h

theorem noFooteComponent_Ly
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Blueprint.NativeSporadic.IsSporadic G .Ly) : NoFooteComponent G := by
  refine noFooteComponent_of_comps' (fun hna t ht =>
    pPrimeCore_eq_bot_of_sporadicOddCoreFree Sporadic.LySchreier.sporadicOddCoreFree_Ly hna hG t
      ht) fun t ht => ?_
  obtain ⟨hq, -, ⟨eA⟩⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple hG t ht
  have hcard : Nat.card (centralizer ({t} : Set G) ⧸ center (centralizer ({t} : Set G))) =
      19958400 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  refine (compsSatisfy_of_isQuasisimple hq (isoInvariant_card_quotient_center {19958400})
    hcard).mono fun Y _ h => not_small_of_card_quotient ?_
  rw [Set.mem_singleton_iff.1 h]
  exact not_isSmallOrder_A11

end CFSG.ComponentClassification.FooteLit.KG
