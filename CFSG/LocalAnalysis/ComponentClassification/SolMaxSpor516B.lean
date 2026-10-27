module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSpor516J
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.Sporadic.SuzOddCore.CTIComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion

public section

namespace CFSG.ComponentClassification.SolMax.Spor516

open CFSG CFSG.Blueprint CFSG.ComponentClassification.GSThmB
open CFSG.Sporadic.FischerOddCore
  (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven)

theorem leafAt_Suz
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Suz) :
    CF516LeafAt S :=
  leafAt_of_filter e CatalogueU.sporadicOddCoreFree_Suz (N := 448345497600)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Suz) =
        Nat.card NativeSporadic.Suz from rfl, Sporadic.Suz.card_Suz])
    [(2, 13), (3, 7), (5, 2), (7, 1), (11, 1), (13, 1)]
    (by decide) (by decide) (Qs := {3}) (by decide)
    (fun _ q hq t ht B hB => by
      rw [Finset.mem_singleton] at hq
      subst hq
      rw [Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e t ht B
        hB]
      norm_num)

theorem leafAt_Fi22
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Fi22) :
    CF516LeafAt S :=
  leafAt_of_filter e CatalogueU.sporadicOddCoreFree_Fi22 (N := 64561751654400)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Fi22) =
        Nat.card NativeSporadic.Fi22 from rfl, Sporadic.Fi22.card_Fi22])
    [(2, 17), (3, 9), (5, 2), (7, 1), (11, 1), (13, 1)]
    (by decide) (by decide) (Qs := {3}) (by decide)
    (fun _ q hq t ht B hB => by
      rw [Finset.mem_singleton] at hq
      subst hq
      rw [Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order e t
        ht B hB]
      norm_num)

theorem leafAt_Fi23
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Fi23) :
    CF516LeafAt S :=
  leafAt_of_filter e CatalogueU.sporadicOddCoreFree_Fi23 (N := 4089470473293004800)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Fi23) =
        Nat.card NativeSporadic.Fi23 from rfl, Sporadic.Fi23.card_Fi23])
    [(2, 18), (3, 13), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (23, 1)]
    (by decide) (by decide) (Qs := {3}) (by decide)
    (fun _ q hq t ht B hB => by
      rw [Finset.mem_singleton] at hq
      subst hq
      rcases RestrictedStd.Spor.fi23_inner_comps e t ht B hB with h | h
      · rw [h]
        norm_num
      · rw [Set.mem_singleton_iff.1 h]
        norm_num)

theorem leafAt_Fi24Prime
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Fi24Prime) :
    CF516LeafAt S :=
  leafAt_of_filter e CatalogueU.sporadicOddCoreFree_Fi24Prime (N := 1255205709190661721292800)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Fi24Prime) =
        Nat.card NativeSporadic.Fi24prime from rfl, Sporadic.Fi24.card_Fi24prime])
    [(2, 21), (3, 16), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1)]
    (by decide) (by decide) (Qs := {3}) (by decide)
    (fun _ q hq t ht B hB => by
      rw [Finset.mem_singleton] at hq
      subst hq
      rw [(CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e t ht
        B hB).1]
      norm_num)

theorem leafAt_Co1
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Co1) :
    CF516LeafAt S :=
  leafAt_of_filter e CatalogueU.sporadicOddCoreFree_Co1 (N := 4157776806543360000)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Co1) =
        Nat.card NativeSporadic.Co1 from rfl, Sporadic.Co1.card_Co1])
    [(2, 21), (3, 9), (5, 4), (7, 2), (11, 1), (13, 1), (23, 1)]
    (by decide) (by decide) (Qs := {3}) (by decide)
    (fun _ q hq t ht B hB => by
      rw [Finset.mem_singleton] at hq
      subst hq
      rw [(RestrictedStd.Spor.co1LocalComponentsInput_holds S e t ht B hB).1]
      norm_num)

theorem leafAt_Th
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Th) :
    CF516LeafAt S :=
  leafAt_of_filter e Sporadic.ThSchreier.sporadicOddCoreFree_Th (N := 90745943887872000)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Th) =
        Nat.card NativeSporadic.Th from rfl, UnbalancedCorr.card_nativeTh])
    [(2, 15), (3, 10), (5, 3), (7, 2), (13, 1), (19, 1), (31, 1)]
    (by decide) (by decide) (Qs := {3}) (by decide)
    (fun _ q hq t ht B hB => by
      rw [Finset.mem_singleton] at hq
      subst hq
      exact RestrictedStd.Spor.compsSatisfy_of_charP
        ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 S
          ⟨e⟩).1 t ht).1
        (fun Y _ => Nat.card (Y ⧸ Subgroup.center Y) * 2 ≠ 3 ^ 2 * ((3 ^ 2) ^ 2 - 1)) B hB)

end CFSG.ComponentClassification.SolMax.Spor516
