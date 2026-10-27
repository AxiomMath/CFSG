module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreSporadicBase
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBenderLarge

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant
  isoInvariant_card_quotient_center)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace QSporadic

open CFSG.ComponentClassification.RestrictedStd.Spor (co1LocalComponentsInput_holds) in
theorem co1_qFree :
    QFree .Co1 := by
  have hinner : ∀ β : MulAut (NativeSporadic.Carrier .Co1),
      β ∈ inner (NativeSporadic.Carrier .Co1) := fun β => by
    obtain ⟨g, hg⟩ := CFSG.Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
      CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner β
    exact ⟨g, hg.symm⟩
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Co1) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G))
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({251596800} : Set ℕ) :=
    fun G _ _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2 (co1LocalComponentsInput_holds G e t ht B hB).1
  refine qFree_of_card_quotient_center (No := ∅) (fun _ _ _ _ hX => ⟨?_, Set.notMem_empty _⟩)
    hin (Sporadic.outer_comps_of_forall_inner hinner _)
  exact SporadicBender.not_mem_singleton_of_ne
    (SporadicBender.ne_of_check_U3 hX (e := 12) (h := 61425) (by norm_num) (by decide)
      (by decide))

open CFSG.Sporadic.FischerOddCore in
theorem fi22_qFree :
    QFree .Fi22 := by
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Fi22) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G))
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({9196830720} : Set ℕ) :=
    fun G _ _ _ ⟨e⟩ t ht B hB => Set.mem_singleton_iff.2
      (CTI_Fi22_involution_local_components_unitary_quotient_order e t ht B hB)
  have hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Fi22) → ∀ β : MulAut G, orderOf β = 2 →
        β ∉ inner G → CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β)
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({174182400, 1451520} : Set ℕ) := by
    intro G _ _ hG hGs β hβ2 hβ B hB
    rcases fi22OuterComponentsInput_holds G hGs β
        (Sporadic.mul_self_eq_one_of_orderOf_eq_two hβ2) hβ B hB with h | h <;> simp [h]
  refine qFree_of_card_quotient_center (fun _ _ _ _ hX => ⟨?_, ?_⟩) hin hout
  · exact SporadicBender.not_mem_singleton_of_ne
      (SporadicBender.ne_of_check_U3 hX (e := 15) (h := 280665) (by norm_num) (by decide)
        (by decide))
  · exact SporadicBender.not_mem_pair_of_ne
      (SporadicBender.ne_of_check_U3 hX (e := 12) (h := 42525) (by norm_num) (by decide)
        (by decide))
      (SporadicBender.ne_of_check_U3 hX (e := 9) (h := 2835) (by norm_num) (by decide)
        (by decide))

open CFSG.ComponentClassification.RestrictedStd.Spor (fi23_inner_comps) in
theorem fi23_qFree :
    QFree .Fi23 := by
  have hinner : ∀ β : MulAut (NativeSporadic.Carrier .Fi23),
      β ∈ inner (NativeSporadic.Carrier .Fi23) := fun β => by
    change β ∈ inner NativeSporadic.Fi23
    rw [CFSG.Sporadic.FischerOddCore.CTUC_Fi23_all_automorphisms_inner.1]
    trivial
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Fi23) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ =>
          Nat.card (Y ⧸ center Y) ∈ ({64561751654400, 9196830720} : Set ℕ) :=
    fun G _ _ _ ⟨e⟩ t ht => fi23_inner_comps e t ht
  refine qFree_of_card_quotient_center (No := ∅) (fun _ _ _ _ hX => ⟨?_, Set.notMem_empty _⟩)
    hin (Sporadic.outer_comps_of_forall_inner hinner _)
  exact SporadicBender.not_mem_pair_of_ne
    (SporadicBender.ne_of_check_U3 hX (e := 17) (h := 492567075) (by norm_num) (by decide)
      (by decide))
    (SporadicBender.ne_of_check_U3 hX (e := 15) (h := 280665) (by norm_num) (by decide)
      (by decide))

open CFSG.Sporadic.FischerOddCore in
theorem fi24prime_qFree :
    QFree .Fi24Prime := by
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Fi24Prime) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G))
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({64561751654400} : Set ℕ) :=
    fun G _ _ _ ⟨e⟩ t ht B hB => Set.mem_singleton_iff.2
      (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven
        e t ht B hB).1
  have hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Fi24Prime) → ∀ β : MulAut G, orderOf β = 2 →
        β ∉ inner G → CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) fun Y _ =>
          Nat.card (Y ⧸ center Y) ∈ ({4089470473293004800, 9196830720} : Set ℕ) := by
    intro G _ _ hG hGs β hβ2 hβ B hB
    rcases fi24primeOuterComponentsInput_holds G hGs β
        (Sporadic.mul_self_eq_one_of_orderOf_eq_two hβ2) hβ B hB with h | h <;> simp [h]
  refine qFree_of_card_quotient_center (fun _ _ _ _ hX => ⟨?_, ?_⟩) hin hout
  · exact SporadicBender.not_mem_singleton_of_ne
      (SporadicBender.ne_of_check_U3 hX (e := 17) (h := 492567075) (by norm_num) (by decide)
        (by decide))
  · exact SporadicBender.not_mem_pair_of_ne
      (SporadicBender.ne_of_check_U3 hX (e := 18) (h := 15600091832325) (by norm_num)
        (by decide) (by decide))
      (SporadicBender.ne_of_check_U3 hX (e := 15) (h := 280665) (by norm_num) (by decide)
        (by decide))

end QSporadic

end CFSG.LocalAnalysis.EvenBN.GMSK
