module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesV

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification
open CFSG.OddStandard.SmallF3.HypA2
  (NoncentralDatum TypU isSLTwoOver_of_mulEquiv coreInvariant_typU)

@[expose] def a2lDatum (X : Type) [Group X] : Prop :=
  ∃ (q₀ : ℕ) (T N : Subgroup X) (z : X), Odd q₀ ∧ 5 ≤ q₀ ∧ orderOf z = 2 ∧ z ∈ N ∧ N ≤ T ∧
    T ≤ centralizer ({z} : Set X) ∧ CFSG.Assembly.IsComponentOf T (centralizer ({z} : Set X)) ∧
    HarrisLit.IsSLTwoOver q₀ ↥N ∧ TypU ↥T

theorem a2l_map_centralizer_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (z : X) :
    (centralizer ({z} : Set X)).map e.toMonoidHom = centralizer ({e z} : Set Y) := by
  apply le_antisymm
  · simpa using Subgroup.map_centralizer_le_centralizer_image ({z} : Set X) e.toMonoidHom
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    show e.symm y ∈ centralizer ({z} : Set X)
    rw [mem_centralizer_singleton_iff] at hy ⊢
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hy

theorem a2lDatum_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : a2lDatum X) :
    a2lDatum Y := by
  obtain ⟨q₀, T, N, z, hodd, h5, hz, hzN, hNT, hTC, hTc, hN, hTU⟩ := h
  have hC := a2l_map_centralizer_equiv e z
  have eT : ↥T ≃* ↥(T.map e.toMonoidHom) := T.equivMapOfInjective e.toMonoidHom e.injective
  have eN : ↥N ≃* ↥(N.map e.toMonoidHom) := N.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨q₀, T.map e.toMonoidHom, N.map e.toMonoidHom, e z, hodd, h5, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact hz
  · exact Subgroup.mem_map_of_mem _ hzN
  · exact Subgroup.map_mono hNT
  · rw [← hC]; exact Subgroup.map_mono hTC
  · obtain ⟨-, hsub, hq⟩ := hTc
    rw [← hC]
    refine ⟨Subgroup.map_mono hTC, hsub.map e.toMonoidHom, ?_⟩
    exact (AssemblyBPredicates.isQuasisimple_iff_native _).2
      ((LocalAnalysis.ComponentInitial.isQuasisimple_congr eT).1
        ((AssemblyBPredicates.isQuasisimple_iff_native T).1 hq))
  · exact isSLTwoOver_of_mulEquiv eN hN
  · refine coreInvariant_typU _ _ ?_ hTU
    exact ⟨QuotientGroup.congr _ _ eT (CFSG.pPrimeCore_map_iso 2 eT)⟩

end CFSG.OddStandard.SmallF3.HypA2Leaves
