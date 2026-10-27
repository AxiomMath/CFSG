module

public import CFSG.RankThree.Native.Fi22USections
public import CFSG.Fischer.Classification.Recognition.CaseR3
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFi22Model

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.Schreier CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HypOne.Fi22

theorem fi22_quasisimple_center
    {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G} (hL : IsSporadic L .Fi22)
    (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcard : 18393661440 ≤ Nat.card K) :
    CFSG.Open.IsQuasisimple ↥(K.subgroupOf L) ∧ Nat.card (center ↥(K.subgroupOf L)) = 2 := by
  obtain ⟨Φ, hΦ, hK⟩ := exists_equiv_fi22 hL hu hu2 hKL hKu hcard
  have hmap : (K.subgroupOf L).map Φ.toMonoidHom = fi22OuterM.subgroupOf fi22P := by
    rw [← fi22_centralizer_eq_subgroupOf]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hK x).1 hx
    · intro hy
      exact ⟨Φ.symm y, (hK _).2 (by rwa [MulEquiv.apply_symm_apply]), by simp⟩
  let ε : ↥(K.subgroupOf L) ≃* ↥fi22OuterM :=
    (Φ.subgroupMap (K.subgroupOf L)).trans
      ((MulEquiv.subgroupCongr hmap).trans (subgroupOfEquivOfLe fi22OuterM_le_P))
  have hq : CFSG.Open.IsQuasisimple ↥fi22OuterM :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
      CFSG.RankThree.Native.Fi22U.fi22OuterM_isQuasisimple
  refine ⟨CFSG.Fischer.Classification.Recognition.R3.isQuasisimple_of_mulEquiv ε.symm hq, ?_⟩
  have hc : (center ↥(K.subgroupOf L)).map ε.toMonoidHom = center ↥fi22OuterM :=
    Subgroup.map_center_eq ε
  rw [← CFSG.RankThree.Native.Fi22U.card_center_fi22OuterM, ← hc,
    Subgroup.card_map_of_injective ε.injective]

end CFSG.EvenSporadicStandard.Solomon78
