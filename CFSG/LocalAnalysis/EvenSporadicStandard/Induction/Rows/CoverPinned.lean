module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFactor
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Conj

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic Cover

theorem isSporadic_top {s : TauCeti.SporadicName} {Y : Type} [Group Y] (h : IsSporadic Y s) :
    IsSporadic ↥(⊤ : Subgroup Y) s := by
  obtain ⟨e⟩ := h
  exact ⟨Subgroup.topEquiv.trans e⟩

theorem OddCover.orderOf_q_involution {s : TauCeti.SporadicName} {H : Type} [Group H]
    {L : Subgroup H} (hcov : OddCover s L) {u : H} (hu : u ∈ L) (hu2 : orderOf u = 2) :
    orderOf (q ↥L ⟨u, hu⟩) = 2 := by
  have hsq : (⟨u, hu⟩ : ↥L) * ⟨u, hu⟩ = 1 := Subtype.ext (mul_self_eq_one_of_orderOf hu2)
  refine orderOf_eq_two_of_mul_self (by rw [← map_mul, hsq, map_one]) fun h1 => ?_
  apply hcov.not_mem_centralizer_of_orderOf_two hu hu2
  have hz : (⟨u, hu⟩ : ↥L) ∈ center ↥L := q_eq_one_iff.1 h1
  rw [mem_centralizer_iff]
  intro g hg
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)

theorem pinnedLocal_of_solomonLocal {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {u : Y}
    (hl : SolomonLocal (⊤ : Subgroup Y) K u)
    (hnorm : ∀ c ∈ centralizer ({u} : Set Y), K.map (conjHom c) = K) : PinnedLocal K u := by
  have hA : SolStd (K.subgroupOf (⊤ : Subgroup Y)) :=
    solStd_of_standardComponentIsStandard hl.standard_in_L
  obtain ⟨t, -, hcomp⟩ := hA.2
  have hmap : (K.subgroupOf (⊤ : Subgroup Y)).map (Subgroup.topEquiv (G := Y)).toMonoidHom = K := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_top)
    hcomp.isQuasisimple, ?_, hnorm, (twoAdic_autFixing_le K).trans hl.autCentralizer_two⟩
  have := stdBare_map_mulEquiv (Subgroup.topEquiv (G := Y)) hA.1
  rwa [hmap] at this

end CFSG.EvenSporadicStandard.Induction
