module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Fam
public import CFSG.ClassicalInvolution.Q3.TL3T22

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight

namespace TwinDisc

namespace ExitO2

variable {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)} {W : Subgroup Y}

theorem Q8Fam.partIHypG (F : Q8Fam Y Δ) : Q3CL.PartIHypG Δ :=
  ⟨F.hyp, TC.Thin.classicalClause_of_two F.hyp F.two, F.aEmpty⟩

theorem fam_conjSub_eq_of_wSet (F : Q8Fam Y Δ)
    (hW1 : WSet (Δ) = {W}) (g : Y) : conjSub g W = W := by
  have hW : W ∈ WSet (Δ) := by rw [hW1]; rfl
  have := WSet.conj F.hyp.conjInvariant hW g
  rwa [hW1] at this

theorem fam_not_le_of_wSet (F : Q8Fam Y Δ) (hW1 : WSet Δ = {W}) :
    ∀ L ∈ Δ, ¬ L ≤ W := by
  intro L hL hle
  have hW : W ∈ WSet Δ := by rw [hW1]; rfl
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet F.hyp hW
  obtain ⟨e⟩ := F.q8 L hL
  apply (show (QuaternionGroup.a 1 : QuaternionGroup 2) * .xa 0 ≠ .xa 0 * .a 1 by decide)
  have h' : e.symm (.a 1) * e.symm (.xa 0) = e.symm (.xa 0) * e.symm (.a 1) :=
    Subtype.ext (hWab _ (hle (e.symm (.a 1)).2) _ (hle (e.symm (.xa 0)).2))
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h'

theorem fam_mem_DSet_of_wSet (F : Q8Fam Y Δ)
    (hW1 : WSet (Δ) = {W}) :
    ∀ L ∈ Δ,
      L ∈ DSet (Δ) W ∧ IsSylow2In L L := by
  intro L hL
  have hLsyl : IsSylow2In L L :=
    ⟨le_rfl, F.two L hL, fun V hVL _ hLV => le_antisymm hVL hLV⟩
  exact ⟨⟨mem_RSet_of_isSylow2In hL hLsyl,
    fun x _ => mem_normalizer_iff_conjSub_eq.mpr (fam_conjSub_eq_of_wSet F hW1 x)⟩, hLsyl⟩

theorem fam_exists_rep_of_wSet (F : Q8Fam Y Δ)
    (hW1 : WSet (Δ) = {W}) :
    ∀ L ∈ Δ,
      ∃ ρ : Rep (Δ) W, ρ.K = L := by
  intro L hL
  obtain ⟨r, hrL, hrW⟩ := Set.not_subset.mp (fam_not_le_of_wSet F hW1 L hL)
  obtain ⟨hLD, hLsyl⟩ := fam_mem_DSet_of_wSet F hW1 L hL
  exact ⟨⟨L, L, r, hL, hLD, hLsyl, hrL, hrW⟩, rfl⟩

theorem fam_mem_omegaStarNbr_of_wSet (F : Q8Fam Y Δ) (hW1 : WSet (Δ) = {W}) :
    ∀ K ∈ Δ, ∀ J ∈ Δ,
      K ≠ J → J ∈ omegaStarNbr (Δ) K := by
  intro K hK J hJ hne
  have hW : W ∈ WSet (Δ) := by rw [hW1]; rfl
  obtain ⟨ρ, rfl⟩ := fam_exists_rep_of_wSet F hW1 K hK
  obtain ⟨σ, rfl⟩ := fam_exists_rep_of_wSet F hW1 J hJ
  exact Q3T6.Mu.muTab_omegaStar F.partIHypG hW ρ σ hne

theorem fam_dstarConnected_of_wSet (F : Q8Fam Y Δ) (hW1 : WSet (Δ) = {W}) :
    T3.DStarConnected (Δ) := by
  intro K hK J hJ
  by_cases h : K = J
  · subst h
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      ⟨hJ, Or.inl (fam_mem_omegaStarNbr_of_wSet F hW1 K hK J hJ h)⟩

end ExitO2

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
