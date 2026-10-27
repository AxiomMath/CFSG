module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec63PT_exists_equiv_p3 {G : Type} [Group G] {Y : Subgroup G} (h : IsOmega6Plus Y) :
    Nonempty (↥Y ⧸ oddCore ↥Y ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 (ZMod 3)) := by
  unfold IsOmega6Plus at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK]
    norm_num
  exact ⟨e.trans (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr
    (FiniteField.ringEquivOfCardEq hc))⟩

theorem sec63PT_nontrivial_p3 :
    Nontrivial (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 (ZMod 3)) := by
  have hsimple : IsSimpleGroup
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 (ZMod 3)) := by
    have := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 3) (n := 4) (by norm_num)
      (Or.inl (by norm_num))).2.1
    exact (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      4 (ZMod 3)).symm.isSimpleGroup
  exact hsimple.toNontrivial

theorem sec63PT_std_form
    (α : MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 (ZMod 3))) :
    ∃ (A : GL (Fin 4) (ZMod 3)) (ε : ℕ), ε ≤ 1 ∧
      α = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 4 (ZMod 3) A *
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut 4 (ZMod 3) ^ ε := by
  obtain ⟨A, σ, ε, hε, h⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_std_of_mulEquiv (n := 4) (K := ZMod 3)
      (by norm_num) (MulEquiv.refl _) α
  have hσ : σ = 1 := Subsingleton.elim σ 1
  have hc : MulAut.congr (MulEquiv.refl
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 (ZMod 3))) α = α := by
    ext x
    rfl
  rw [hc, hσ, map_one, mul_one] at h
  exact ⟨A, ε, hε, h⟩

end CFSG.OddStandard.SmallF3.Omega
