module

public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section KGroup

theorem isKGroup_of_subgroup {X : Type*} [Group X] (hX : CFSG.Open.IsKGroup X) (H : Subgroup X) :
    CFSG.Open.IsKGroup ↥H :=
  hX.subgroup H

theorem isKGroup_quotient {X : Type*} [Group X] (hX : CFSG.Open.IsKGroup X) (M : Subgroup X)
    [M.Normal] : CFSG.Open.IsKGroup (X ⧸ M) :=
  hX.quotient M

end KGroup

section LThreeFour

private theorem exists_equiv_projectiveSL {X : Type} [Group X] (h : IsLThreeFour X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hcard,
    ⟨(e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 F)⟩⟩

theorem card_eq_of_isLThreeFour {X : Type} [Group X] (h : IsLThreeFour X) :
    Nat.card X = 20160 := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := exists_equiv_projectiveSL h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.card_projectiveSL_three_four hcard

theorem isLThreeFour_card_eq {X Y : Type} [Group X] [Group Y] (hX : IsLThreeFour X)
    (hY : IsLThreeFour Y) : Nat.card X = Nat.card Y := by
  rw [card_eq_of_isLThreeFour hX, card_eq_of_isLThreeFour hY]

theorem isSimpleGroup_of_isLThreeFour {X : Type} [Group X] (h : IsLThreeFour X) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hcard := card_eq_of_isLThreeFour h
  obtain ⟨F, _, _, -, ⟨e⟩⟩ := h
  have e' : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
  have hs : IsSimpleGroup X :=
    e'.isSimpleGroup_congr.2
      (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by norm_num)
        (Or.inl le_rfl)).2.1
  refine ⟨hs, ?_⟩
  by_contra hno
  push Not at hno
  let _ : CommGroup X := { ‹Group X› with mul_comm := fun a b => hno a b }
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hp := IsSimpleGroup.prime_card (α := X)
  rw [hcard] at hp
  exact absurd hp (by norm_num)

end LThreeFour

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
