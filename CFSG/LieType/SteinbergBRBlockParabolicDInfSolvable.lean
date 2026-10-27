module

public import CFSG.LieType.SteinbergBRBlockParabolicDInf

public section

namespace CFSG.LieType.SteinbergBR.BlockPar

open Matrix

variable {F : Type*} [Field F] {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
  [DecidableEq b]

theorem isSolvable_quotient_ker_of_isSolvable {G H : Type*} [Group G] [Group H] (f : G →* H)
    [Group.IsSolvable H] : Group.IsSolvable (G ⧸ f.ker) := by
  have : Group.IsSolvable f.range := inferInstance
  exact Group.isSolvable_of_isSolvable_injective
    (f := (QuotientGroup.quotientKerEquivRange f).toMonoidHom) (MulEquiv.injective _)

theorem perfectResidual_parQ_eq_parJR_of_isSolvable [Finite F] [Nontrivial b]
    (hGL : Group.IsSolvable (GL a F)) (hSL : commutator (SpecialLinearGroup b F) = ⊤) :
    CFSG.perfectResidual (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)) =
      (parJR F a b).subgroupOf parQ := by
  obtain ⟨-, -, -, -, hiff, -⟩ :=
    CFSG.perfect_residual_characterization (G := (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)))
  obtain ⟨-, -, hperf⟩ := CFSG.perfect_residual_transport
    (MonoidHom.id (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)))
  refine le_antisymm ?_ (hperf _ (isPerfect_subgroupOf parJR_le_parQ (commutator_parJR hSL)))
  rw [← ker_chiL]
  exact (hiff _).1 (isSolvable_quotient_ker_of_isSolvable _)

theorem perfectResidual_parQ_eq_parJL_of_isSolvable [Finite F] [Nontrivial a]
    (hGL : Group.IsSolvable (GL b F)) (hSL : commutator (SpecialLinearGroup a F) = ⊤) :
    CFSG.perfectResidual (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)) =
      (parJL F a b).subgroupOf parQ := by
  obtain ⟨-, -, -, -, hiff, -⟩ :=
    CFSG.perfect_residual_characterization (G := (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)))
  obtain ⟨-, -, hperf⟩ := CFSG.perfect_residual_transport
    (MonoidHom.id (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)))
  refine le_antisymm ?_ (hperf _ (isPerfect_subgroupOf parJL_le_parQ (commutator_parJL hSL)))
  rw [← ker_chiR]
  exact (hiff _).1 (isSolvable_quotient_ker_of_isSolvable _)

end CFSG.LieType.SteinbergBR.BlockPar
