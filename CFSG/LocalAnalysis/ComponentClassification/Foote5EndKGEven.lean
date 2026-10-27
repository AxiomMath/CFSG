module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank

theorem not_isSolvable_centralizer_of_isTwoComponentAt {X : Type*} [Group X] [Finite X] {z : X}
    {K : Subgroup X} (hK : IsTwoComponentAt z K) :
    ¬ Group.IsSolvable ↥(centralizer ({z} : Set X)) := by
  intro hs
  have : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hK.2.1)
  exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple
    (isQuasisimple_quotient_of_isPComponent hK.2.1 hK.2.2) inferInstance

theorem exists_mul_ne_mul_of_isTwoComponentAt {X : Type*} [Group X] [Finite X] {z : X}
    {K : Subgroup X} (hK : IsTwoComponentAt z K) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcomm
  refine not_isSolvable_centralizer_of_isTwoComponentAt hK
    (Group.isSolvable_of_comm fun x y => Subtype.ext ?_)
  by_contra h
  exact hcomm ⟨x, y, h⟩

theorem endKnownGroupsInputOn_evenLieType
    (hodd : Sol78.F514.EndOddLieInput)
    (hspor : EndKnownGroupsInputOn fun X _ => Blueprint.NativeSporadic.SporadicRep X) :
    EndKnownGroupsInputOn fun X _ => ∃ (τ : StatedLieTag) (n f : ℕ),
      StatedLieAdmissible τ n 2 f ∧ Blueprint.LieModel X τ n 2 f := by
  intro X _ _ hXs heven z t K P D hK huniq hKs hKt hIE hP htP ht hzt hzD hD hPD hDd hD8 hsolv hNP
  have : IsSimpleGroup X := hXs
  have hna := exists_mul_ne_mul_of_isTwoComponentAt hK
  rcases CatLeaf.oddCore_eq_bot_or_uList_of_evenLieType hna heven hK.1 with hcore | hU
  ·
    exact absurd ⟨Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hK.2.2,
      hK.2.2.choose_spec.2.1⟩
      (CatLeaf.involutionCentralizersComponentFree_of_evenLieType heven z hK.1 _)
  rcases hU with hoddX | ⟨n, -, h7, hA⟩ | hL34 | hHe
  · exact endKnownGroupsInputOn_oddLieType hodd X hXs hoddX z t K P D hK huniq hKs hKt hIE hP
      htP ht hzt hzD hD hPD hDd hD8 hsolv hNP
  · exact endKnownGroupsInputOn_alternating X hXs ⟨n, by omega, hA⟩ z t K P D hK huniq hKs hKt
      hIE hP htP ht hzt hzD hD hPD hDd hD8 hsolv hNP
  ·
    have hC := (PSL3Four.excludes_alternating_models_stated.{0} X
      (CatLeaf.statedClassicalModel_of_lieModel_psl hL34)).2.1 z hK.1
    have hC2 : IsPGroup 2 ↥(centralizer ({z} : Set X)) :=
      IsPGroup.of_card (n := 6) (by rw [hC]; norm_num)
    have : Group.IsNilpotent ↥(centralizer ({z} : Set X)) := hC2.isNilpotent
    exact (not_isSolvable_centralizer_of_isTwoComponentAt hK inferInstance).elim
  · exact hspor X hXs ⟨.He, hHe⟩ z t K P D hK huniq hKs hKt hIE hP htP ht hzt hzD hD hPD hDd
      hD8 hsolv hNP

theorem endKnownGroupsInput_of_oddLie_sporadic
    (hodd : Sol78.F514.EndOddLieInput)
    (hspor : EndKnownGroupsInputOn fun X _ => Blueprint.NativeSporadic.SporadicRep X) :
    EndKnownGroupsInput :=
  endKnownGroupsInput_of_families hodd (endKnownGroupsInputOn_evenLieType hodd hspor)
    endKnownGroupsInputOn_alternating hspor

end CFSG.ComponentClassification.Foote5
