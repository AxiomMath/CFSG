module

public import CFSG.CGT.T75O.Root
public import CFSG.CGT.T75E.UtiInd
public import CFSG.CGT.T75G.Sec68Main
public import CFSG.CGT.Timmesfeld75.Sec68FromCorB

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.CGT.T75G CFSG.CGT.T75E

variable {G : Type} [Group G] {T T₁ : Subgroup G}


namespace Cfg56

variable (c : Cfg56 T T₁)
include c

theorem arsHyp (hL : ListWCIdentification) (hJ : ¬ NativeSporadic.IsSporadic G .J2) {a : G}
    (ha : a ∈ secA T T₁) (ha1 : a ≠ 1) : ARS.Hyp G (rootClass (CorB.cls a)) := by
  rcases arsHyp_or_exc_of_hyp (c.hyp ha ha1) with h | hA6 | hJ'
  · exact h
  · exact absurd (c.false_of_listGroup hL
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨6, le_rfl, by norm_num, hA6⟩))))) id
  · exact absurd hJ' hJ

theorem exists_setup (hL : ListWCIdentification) (hJ : ¬ NativeSporadic.IsSporadic G .J2)
    (hU : ¬ LieModel G .PSU 3 3 1) {a : G} (ha : a ∈ secA T T₁) (ha1 : a ≠ 1) :
    ∃ A₀ P P' : Subgroup G,
      ∃ _ : CaseH.Setup (rootClass (CorB.cls a)) (secA T T₁) A₀ P P',
        ¬ (Nat.card (secA T T₁) = 2 ∧
          (linesThrough (rootClass (CorB.cls a)) (secA T T₁)).ncard = 3) := by
  have := c.hy.finite
  have hs := c.setup ha ha1
  have h := c.arsHyp hL hJ ha ha1
  have hno : CorB.NoOppCentral (rootClass (CorB.cls a)) :=
    CorB.noOppCentral_rootClass hs.isRootInvolutionSet hs.noOddCent
  have hA : secA T T₁ ∈ rootClass (CorB.cls a) :=
    ⟨a, CorB.mem_cls_self a, (c.rootGroup_eq ha ha1).symm⟩
  by_cases hmax : IsCoatom (Subgroup.normalizer ((secA T T₁ : Subgroup G) : Set G))
  · have hσ := CorB.sigmaSet_eq_lambdaSet h hno hA
    have hH : SigmaEqLambda (rootClass (CorB.cls a)) := sigmaEqLambda_of_mem h.root hA hσ
    have h3 := CaseH.three_le_ncard_linesThrough h hH hA hmax
    by_cases h23 : Nat.card (secA T T₁) = 2 ∧
        (linesThrough (rootClass (CorB.cls a)) (secA T T₁)).ncard = 3
    · exact absurd (lieModel_PSU_of_caseH h hH hA h23.1 h23.2) hU
    · have hT := CaseH.mTransitive_of_not_two_three h hH hA h3 h23
      obtain ⟨A₀, P, P', S⟩ := CaseH.exists_setup h hH hT hA h3
      exact ⟨A₀, P, P', S, h23⟩
  · exfalso
    obtain ⟨f, -, -, hLM⟩ := caseL_psl3 h hno hA hmax
    have hm2 := statedClassicalModel_of_lieModel_of_ne_zero (by norm_num) hLM
    exact c.false_of_listGroup hL (Or.inl ⟨3, f, by norm_num, hm2.1.2.1, hm2⟩)

end Cfg56

end CFSG.CGT.T75O
