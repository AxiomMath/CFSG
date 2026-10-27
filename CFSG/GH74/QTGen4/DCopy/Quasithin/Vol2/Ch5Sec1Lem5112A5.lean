module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112A5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.A3Structure314Cases

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

namespace EmbLoc

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
variable {S X K Kh : Subgroup G} (l : EmbLoc G S X K Kh)
include l

theorem a5_cases_F4 (hF : A314Facts_F4) (hNL : A314NotLie2)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (hL2 : LieModel (O2Q K) .PSL 2 2 2) :
    IsRank2LieChar2 (O2Q Kh) ∨
      (¬ IsLieTypeChar2 (O2Q Kh) ∧
        A314Statement (o2Img X S) (o2Img X K) (o2Img X Kh)) := by
  obtain ⟨eA⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hL2
  have hA : IsAlt 5 (↥(modO2Image X K) ⧸ CFSG.solvableRadical ↥(modO2Image X K)) :=
    A7.isAlt_quot_solvableRadical_of_surj ⟨eA⟩ (barMap_surjective l.le_X)
      (isPGroup_ker_barMap _)
  have hTL : IsSylowTwoOf (o2Img X S ⊓ modO2Image X Kh) (modO2Image X Kh) :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp l.hatBar_cComp) l.sylowBar
  have hB1 : modO2Image X K ∈ lFamily (o2Img X S ⊓ modO2Image X Kh) :=
    cComp_mem_of_le l.bar_lFamily le_sup_left (sup_le_sup_left inf_le_left _)
  have hlt := l.bar_lt
  obtain ⟨eH⟩ := l.hat_equiv
  have hL' := l.hatBar_cComp
  have h314 : A314Statement (o2Img X S) (modO2Image X K) (modO2Image X Kh) := by
    rcases l.cases h312 with hc | hnq
    · exact A314.of_case_F4 hF ⟨l.bar_lFamily, hlt, hTL, hB1, hA⟩ hc
    · have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot l.qtke l.simple l.nonabelian l.pCoreX
      rcases A314.nonquasi_case (h36 _ hQ _ hL') (A312.not_quasisimple_of_nonquasi hnq) hlt hA
        hnq with h13 | h14
      · unfold A314Statement
        iterate 12 right
        left
        exact h13
      · unfold A314Statement
        iterate 13 right
        exact h14
  have hnl : ∀ (hL : ¬ IsLieTypeChar2 ↥(modO2Image X Kh)),
      IsRank2LieChar2 (O2Q Kh) ∨
        (¬ IsLieTypeChar2 (O2Q Kh) ∧
          A314Statement (o2Img X S) (o2Img X K) (o2Img X Kh)) :=
    fun hL => Or.inr ⟨fun h => hL (IsLieTypeChar2.of_mulEquiv eH h), h314⟩
  have hlist : A314OverList ↥(modO2Image X Kh) → ¬ IsLieTypeChar2 ↥(modO2Image X Kh) :=
    hNL.1 _
  have h314' := h314
  unfold A314Statement at h314'
  rcases h314' with ⟨-, -, h1, -⟩ | ⟨-, h2, -⟩ | ⟨-, h3⟩ | ⟨-, h4, -⟩ | ⟨-, h5, -⟩ |
      ⟨-, -, -, h6⟩ | ⟨-, -, -, h7⟩ | ⟨-, h8, -⟩ | ⟨-, h9, -⟩ | ⟨-, -, h10⟩ | ⟨-, h11, -⟩ |
      ⟨-, -, h12, -⟩ | ⟨hB5, hLeq⟩ | ⟨-, h14⟩
  · exact Or.inl (IsRank2LieChar2.of_mulEquiv eH.symm (isRank2LieChar2_of_a314One h1))
  · exact hnl (hlist (Or.inl h2))
  · exact hnl (hlist (Or.inr (Or.inl h3)))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inl h4))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8))))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h9)))))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h10))))))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h11)))))))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr h12)))))))))))
  · refine hnl fun hLie => ?_
    have hs := hNL.2 _ hLie
    exact false_of_a314Thirteen hlt hB5 hLeq ⟨by
      have : Group.IsPerfect ↥(modO2Image X Kh) := A36A.isPerfect_of_mem_cComp hL'
      exact this.commutator_eq_top, hs⟩
  ·
    obtain ⟨p, hp, hp5, -, ⟨eSL⟩⟩ := h14
    refine hnl fun hLie => ?_
    have hs := hNL.2 _ hLie
    have : Group.IsPerfect ↥(modO2Image X Kh) := A36A.isPerfect_of_mem_cComp hL'
    have : IsSimpleGroup (↥(modO2Image X Kh) ⧸ Subgroup.center ↥(modO2Image X Kh)) := hs
    have hq : CFSG.IsQuasisimple ↥(modO2Image X Kh) := by
      have : Group.IsPerfect (↥(modO2Image X Kh) ⧸ Subgroup.center ↥(modO2Image X Kh)) :=
        Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
      have hnc := Group.IsPerfect.not_isMulCommutative
        (↥(modO2Image X Kh) ⧸ Subgroup.center ↥(modO2Image X Kh))
      refine ⟨inferInstance, hs, ?_⟩
      by_contra hall
      push Not at hall
      exact hnc ⟨⟨hall⟩⟩
    have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot l.qtke l.simple l.nonabelian l.pCoreX
    obtain ⟨hFO, -, hcases, -, -⟩ := (h36 _ hQ _ hL').2.1
    have hp2 : 2 < p := by
      rcases hp.eq_two_or_odd' with rfl | ho
      · norm_num at hp5
      · rcases hp.two_le.lt_or_eq with h2 | h2
        · exact h2
        · subst h2
          exact absurd ho (by decide)
    have : Fact (2 < p) := ⟨hp2⟩
    rcases hcases with ⟨hgF, -⟩ | ⟨hFZ, -, -⟩
    ·
      have hOtop : CFSG.oddCore ↥(modO2Image X Kh) = ⊤ := by
        rw [← hFO, ← hgF, A36A.generalizedFitting_eq_top hq]
      have : Subsingleton (↥(modO2Image X Kh) ⧸ CFSG.oddCore ↥(modO2Image X Kh)) := by
        rw [hOtop]
        exact QuotientGroup.subsingleton_quotient_top
      have := nontrivial_sl2 (p := p)
      obtain ⟨a, b, hab⟩ := exists_pair_ne (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
      exact hab (eSL.symm.injective (Subsingleton.elim _ _))
    ·
      have hOZ : CFSG.oddCore ↥(modO2Image X Kh) = Subgroup.center ↥(modO2Image X Kh) :=
        hFO.symm.trans hFZ
      have : IsSimpleGroup (↥(modO2Image X Kh) ⧸ CFSG.oddCore ↥(modO2Image X Kh)) :=
        (QuotientGroup.quotientMulEquivOfEq hOZ).isSimpleGroup
      exact not_isSimpleGroup_sl2 (p := p) (eSL.symm.isSimpleGroup)

end EmbLoc

end CFSG.Quasithin.H13
