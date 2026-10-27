module

public import CFSG.CGT.T75E.J2
public import CFSG.CGT.T75E.LinTwoTrans
public import CFSG.CGT.T75E.UtiInd
public import CFSG.CGT.T75E.UtiLin
public import CFSG.CGT.T75E.Reduce

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75

section Hyp

variable {K : Type} [Group K] [Finite K] [IsSimpleGroup K] {T : Subgroup K}

theorem hyp_center_eq_bot (hyp : Lemma26Hyp K T) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hyp_ne_bot hyp)
    have ht1' : t ≠ 1 := fun e => ht1 (Subtype.ext e)
    exact hyp_classD_inf_center hyp (mem_classD_of_mem ht ht1') (h ▸ Subgroup.mem_top t)

theorem hyp_of_lemma26Hyp (hyp : Lemma26Hyp K T) (hnd : Lemma26Nondeg T) :
    CFSG.Timmesfeld.Hyp K (classD T) where
  finite := inferInstance
  isClass := hyp.2.2.1
  root := hyp.2.2.2.1
  gen := hyp.2.2.2.2
  oddCore := fun N hN hodd => by
    have := hN
    exact eq_bot_iff.2 ((hyp_oddCore_le_center hyp hodd).trans (hyp_center_eq_bot hyp).le)
  twoCore := fun N hN h2 => by
    have := hN
    exact eq_bot_iff.2 ((hyp_twoCore_le_center hyp h2).trans (hyp_center_eq_bot hyp).le)
  nondeg := hnd

end Hyp

section Outcome

variable {K : Type} [Group K]

theorem statedClassicalModel_of_lieModel_psl {n f : ℕ}
    (h : CFSG.Blueprint.LieModel K .PSL n 2 f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL n 2 f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)


theorem lemma26SimpleConcl_of_nondeg [Finite K] [IsSimpleGroup K]
    {T : Subgroup K} (hyp : Lemma26Hyp K T) (hnd : Lemma26Nondeg T) :
    Lemma26SimpleConcl K T := by
  rcases arsHyp_or_exc_of_hyp (hyp_of_lemma26Hyp hyp hnd) with hars | hA | hJ
  · obtain ⟨A, hA⟩ := rootGroupsIn_nonempty hyp
    obtain ⟨n, f, hn, hf, hL⟩ := lieModel_psl_of_isTI hars (isTI_rootGroupsIn hyp hars) hA
    have hM := statedClassicalModel_of_lieModel_psl hL
    refine ⟨Or.inl ⟨n, f, by omega, hf, hM⟩, fun _ => ?_⟩
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hM
    have : CharP F 2 := charP_two_of_card hF
    exact two_trans_psl hn e hyp.1 (hyp_ne_bot hyp)
  · exact ⟨Or.inr (Or.inr (Or.inr hA)), fun h => absurd hA h⟩
  · exact (j2_excl K T hyp hnd hJ).elim

end Outcome

end CFSG.CGT.T75E
