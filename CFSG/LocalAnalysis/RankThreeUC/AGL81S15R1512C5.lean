module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem quotCenter_of_isUFiveFour {S : Type} [Group S] (h : IsUFiveFour S) :
    ∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 ∧ Q.card = 4 ∧
      d.1 = .twistedA 4 Q ∧
      Nonempty ((S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨Q, hQ2, hc, d, hd, ⟨e⟩⟩ := h
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨⟨hp, -, hn, hne⟩, K, hKf, hKfin, hK, ⟨eP⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 Q hv (MulEquiv.refl _)
  haveI : Fact Q.p.Prime := ⟨hp⟩
  haveI hsimpleP : IsSimpleGroup
      (CFSG.Open.StatedProj (CFSG.Open.StatedSU (4 + 1) (Q.p ^ Q.exponent) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K Q.p Q.exponent hK (4 + 1)
      (by omega) hne
  haveI hperfSU : Group.IsPerfect (CFSG.Open.StatedSU (4 + 1) (Q.p ^ Q.exponent) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by omega) hne
  haveI hperfP : Group.IsPerfect
      (CFSG.Open.StatedProj (CFSG.Open.StatedSU (4 + 1) (Q.p ^ Q.exponent) K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.twistedA 4 Q, hv⟩).Group := eP.isSimpleGroup
  haveI : Group.IsPerfect (TauCeti.CFSGIndex.lie ⟨.twistedA 4 Q, hv⟩).Group :=
    Group.IsPerfect.ofSurjective (f := eP.symm.toMonoidHom) eP.symm.surjective
  haveI : IsSimpleGroup S := e.isSimpleGroup
  have hbot : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      haveI : Group.IsPerfect S :=
        Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      haveI : IsMulCommutative S :=
        ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm⟩⟩
      exact Group.IsPerfect.not_isMulCommutative S ‹_›
  exact ⟨⟨_, hv⟩, Q, hQ2, hc, rfl, ⟨(QuotientGroup.quotientMulEquivOfEq hbot).trans
    (QuotientGroup.quotientBot.trans e)⟩⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
