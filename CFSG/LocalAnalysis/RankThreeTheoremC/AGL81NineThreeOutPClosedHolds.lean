module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeOutPClosedOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowClassical
public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowExceptional
public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowSporadic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.ComponentClassification.OuterAutomorphisms

theorem sylow_normal_outer_nineThree
    (p : ℕ) (i : TauCeti.CFSGIndex) (hp : p.Prime) (hp2 : p ≠ 2) (hi : IsNineThreeIndex p i) :
    ∀ S : Sylow p (Outer i.Group), (S : Subgroup (Outer i.Group)).Normal := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases i with ⟨q, hq⟩ | ⟨n, hn⟩ | ⟨d, hv⟩ | s
  · exact hi.elim
  · exact sylow_normal_outer_alternating_nineThree hp2 n hn hi
  · rcases hi with ⟨q, hqp, hqe, hd⟩ | ⟨q, hqp, hd⟩ | hsp | ⟨q, hqp, hqe, hd⟩ | ⟨hp3, m, hd⟩ |
        ⟨hp3, ⟨q, hq2, hq3, hd | hd | hd⟩ | ⟨q, hq2, hq2', hd⟩ | ⟨q, hq2, hq1, hd⟩ | hd⟩ |
        ⟨hp5, hd | hd | hd⟩
    · dsimp only at hd; subst hd; exact sylow_normal_outer_A1 q hv
    · dsimp only at hd; subst hd; exact sylow_normal_outer_twistedA2 hp2 q hv
    · exact sylow_normal_outer_spFour hp2 ⟨d, hv⟩ hsp
    · dsimp only at hd; subst hd; exact sylow_normal_outer_A2 hp2 q hv
    · dsimp only at hd; subst hd; exact sylow_normal_outer_reeG2 m hv
    · dsimp only at hd; subst hd; exact sylow_normal_outer_A1 q hv
    · dsimp only at hd; subst hd
      exact sylow_normal_outer_G2 q hv (by rw [hq2, hq3]; norm_num)
    · dsimp only at hd; subst hd; subst hp3; exact sylow_normal_outer_B2_eight q hq2 hq3 hv
    · dsimp only at hd; subst hd; exact sylow_normal_outer_A2 hp2 q hv
    · dsimp only at hd; subst hd; exact sylow_normal_outer_B3_two q hq2 hq1 hv
    · dsimp only at hd; subst hd; exact sylow_normal_outer_tits hp2 hv
    · dsimp only at hd; subst hd; exact sylow_normal_outer_suzuki 2 hv
    · dsimp only at hd; subst hd; exact sylow_normal_outer_tits hp2 hv
    · dsimp only at hd; subst hd; exact sylow_normal_outer_reeF4 2 hv
  · exact sylow_normal_outer_sporadic_nineThree hp2 s hi

theorem kFactNineThreeOutPClosed_holds :
    KFactNineThreeOutPClosed :=
  kFactNineThreeOutPClosed_of_simple fun p i hp hp2 hi _ =>
    sylow_normal_outer_nineThree p i hp hp2 hi

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
