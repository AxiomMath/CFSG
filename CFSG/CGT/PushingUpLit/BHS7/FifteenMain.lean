module

public import CFSG.CGT.PushingUpLit.BHS7.FifteenCaseTwo

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit.BHS5

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem fifteen_of_certificate (h : MinCex G T) (h5 : Seven5 G T)
    (h13 : Seven13 G T) (h14 : Seven14 G T) : ∃ Ê : Subgroup Γ, NatTailData G T Ê := by
  obtain ⟨E, hE, hEG, hsub, hnotle, hbaum, hBN⟩ := fifteen_comp h h5 h13 h14
  refine ⟨liftSub (vSub G T) G E, hsub, hnotle, hbaum, fun hH => ?_⟩
  exact ⟨vSub G T, h.charTwo, h.sylow, h.ne, le_normalizer_vSub G T,
    omegaOneCenterOf_le_vSub G T, vSub_le_omegaOneCenter h.charTwo h.sylow,
    caseTwo_natural h hE hEG hBN hH⟩

end CFSG.CGT.PushingUpLit.BHS7
