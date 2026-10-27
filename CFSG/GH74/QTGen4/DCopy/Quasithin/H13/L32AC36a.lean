module

public import CFSG.Quasithin.H13.L32AC36a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC47c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem m22_or_hat_of_sporadic_F4 (h30 : Lemma14_7_30_F4) (h32 : Lemma14_7_32_F4) (hD310 : D310)
    (hD391 : D391) (hI4 : Insp4) (hFine : F918Fine4) (hdisj : SporadicFourListDisjoint)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H) {s : TauCeti.SporadicName}
    (hs : IsSporadic s (cStar K ⧸ Subgroup.center (cStar K))) :
    IsSporadic .M22 (cStar K) ∨ IsHat (cStar K) (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  obtain ⟨-, hTK, S₀, hF⟩ := reduce_KL1T_F4 h30 h32 S hK
  have hSQ := sqtkGroup_of_setting S₀
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have h4 := (F918_4_fine' hF hSQ (conjClosure_T_eq_self hTK) hV₁I hIU W hW hirrU
    hD310 hD391 hI4 hFine).1
  obtain ⟨eA⟩ := L1295B.nonempty_mulEquiv_autIH hF
  have hfine := fourListFine_of_mulEquiv ((cStarEquiv K).trans eA) h4
  exact hfine.2.2 (hdisj _ s hs hfine.1)

end CFSG.Quasithin.H13.L32A.C
