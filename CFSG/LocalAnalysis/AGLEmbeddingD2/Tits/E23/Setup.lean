module

public import CFSG.CGT.PushingUpLit.BHS5.AmbientJ
public import CFSG.CGT.PushingUpLit.BHS.FourSymI
public import CFSG.Quasithin.Background.E2SolvBlocks

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5

variable {G : Type} [Group G] [Finite G] {H T M : Subgroup G}

omit [Finite G] in
theorem vZ_le_of_le_centralizer (hH : H ≤ Subgroup.centralizer (omegaOneCenterOf T : Set G)) :
    VZ T H ≤ omegaOneCenterOf T := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨h, hh, z, hz, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.1 (hH hh) z hz
  have : h * z * h⁻¹ = z := by rw [← hc]; group
  rw [this]
  exact hz

theorem cStarStarIn_le_M (hmin : MinParabolic H T M) (hmp : MinPar H T M)
    (hred : IsTwoReducedIn H (VZ T H))
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G)) : cStarStarIn H T ≤ M := by
  have hTH : T ≤ H := hmin.isSylow.1
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  refine sup_le (hmp.max _ ?_ ?_) (hmp.max _ ?_ ?_)
  · refine le_inf hTH fun t ht => Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    exact (Subgroup.mem_centralizer_iff.1 (C1GN.omegaOneCenterOf_le_centerOf T hz).2 t ht).symm
  · refine lt_of_le_of_ne inf_le_left fun heq => hJ ?_
    have hle : H ≤ Subgroup.centralizer (omegaOneCenterOf T : Set G) := by
      rw [← heq]
      exact inf_le_right
    intro j hj
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    have hvZ := (C1GN.omegaOneCenterOf_le_centerOf T (vZ_le_of_le_centralizer hle hv)).2
    exact (Subgroup.mem_centralizer_iff.1 hvZ j (hJT hj)).symm
  · exact le_inf hTH (Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T))
  · refine lt_of_le_of_ne inf_le_left fun heq => hJ ?_
    have hle : H ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
      rw [← heq]
      exact inf_le_right
    have hJQ : thompsonJ T ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hJT.trans hTH) hle
        (hmin.isSylow.2.1.to_le hJT)
    exact hJQ.trans (MinParabolic.pCoreOf_le_centralizer hred)

theorem vHyp_of_e23 (hV : IsElemAbelian 2 (VZ T H)) (hmin : MinParabolic H T M)
    (hmp : MinPar H T M) (hF : CharTwo H) (hred : IsTwoReducedIn H (VZ T H))
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G)) : VHyp H T M (VZ T H) where
  charTwo := hF
  minpar := hmp
  ne := fun heq => by
    have h1 := cStarStarIn_le_M hmin hmp hred hJ
    rw [heq] at h1
    exact (lt_irrefl _ (lt_of_le_of_lt h1 hmp.lt_P))
  elem := hV
  le_T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow)
  normalized := hred.2.1
  pCore_le := MinParabolic.pCoreOf_le_centralizer hred
  cen_le_M := (hmin.inf_centralizer_le_kerIn hred (E2.not_le_centralizer hmin hJ)).trans kerIn_le
  omega_le := le_conjClosure _ _
  J_not_le := hJ

variable (hV : IsElemAbelian 2 (VZ T H)) (hmin : MinParabolic H T M) (hmp : MinPar H T M)
  (hF : CharTwo H) (hred : IsTwoReducedIn H (VZ T H))
  (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G))

include hmin hmp hF hred hJ

theorem hyp51_of_e23 : Hyp51 (autI hV H) (autI hV T) (autI hV M) :=
  (vHyp_of_e23 hV hmin hmp hF hred hJ).hyp51

theorem fiveFive_of_e23 :
    FiveFive (autI hV H) (autI hV T) (autI hV M) (compSet (autI hV H) (autI hV M)) :=
  five_five bhsSymType (hyp51_of_e23 hV hmin hmp hF hred hJ) fun v => IntMod.sq_eq_one v

theorem autI_thompsonJ_eq_genD :
    autI hV (thompsonJ H) = genD (autI hV H) :=
  le_antisymm ((vHyp_of_e23 hV hmin hmp hF hred hJ).autOn_thompsonJ_le bhsSymType)
    ((vHyp_of_e23 hV hmin hmp hF hred hJ).genD_le_autOn_thompsonJ bhsSymType)

end CFSG.AGLEmbeddingD2.Tits.E23
