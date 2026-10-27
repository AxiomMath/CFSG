module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem515
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Hyp5_0_1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

theorem hyp318_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) (hV : IsCh5Module T L V)
    {H : Subgroup G} (hH : IsHStar T M H) : Hyp318 T M L V where
  inM := ⟨h.maxTwoLocal, h.T_le⟩
  nonempty := ⟨H, hH⟩
  perfect := h.oTwoUpper_eq.symm
  le_M := h.L_le
  normal := h.normal
  unique := h.isUniqueM_F4 h331
  reduced := hV.isTwoReducedIn
  centralizer := (h.centralizer_eq_pCoreOf hV).symm

end Hyp5_0_1

end CFSG.Quasithin.H13
