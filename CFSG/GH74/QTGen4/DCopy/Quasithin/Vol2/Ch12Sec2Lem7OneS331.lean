module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7One
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Lem7

theorem minParabolic_F4 (h331 : Stmt3_3_1_F4) {T L V H : Subgroup G} (hH : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    MinParabolic H T (H ⊓ Subgroup.normalizer (L : Set G)) := by
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq hH.sylow
  have hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨-, -, -, hNT, -⟩ :=
      (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
    rwa [hH.conjClosure_eq] at hNT
  refine ⟨isSylowTwoOf_of_isSylowTwo hH.sylow hHs.1.1, fun h => hHs.2.1 (h.trans hNT), ?_⟩
  subst hS
  exact IsHStar.isUniqueMaxOver S hHs hH.normalizes

end Lem7

open Lem7

end CFSG.Quasithin.H13
