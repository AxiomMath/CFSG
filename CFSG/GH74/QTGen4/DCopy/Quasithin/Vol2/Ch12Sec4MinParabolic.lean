module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.Quasithin.Vol2.Ch1Local

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem Hyp1223.minParabolic_of_isHStar_F4 (h331 : Stmt3_3_1_F4) (h : Hyp1223 G T L V)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    MinParabolic H T (H ⊓ Subgroup.normalizer (L : Set G)) := by
  have h3 := (h331 G T h.simple h.nonabelian h.qtke h.sylow).2 L h.maximal h.quasisimple
  rw [h.conjClosure_eq] at h3
  obtain ⟨-, -, -, -, hall⟩ := h3
  obtain ⟨hU, hT⟩ := hall H hH
  exact ⟨isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hH.1.1, hT, hU⟩

end CFSG.Quasithin.H13
