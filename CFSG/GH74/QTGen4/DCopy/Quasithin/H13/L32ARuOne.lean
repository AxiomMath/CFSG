module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU
public import CFSG.Quasithin.H13.L32ANotation
public import CFSG.Quasithin.H13.L32NInputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

namespace Hyp147

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem normalizes_F4 (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two_F4) :
    T ≤ Subgroup.normalizer (L : Set G) :=
  (h13322 G T L h.hyp.h13 L h.hyp.h13.faithful).1

theorem conjClosure_eq_F4 (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two_F4) :
    conjClosure L T = L :=
  le_antisymm
    (conjClosure_le fun _ ht l hl =>
      (Subgroup.mem_normalizer_iff.1 (h.normalizes_F4 h13322 ht) l).1 hl)
    (le_conjClosure L T)

theorem hyp1223_F4 (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two_F4) : Hyp1223 G T L V where
  simple := h.fsu.simple
  nonabelian := h.fsu.nonabelian
  qtke := h.fsu.qtke
  sylow := h.fsu.sylow
  notAlt := fun hA => h.hyp.h13.not_excluded (Hyp14310One.qt13Excluded_of_alt hA)
  maximal := h.fsu.maximal
  faithful := h.fsu.faithful
  quasisimple := h.fsu.quasisimple
  normalizes := h.normalizes_F4 h13322
  irrPlus := by
    have := h.fsu.irrPlus
    rwa [h.conjClosure_eq_F4 h13322] at this

theorem hyp1281One_F4 (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two_F4) (hV : StmtL32NModule_F4) :
    Hyp1281One G T L V 3 where
  hyp := h.hyp1223_F4 h13322
  n_mem := Or.inl rfl
  quot := nonempty_equiv_SL32_of_lieModel h.hyp.linear
  natural := (hV G T L V h.hyp h.fsu).2.2.2.2
  not_linear := fun hL => h.hyp.h13.not_excluded (Or.inr (Or.inl (Or.inl hL)))
  not_alt9 := fun hA => h.hyp.h13.not_excluded (Or.inr (Or.inr (Or.inl hA)))
  not_m24 := fun hM => h.hyp.h13.not_excluded (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl hM))))))

end Hyp147

end CFSG.Quasithin.H13
