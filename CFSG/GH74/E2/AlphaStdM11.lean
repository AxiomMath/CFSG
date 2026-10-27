module

public import CFSG.GH74.E2.BlackBoxesStdM11
public import CFSG.GH74.E2.AlphaStd
public import CFSG.GH74.AS16.E2.ShapeCards

public section

namespace CFSG.GH74.E2

open Subgroup

theorem false_of_M11_rank_two
    (hComp : ComponentList) (hP : PumpUpData) (hD3 : K0Data3)
    (hI : NoCaseI) (hAS : AschbacherStandardM11) {G : Type} [Group G] [Finite G] (hH : Hyp G)
    {t : G} (ht : orderOf t = 2) {K : Subgroup G} (hK : IsCompCen t K) (hsh : ShapeM11 ↥K)
    {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v) (hcomm : u * v = v * u)
    (huK : ∀ k ∈ K, u * k = k * u) (hvK : ∀ k ∈ K, v * k = k * v) : False := by
  have hcard : Nat.card ↥K = 7920 := AS16.E2.card_of_shapeM11 hsh
  have hterm := isTerminalPair_of_card hComp hP hH ht hK (by omega) (by omega)
  have hq := isCompCen_quasisimple hK
  have hZ : center ↥K = ⊥ :=
    hD3.center_bot ↥K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsh)))))
  have hSub := AS16.E2.Local3Sub.of_table (AS16.E2.local3Data_M11 ↥K hsh)
    (hD3.inner3 ↥K (Or.inr (Or.inr hsh)))
  have htC : t ∈ centralizer (K : Set G) :=
    mem_centralizer_iff.2 fun k hk => (mem_Cen.1 (hK.1 hk)).symm
  have hstd : CFSG.IsStandardSubgroup K :=
    AS16.isStandardSubgroup_of_terminal hq ht htC (fun y hy hy2 => hterm.2.2.2 y hy2 hy)
      (fun g hg => false_of_isCompIn_conj_centralizer hI hH hq hZ hSub.elemAb9 hSub.exists3 g hg)
  exact hAS G hH.simple hH.nonabelian hH.kgh K hstd hsh
    ⟨u, v, hu, hv, huv, hcomm, mem_centralizer_iff.2 fun k hk => (huK k hk).symm,
      mem_centralizer_iff.2 fun k hk => (hvK k hk).symm⟩

theorem noCaseIIAlphaM11_of_standard
    (hComp : ComponentList) (hP : PumpUpData) (hD3 : K0Data3)
    (hI : NoCaseI) (hAS : AschbacherStandardM11) : NoCaseIIAlphaM11 := by
  intro G _ _ hH t t' a A B K hc hK hsh _ _ ht'K
  exact false_of_M11_rank_two hComp hP hD3 hI hAS hH hc.order_t hK hsh hc.order_t hc.order_t'
    hc.ne hc.comm (fun k hk => mem_Cen.1 (hK.1 hk)) ht'K

end CFSG.GH74.E2
