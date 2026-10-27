module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroSupport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroSingle
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.ComponentClassification.TBLitComponents
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isComponent_or_swappedBar_of_l34
    (hcat : L34CyclicProperFixedCatalog)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hG : L34BaseSetting G) (hhost : L34ZeroHostFree G) {x b : G} (hx : orderOf x = 2)
    (hb : orderOf b = 2) (hxb : x ∈ centralizer ({b} : Set G)) {P : Subgroup G}
    (hPx : P ≤ centralizer ({x} : Set G)) (hPb : P ≤ centralizer ({b} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({x} : Set G))))
    (hPodd : Odd (Nat.card (center ↥P))) (hPL : IsL34Type (↥P ⧸ center ↥P))
    {F : Subgroup G} (hFP : F ≤ centralizer (P : Set G)) (hFb : F ≤ centralizer ({b} : Set G))
    (hF : Open.IsElemAbelian 2 F) (hF8 : 8 ≤ Nat.card F) (hW : wGroup F = ⊥) :
    IsComponent (P.subgroupOf (centralizer ({b} : Set G))) ∨ L34ZeroSwappedBar x b hxb P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG' := hG
  obtain ⟨hsimple, hnonab, hKproper, -⟩ := hG'
  let X : Subgroup G := centralizer ({b} : Set G)
  have hPX : P ≤ X := hPb
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb
    omega
  have hKX : SectionRank.IsKGroupCat ↥X :=
    TBLit.isKGroupCat_centralizer hKproper
      (@GrS5.not_mem_center_of_ne_one G _ hsimple hnonab b hb1)
  have hPq : IsQuasisimple ↥P :=
    (IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hPx)).mp hcomp.1
  have hcompCx : Assembly.IsComponentOf P (centralizer ({x} : Set G)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hPx).mpr hcomp
  have hcompCX : IsComponent (P.subgroupOf (centralizer ({x} : Set G) ⊓ X)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      (le_inf hPx hPX)).mp (hcompCx.of_le_of_le (le_inf hPx hPX) inf_le_left)
  have hLY : P.subgroupOf X ≤ (centralizer ({x} : Set G) ⊓ X).subgroupOf X := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact ⟨hPx hy, y.2⟩
  let eA : ↥((P.subgroupOf X).subgroupOf
      ((centralizer ({x} : Set G) ⊓ X).subgroupOf X)) ≃*
      ↥(P.subgroupOf (centralizer ({x} : Set G) ⊓ X)) :=
    (Subgroup.subgroupOfEquivOfLe hLY).trans
      ((Subgroup.subgroupOfEquivOfLe hPX).trans
        (Subgroup.subgroupOfEquivOfLe (le_inf hPx hPX)).symm)
  have hΛ : IsComponent ((P.subgroupOf X).subgroupOf
      (centralizer ({⟨x, hxb⟩} : Set ↥X))) := by
    rw [UGSChain.centralizer_mk_eq_subgroupOf hxb]
    exact ⟨(IsQuasisimple.congr eA).mpr hcompCX.1,
      (CFSG.GroupTheory.isSubnormal_subgroupOf_subgroupOf_iff (B := P)
        (L := centralizer ({x} : Set G) ⊓ X) (K := X) inf_le_right).mpr hcompCX.2⟩
  have hΛs : (P.subgroupOf X) ≤ centralizer ({⟨x, hxb⟩} : Set ↥X) := by
    rw [UGSChain.centralizer_mk_eq_subgroupOf hxb]
    exact hLY
  have hs : orderOf (⟨x, hxb⟩ : ↥X) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hx
  have hPoddX : Odd (Nat.card (center ↥(P.subgroupOf X))) := by
    rw [Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hPX)).toEquiv]
    exact hPodd
  have hPLX : IsL34Type (↥(P.subgroupOf X) ⧸ center ↥(P.subgroupOf X)) :=
    Blueprint.LieModel.quotient_center_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPX).symm hPL
  rcases l34Zero_support hcat hKX hs hΛs hΛ hPoddX hPLX with
    hsingle | ⟨L, hL, hΛL, hLfix, htype⟩ | ⟨L, hL, hLne, -, -, hsupp⟩
  · exact Or.inl (isComponent_of_isComponent_map_of_l34 hSch hU hheld hG hb hPb hPq hsingle
      hFP hFb hF hF8 hW)
  · exact (hhost x b hxb P hx hb hPx hPb hcomp hPodd hPL L hL hΛL hLfix htype).elim
  · exact Or.inr ⟨L, hL, hLne, hsupp⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
