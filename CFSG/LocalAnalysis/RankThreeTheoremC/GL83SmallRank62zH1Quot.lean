module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zDefs
public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.LocalAnalysis.GLTheoremB CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {f : ℕ} {X Q : Subgroup G}

structure k631aHyp (f : ℕ) (X Q : Subgroup G) : Prop where
  prime : f.Prime
  ne_two : f ≠ 2
  kgroup : IsKGroup ↥X
  le : Q ≤ X
  pgroup : IsPGroup f Q
  sylow : ¬ f ∣ (Q.subgroupOf X).index
  comm : IsMulCommutative Q

omit [Finite G] in
theorem k631a_hyp_of_layer (hL : LayerHyp f X Q) : k631aHyp f X Q :=
  ⟨hL.prime, hL.ne_two, hL.kgroup, hL.le, hL.pgroup, hL.sylow, hL.comm⟩

structure k631aBHyp (f : ℕ) {B : Type} [Group B] (Q : Subgroup B) : Prop where
  prime : f.Prime
  ne_two : f ≠ 2
  core : GLAPPrimeCore f B = ⊥
  catalog : CatalogSimpleSections B
  pgroup : IsPGroup f Q
  sylow : ¬ f ∣ Q.index
  comm : IsMulCommutative Q

theorem k631a_catalog_of_kgroup {X : Type} [Group X] (h : IsKGroup X) : CatalogSimpleSections X :=
  fun K L hL hs _ => by
    let _ := hL
    exact h K L hs

theorem k631a_bhyp_barX (h : k631aHyp f X Q) : k631aBHyp f (barX f X Q) := by
  refine ⟨h.prime, h.ne_two, glaPPrimeCore_quotient_eq_bot h.prime,
    (k631a_catalog_of_kgroup h.kgroup).quotient _, ?_, ?_, ?_⟩
  · have h1 : IsPGroup f ↥(Q.subgroupOf X) :=
      h.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm
    exact h1.map (QuotientGroup.mk' (GLAPPrimeCore f ↥X))
  · exact fun hd => h.sylow (hd.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  · refine IsMulCommutative.of_comm ?_
    rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩
    refine Subtype.ext ?_
    have hxy := h.comm.is_comm.comm (⟨(x : G), hx⟩ : ↥Q) ⟨(y : G), hy⟩
    have hxy1 : (x : G) * y = y * x := congrArg Subtype.val hxy
    have hxy' : x * y = y * x := Subtype.ext hxy1
    show QuotientGroup.mk' (GLAPPrimeCore f ↥X) x * QuotientGroup.mk' (GLAPPrimeCore f ↥X) y =
      QuotientGroup.mk' (GLAPPrimeCore f ↥X) y * QuotientGroup.mk' (GLAPPrimeCore f ↥X) x
    rw [← map_mul, ← map_mul, hxy']

end CFSG.LocalAnalysis.RankThreeTheoremC
