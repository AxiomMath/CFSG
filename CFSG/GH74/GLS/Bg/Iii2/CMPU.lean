module

public import CFSG.GH74.GLS.Bg.Iii2.Statements
public import CFSG.GH74.GLS.C3.Layer1.St1RigDiag3

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.C3.Layer1.PumpRigid

namespace CMEngine

variable {G : Type} [Group G] [Finite G]

theorem isRigidRankOneComp_of_pumpUpLT {x u : G} {K J : Subgroup G} (hK : IsRigidRankOneComp x K)
    (hlt : PumpUpLT 2 x K u J) : IsRigidRankOneComp u J := by
  obtain ⟨e⟩ := hK.1.2 u J (LongPumpUp.single' hlt)
  refine ⟨⟨hlt.2.1, fun x' K' hl => ?_⟩, ?_⟩
  · obtain ⟨e'⟩ := hK.1.2 x' K' (LongPumpUp.trans' (LongPumpUp.single' hlt) hl)
    exact ⟨e'.trans e.symm⟩
  · have h1 : pRank 2 (Hat J) = pRank 2 (Hat K) := pRank_eq_of_mulEquiv' e
    rw [← pRank_hat J, h1, pRank_hat K]
    exact hK.2

end CMEngine

theorem pu_of : PU := by
  intro G _ _ hG h3 x u K hK huo hux huK
  have hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := fun y hy =>
    TwoThin.rankThreeCentralizers G hG.1 hG.2.1 h3 y hy
  obtain ⟨J, hJ⟩ := exists_pumpUpLT hK.1.1 huo (Subgroup.mem_inf.mpr ⟨hux, huK⟩) (hR u huo)
  exact ⟨J, CMEngine.isRigidRankOneComp_of_pumpUpLT hK hJ⟩

end CFSG.GH74.GLS.Bg.Iii2
