module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

namespace Hyp5_0_1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

theorem normalizer_le_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) :
    Subgroup.normalizer (T : Set G) ≤ M :=
  (h331 G T h.simple h.nonabelian h.qtke h.sylow).1 M L h.maxTwoLocal h.T_le h.maximal h.L_le
    h.isQuasisimple

theorem minParabolic_of_isHStar_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) {H : Subgroup G}
    (hH : IsHStar T M H) :
    MinParabolic H T (H ⊓ M) ∧ (1 < E1.nParam H → ¬ Group.IsSolvable ↥H ∧ SQTKGroup ↥H) := by
  refine ⟨⟨h.isSylowTwoOf hH.1.1, hH.not_le_normalizer (h.normalizer_le_F4 h331), ?_⟩, ?_⟩
  · obtain ⟨S, rfl⟩ := exists_sylow_coe_eq h.sylow
    exact hH.isUniqueMaxOver S h.T_le
  · intro hn
    refine ⟨fun hsolv => ?_, ?_⟩
    · have := E1.solvable_nParam_le_one hsolv
      exact absurd hn (not_lt.mpr this)
    · obtain ⟨hk, hq⟩ := isSQTKSub_of_inH h.qtke h.simple h.nonabelian hH.1
      exact ⟨hq, hk⟩

end Hyp5_0_1

theorem stmt5_1_1_of_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) : Stmt5_1_1_F4 := by
  intro G _ _ T M L V n h hV
  exact ⟨h.centralizer_eq_pCoreOf hV, fun H hH => h.minParabolic_of_isHStar_F4 h331 hH,
    fun H hH => h.hyp315Base hV hH, ⟨_, h.minParabolic_sup hR⟩⟩

end CFSG.Quasithin.H13
