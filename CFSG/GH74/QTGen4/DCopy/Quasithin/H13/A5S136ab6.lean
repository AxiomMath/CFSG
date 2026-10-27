module

public import CFSG.Quasithin.H13.A5S136ab6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136ab3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136ab5

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace ConfAB

end ConfAB

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem false_of_lieZCent_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hEven : Ch1.EvenLieAutInner) (hF1 : FactLieZCent) (hF2 : FactLieOutAbelian)
    (hF3 : FactLieZCentPGL3) (hF6 : FactL3SylowCenterCyclic) (h122 : Vol2Native.Lemma122A)
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hSQ : Ch1.SQTKCharTwoLie (↥K ⧸ CFSG.pCore 2 ↥K))
    (hL : LieZCentList (↥K ⧸ CFSG.pCore 2 ↥K))
    (h3 : (K.subgroupOf (Subgroup.centralizer ({S.v12} : Set G))).Normal ∨
      3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K))
    (hinner : Ch1.InducesInner S.z K) : False := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  obtain ⟨X, Q, y, hyLv, hconf⟩ := S.exists_conf1366_Lv_F4 h1222 h517 h37 h38 hK hinner
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hK.1)).1 hK.2.1
  have hyodd : Odd (orderOf y) := hconf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine not_conf1366_of_lie_inner hEven hF1 hqs hZ hSQ hL (fun hyN => ?_) hconf
  by_cases hn : (K.subgroupOf Gv).Normal
  · have hGvN : Gv ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK.1).mp hn
    have hTN : S.Tv ≤ Subgroup.normalizer (K : Set G) := fun t ht =>
      hGvN (Subgroup.mem_inf.mp ht).2
    by_cases hr : CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≤ 1
    · exact S.inner_of_comm_inner (MulEquiv.refl _) (hF2 _ hSQ hr) hTN hyLv hyodd hyN
    · push Not at hr
      have h3' := ConfAB.three_dvd_card_of_pRank hr
      rcases S.inner_or_case2 hF318 h36 h38 hK hq hZ h3' hr hyLv hyN with h | h2
      · exact h
      · exact S.inner_of_case2_F4 h1222 h517 hF3 hF6 hEven h38 hK hq hZ h3' hr hSQ hyLv hconf h2 hyN
  · exact S.inner_of_not_normal h122 h37 h38 hK hn (h3.resolve_left hn) (MulEquiv.refl _) hyLv
      hyodd hyN

end Setting

end CFSG.Quasithin.H13.A5
