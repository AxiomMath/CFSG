module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem12Inputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem12Stmt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

open Lem12

theorem stmt12_2_12_one_F4 (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (hH : Hyp1223 G T L V) {v : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) (hTv : IsSylowTwoOf (hH.Tv v) (hH.Mv v))
    (hO2 : pCoreOf 2 (autOn (hH.Lv v ⊔ hH.Tv v) V) = ⊥) :
    hH.Q = pCoreOf 2 (hH.Lv v ⊔ hH.Tv v) ∧
      IsSylowTwoOf hH.Q (centralizerSection (hH.Gv v) (hH.Lv v) (pCoreOf 2 (hH.Lv v))) ∧
      HypC23 (hH.Gv v) hH.Q (hH.Mv v) := by
  obtain ⟨hLvMv, hMvN, -, hcgs, hMvMV⟩ := stmt12_2_5_of_F4 h1222 h323 G T L V hH v hv hv1
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, -, -, -, -⟩ := hall V hH.irrPlus

  have hQ : hH.Q = T ⊓ Subgroup.centralizer (V : Set G) := by
    have := (h3228 G T L V hH.fsu).2.2
    rwa [hH.conjClosure_eq, conjClosure_eq_self_of_normalizes hTV] at this
  have hQ2 : IsPGroup 2 ↥hH.Q := pCoreOf_isPGroup 2 _
  have hQ1 : hH.Q ≠ ⊥ := hH.maximal.1.2.2.2
  have hQTv : hH.Q ≤ hH.Tv v := by
    rw [hQ]
    exact inf_le_inf_left _
      (Subgroup.centralizer_le (t := (V : Set G)) (Set.singleton_subset_iff.mpr hv))
  have hLTv : hH.Lv v ⊔ hH.Tv v ≤ L ⊔ T :=
    sup_le_sup ((oTwoUpper_le _).trans inf_le_left) inf_le_left
  have hVN : hH.Lv v ⊔ hH.Tv v ≤ Subgroup.normalizer (V : Set G) :=
    (sup_le hLvMv hTv.1).trans (hMvMV.trans inf_le_right)

  have hR : hH.Q = pCoreOf 2 (hH.Lv v ⊔ hH.Tv v) := by
    refine le_antisymm ?_ ?_
    · exact le_pCoreOf_of_le_normalizer 2 (hQTv.trans le_sup_right)
        (hLTv.trans (le_normalizer_pCoreOf 2 (L ⊔ T))) hQ2
    · rw [hQ]
      refine le_inf ?_ (pCoreOf_le_centralizer_of_autOn hVN hO2)
      have hsyl : IsSylowTwoOf (hH.Tv v) (hH.Lv v ⊔ hH.Tv v) :=
        A4.isSylowTwoOf_mono hTv le_sup_right (sup_le hLvMv hTv.1)
      exact (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans inf_le_left

  have hNR : hH.Gv v ⊓ Subgroup.normalizer (hH.Q : Set G) ≤ hH.Mv v :=
    (inf_normalizer_le_cgsIn hQ1).trans hcgs
  have hXN : ((hH.Lv v).subgroupOf (hH.Mv v)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLvMv).mpr hMvN
  obtain ⟨hsylK, hO2Q, -, hsylcc⟩ := a4_2_7_rel (oTwoUpper_oTwoUpper _).symm hLvMv hXN
    inf_le_right hTv hR hNR

  have hGv1 : pCoreOf 2 (hH.Gv v) ≠ ⊥ := pCoreOf_centralizer_ne_bot hH.sylow.1 (hVT hv) hv1
    (Lem5.centralizer_le_normalizer_zpowers v)
  refine ⟨hR, hsylK, ?_⟩
  exact { sqtk := sqtkGroup_of_pCoreOf_ne_bot hH.qtke hH.simple hH.nonabelian hGv1
          radical := ⟨hQTv.trans inf_le_right, hQ1, hO2Q⟩
          le := inf_le_right
          cgs := hcgs
          sylow := hsylcc }

theorem stmt12_2_12_two_F4 (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (hcomp : Lem12212Comp_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
    (hH : Hyp1223 G T L V) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hTv : IsSylowTwoOf (hH.Tv v) (hH.Mv v))
    (hO2 : pCoreOf 2 (autOn (hH.Lv v ⊔ hH.Tv v) V) = ⊥)
    (hperf : autOn (hH.Lv v) V = perfectCore (autOn (hH.Lv v) V)) (hVL : V = ⁅V, hH.Lv v⁆) :
    HypC28 (hH.Gv v) hH.Q (hH.Mv v) (perfectCore (hH.Lv v)) V := by
  obtain ⟨hLvMv, hMvN, hMvC2, hcgs, hMvMV⟩ := stmt12_2_5_of_F4 h1222 h323 G T L V hH v hv hv1
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, -, -, hab, -⟩ := hall V hH.irrPlus
  obtain ⟨-, -, hC23⟩ := stmt12_2_12_one_F4 h1222 h323 h3228 hH hv hv1 hTv hO2

  have hQ : hH.Q = T ⊓ Subgroup.centralizer (V : Set G) := by
    have := (h3228 G T L V hH.fsu).2.2
    rwa [hH.conjClosure_eq, conjClosure_eq_self_of_normalizes hTV] at this
  have hQV : hH.Q ≤ Subgroup.centralizer (V : Set G) := by rw [hQ]; exact inf_le_right
  have hQTv : hH.Q ≤ hH.Tv v := by
    rw [hQ]
    exact inf_le_inf_left _
      (Subgroup.centralizer_le (t := (V : Set G)) (Set.singleton_subset_iff.mpr hv))

  have hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by
    obtain ⟨⟨-, -, hred, -⟩, -⟩ := hall V hH.irrPlus
    have := hred.2.1
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨x, (hVT.trans le_sup_right) hx⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hx)
    simpa using congrArg Subtype.val h2
  have hVTv : V ≤ hH.Tv v :=
    le_inf hVT fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hc x hx v hv)

  have hMvNV : hH.Mv v ≤ Subgroup.normalizer (V : Set G) := hMvMV.trans inf_le_right
  have hLvNV : hH.Lv v ≤ Subgroup.normalizer (V : Set G) := hLvMv.trans hMvNV
  have hTvNV : hH.Tv v ≤ Subgroup.normalizer (V : Set G) := hTv.1.trans hMvNV
  have hL'Lv : perfectCore (hH.Lv v) ≤ hH.Lv v := perfectCore_le _
  have hL'NV : perfectCore (hH.Lv v) ≤ Subgroup.normalizer (V : Set G) := hL'Lv.trans hLvNV
  have hMvL' : hH.Mv v ≤ Subgroup.normalizer (perfectCore (hH.Lv v) : Set G) :=
    hMvN.trans (normalizer_le_normalizer_perfectCore _)
  have hL'Mv : perfectCore (hH.Lv v) ≤ hH.Mv v := hL'Lv.trans hLvMv
  have hcc : conjClosure (perfectCore (hH.Lv v)) (hH.Mv v) = perfectCore (hH.Lv v) :=
    conjClosure_eq_self_of_normalizes hMvL'
  have haut : autOn (perfectCore (hH.Lv v)) V = autOn (hH.Lv v) V := by
    rw [autOn_perfectCore_eq hLvNV]
    exact hperf.symm
  have hcomm' : ⁅V, perfectCore (hH.Lv v)⁆ = V := by
    rw [commutator_eq_of_autOn_eq hL'NV hLvNV haut]
    exact hVL.symm
  have hVL' : V ≤ perfectCore (hH.Lv v) := by
    calc V = ⁅V, perfectCore (hH.Lv v)⁆ := hcomm'.symm
      _ ≤ perfectCore (hH.Lv v) :=
        commutator_le_of_le_normalizer ((hVTv.trans hTv.1).trans hMvL')

  have hR' : hH.Q = pCoreOf 2 (perfectCore (hH.Lv v) ⊔ hH.Tv v) := by
    refine le_antisymm ?_ ?_
    · refine le_pCoreOf_of_le_normalizer 2 (hQTv.trans le_sup_right) ?_ (pCoreOf_isPGroup 2 _)
      exact (sup_le_sup (hL'Lv.trans ((oTwoUpper_le _).trans inf_le_left)) inf_le_left).trans
        (le_normalizer_pCoreOf 2 (L ⊔ T))
    · rw [hQ]
      have hNV' : perfectCore (hH.Lv v) ⊔ hH.Tv v ≤ Subgroup.normalizer (V : Set G) :=
        sup_le hL'NV hTvNV
      have hO2' : pCoreOf 2 (autOn (perfectCore (hH.Lv v) ⊔ hH.Tv v) V) = ⊥ := by
        rw [autOn_sup_eq_sup_autOn hL'NV hTvNV, haut, ← autOn_sup_eq_sup_autOn hLvNV hTvNV]
        exact hO2
      refine le_inf ?_ (pCoreOf_le_centralizer_of_autOn hNV' hO2')
      have hsyl : IsSylowTwoOf (hH.Tv v) (perfectCore (hH.Lv v) ⊔ hH.Tv v) :=
        A4.isSylowTwoOf_mono hTv le_sup_right (sup_le hL'Mv hTv.1)
      exact (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans inf_le_left
  have hXN : ((perfectCore (hH.Lv v)).subgroupOf (hH.Mv v)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL'Mv).mpr hMvL'
  obtain ⟨-, -, hsylM, -⟩ := a4_2_7_rel (eq_oTwoUpper_of_perfect (perfectCore_perfect _)) hL'Mv
    hXN le_rfl hTv hR' inf_le_left

  have hQNV : hH.Q ≤ Subgroup.normalizer (V : Set G) := hQTv.trans hTvNV
  have hLQ : perfectCore (hH.Lv v) ⊔ hH.Q ≤ Subgroup.normalizer (V : Set G) := sup_le hL'NV hQNV
  have hautLQ : autOn (perfectCore (hH.Lv v) ⊔ hH.Q) V = autOn (hH.Lv v) V := by
    rw [autOn_sup_eq_sup_autOn hL'NV hQNV, haut, autOn_eq_bot_of_le_centralizer hQV, sup_bot_eq]
  have hO2Lv : pCoreOf 2 (autOn (hH.Lv v) V) = ⊥ := by
    rw [eq_bot_iff, ← hO2]
    refine pCoreOf_le_pCoreOf_of_normal (A4.autOn_mono le_sup_left) ?_
    rw [autOn_sup_eq_sup_autOn hLvNV hTvNV]
    exact sup_le Subgroup.le_normalizer
      (autOn_le_normalizer_autOn hLvNV hTvNV (hTv.1.trans hMvN))
  have hPV : pCoreOf 2 (perfectCore (hH.Lv v) ⊔ hH.Q) ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_autOn hLQ (by rw [hautLQ]; exact hO2Lv)
  have hVP : V ≤ pCoreOf 2 (perfectCore (hH.Lv v) ⊔ hH.Q) :=
    le_pCoreOf_of_le_normalizer 2 (hVL'.trans le_sup_left) hLQ (hH.sylow.1.to_le hVT)

  have hNVM : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have h := (stmt12_2_6_of_F4 h1222 h323 G T L V hH).2 V (Subgroup.normalizer (V : Set G))
      hH.irrPlus.2.1 le_rfl le_rfl
    intro x hx
    have hx' : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (V : Set G) := ⟨hx, hx⟩
    rw [← h] at hx'
    exact hx'.2
  exact { sqtk := hC23.sqtk
          pgroup := pCoreOf_isPGroup 2 _
          le_M := hQTv.trans hTv.1
          le_H := inf_le_right
          charTwo := hMvC2
          pCore_ne := pCoreOf_centralizer_ne_bot hH.sylow.1 (hVT hv) hv1
            (Lem5.centralizer_le_normalizer_zpowers v)
          comp := hcomp G T L V hH v hv hv1 hTv hO2 hperf hVL
          sylow := by rw [hcc]; exact hsylM
          cgs := hcgs
          V_le := by rw [hcc]; exact hVL'
          V_ne := hH.irrPlus.2.1
          V_elem := ⟨hab, hV2⟩
          V_comm := by rw [hcc]; exact hcomm'
          V_center := by
            rw [hcc]
            exact le_inf hVP (Subgroup.le_centralizer_iff.mp hPV)
          V_norm := fun x hx => ⟨hNVM hx.2, hx.1⟩ }

theorem stmt12_2_12_of_inputs_F4 (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (hcomp : Lem12212Comp_F4) : Stmt12_2_12_F4 := by
  intro G _ _ T L V hH v hv hv1 hTv hO2
  exact ⟨stmt12_2_12_one_F4 h1222 h323 h3228 hH hv hv1 hTv hO2,
    fun hperf hVL => stmt12_2_12_two_F4 h1222 h323 h3228 hcomp hH hv hv1 hTv hO2 hperf hVL⟩

end CFSG.Quasithin.H13
