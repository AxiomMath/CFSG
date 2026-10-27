module

public import CFSG.Quasithin.H13.U3L139S
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6HatPlusB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Producer134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L139

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem stmt13_3_9_of_F4 (h1332 : Stmt13_3_2_F4) (h1226 : Stmt12_2_6_F4) (h1228 : Stmt12_2_8_F4)
    (h1338 : A6.Stmt13_3_8_F4) (hL1 : Stmt13_2_2_9L1_F4) : A6.Stmt13_3_9_F4 := by
  intro G _ _ T L V H Y v hH hV hA6 hHin hHM hY2 hYH hHY hv hvL hYv
  by_cases hZV : V ⊓ centralizer (L : Set G) = ⊥
  ·
    obtain ⟨h5, ⟨hTL, -, -, -⟩, -, -⟩ := h1332 G T L hH L hH.faithful
    have hLV : L ≤ normalizer (V : Set G) := hV.2.2.1
    have hO : pCoreOf 2 L ≤ centralizer (V : Set G) := by
      refine (pCoreOf_le_pCoreOf_sup hTL).trans ?_
      intro k hk
      exact mem_centralizer_iff.2 fun w hw =>
        ((mem_reducedAggregate' (hV.1 hw)).2.1 k hk).symm
    obtain ⟨S⟩ := exists_setting4_of_1332_F4 h1332 hH (a6CentralQuotient_of_isA6On hLV hO h5 hA6)
      hV hZV
    have hv1 : v ≠ 1 := fun h => hvL (h ▸ one_mem _)
    have hvz : v = S.z := (S.mem_V1_iff.1 hv).resolve_left hv1
    refine (stmt13_3_9_core_F4 h1332 h1226 h1228 h1338 hL1 hH hV hA6 hHin hHM hY2 hYH hHY hv hvL
      hYv (frame139OfSetting4 S) fun y hy _ => ?_).imp_right fun h => ⟨h.1, h.2.1, h.2.2.1⟩
    rw [S.normalizer_V1, ← hvz]
    exact (hYv hy).2
  ·
    obtain ⟨S⟩ := exists_setting134_F4 h1332 hH hV hZV
    exact (stmt13_3_9_core_F4 h1332 h1226 h1228 h1338 hL1 hH hV hA6 hHin hHM hY2 hYH hHY hv hvL
      hYv (frame139OfSetting134 S) fun y hy hyN =>
        s134_mem_normalizer_V1 S hv hvL hyN (hYv hy).2).imp_right fun h => ⟨h.1, h.2.1, h.2.2.1⟩

end CFSG.Quasithin.H13.U3
