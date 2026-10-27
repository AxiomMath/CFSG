
module

public import CFSG.Certificates.Kernel.Th.Spec.Ts2313Base

public import CFSG.Certificates.Kernel.Th.Spec.Word

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.Gen CFSG.KC.Th.BigS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier CFSG.KC.Th.Spec.Mir

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (K : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)

end Consts

section Ts

variable {D : TsData} (L : TsLeaves D) {RA RB : Array V4} (hA : WfRows RA) (hB : WfRows RB)
  (hSA : pkMat D.ThSeed_SA = rowsMatrix RA) (hSB : pkMat D.ThSeed_SB = rowsMatrix RB)

include L hSB in
theorem pk_ts0 : pkMat (D.ThTs_RB 0) = rowsMatrix RB * rowsMatrix RB := by
  rw [L.ts_0, pkMat_mulB L.c4, hSB]

include L in
theorem lay_ts1 : InLayout (D.ThTs_RB 1) := by
  rw [L.ts_1]; exact inLayout_wordAB L.c4 _ _ _ _ _

include L in
theorem lay_ts2 : InLayout (D.ThTs_RB 2) := by
  rw [L.ts_2]; exact inLayout_wordAB L.c4 _ _ _ _ _

include L hA hB hSA hSB in
theorem ts_lx : WfRows (lx RA RB) ∧ rowsMatrix (lx RA RB) = pkMat (D.ThTs_RB 1) := by
  refine ⟨wfRows_signedRows fun l _ => wfRows_lett3 hA hB l, ?_⟩
  rw [L.ts_1]
  exact wordAB_matrix_eq L.c4 _ _ hSA hSB (pk_ts0 L hSB) _ _ (fun l _ => rowsMatrix_lett3 RA RB l)
    (by decide +kernel)

include L hA hB hSA hSB in
theorem ts_ly : WfRows (ly RA RB) ∧ rowsMatrix (ly RA RB) = pkMat (D.ThTs_RB 2) := by
  refine ⟨wfRows_signedRows fun l _ => wfRows_lett3 hA hB l, ?_⟩
  rw [L.ts_2]
  exact wordAB_matrix_eq L.c4 _ _ hSA hSB (pk_ts0 L hSB) _ _ (fun l _ => rowsMatrix_lett3 RA RB l)
    (by decide +kernel)

include L hA hB hSA hSB in
theorem ts_ly2 : WfRows (Native.mulRows (ly RA RB) (ly RA RB)) ∧
    rowsMatrix (Native.mulRows (ly RA RB) (ly RA RB)) = pkMat (D.ThTs_RB 3) := by
  have h := ts_ly L hA hB hSA hSB
  exact ⟨h.1.mulRows h.1, by rw [rowsMatrix_mulRows, h.2, L.ts_3, pkMat_mulB L.c4]⟩

include L hA hB hSA hSB in
theorem concl2313_of_facts {rows : String} {px py tp tpa tla : Array ℕ}
    (hrows : hexsOf rows = (List.range 2457).map D.ThTs_ROWS)
    (hpx : px = ((List.range 2457).map D.ThTs_PX).toArray)
    (hpy : py = ((List.range 2457).map D.ThTs_PY).toArray)
    (htp : tp = ((List.range 2457).map D.ThTs_TP).toArray)
    (htpa : tpa = ((List.range 2457).map D.ThTs_TPA).toArray)
    (htla : tla = ((List.range 2457).map D.ThTs_TLA).toArray)
    (hdist : ∀ i < 2457, ∀ j < 2457, i < j → D.ThTs_ROWS i ≠ D.ThTs_ROWS j)
    (hperm : ∀ i < 2457, TsS.permOK D.ThTs_ROWS D.ThTs_PX D.ThTs_PY D.ThS_rm (D.ThTs_RB 1)
      (D.ThTs_RB 3) 2457 i = true)
    (hinv : ∀ i < 2457, TsS.invOK D.ThTs_TP D.ThTs_INV 2457 i = true)
    (htree : ∀ i < 2457, TsS.treeOK D.ThTs_TP D.ThTs_TPA D.ThTs_TLA D.ThTs_PX D.ThTs_PY 2457 i =
      true) :
    ((∀ i < 2457, ∀ j < 2457, i < j → (hexsOf rows).getD i 0 ≠ (hexsOf rows).getD j 0) ∧
        (hexsOf rows).getD 0 0 = 0x6accc40834b0cc5bb7315609695cfa8d6f195e2ac39c3b4260e97d31187fa2 ∧
        (∀ i < 2457, px[i]! < 2457 ∧ py[i]! < 2457 ∧
          (frApply (frTable (lx RA RB)) (v4OfNat ((hexsOf rows).getD i 0))).beq
            (v4OfNat ((hexsOf rows).getD px[i]! 0)) = true ∧
          (frApply (frTable (Native.mulRows (ly RA RB) (ly RA RB)))
            (v4OfNat ((hexsOf rows).getD i 0))).beq
            (v4OfNat ((hexsOf rows).getD py[i]! 0)) = true)) ∧
      (tp[0]! = 0 ∧ (∀ k < 2457, tp[k]! < 2457) ∧ (∀ i < 2457, ∃ k < 2457, tp[k]! = i) ∧
        (∀ k < 2457, 1 ≤ k → tpa[k]! < k ∧
          ((tla[k]! = 1 ∧ px[tp[tpa[k]!]!]! = tp[k]!) ∨
           (tla[k]! = 2 ∧ py[tp[tpa[k]!]!]! = tp[k]!)))) ∧
      (eqRows (Native.mulRows (lx RA RB) (lx RA RB)) idRows = true ∧
        eqRows (lx RA RB) idRows = false ∧
        eqRows (Native.mulRows (Native.mulRows (ly RA RB) (ly RA RB)) (ly RA RB)) idRows = true ∧
        eqRows (ly RA RB) idRows = false ∧
        eqRows (powRows (Native.mulRows (lx RA RB) (ly RA RB)) 21) idRows = true ∧
        eqRows (powRows (Native.mulRows (lx RA RB) (ly RA RB)) 3) idRows = false ∧
        eqRows (powRows (Native.mulRows (lx RA RB) (ly RA RB)) 7) idRows = false ∧
        imageKey (frTable (lx RA RB)) wKeyRow = wKeyRow ∧
        imageKey (frTable (Native.mulRows (ly RA RB) (ly RA RB))) wKeyRow = wKeyRow) := by
  obtain ⟨hlxG, hlx⟩ := ts_lx L hA hB hSA hSB
  obtain ⟨hlyG, hly⟩ := ts_ly L hA hB hSA hSB
  obtain ⟨hly2G, hly2⟩ := ts_ly2 L hA hB hSA hSB
  have hid : rowsMatrix (idRows : Array V4) = 1 := rowsMatrix_idRows
  have hxy : WfRows (Native.mulRows (lx RA RB) (ly RA RB)) := hlxG.mulRows hlyG
  have hxyM : rowsMatrix (Native.mulRows (lx RA RB) (ly RA RB)) =
      pkMat (D.ThTs_RB 1) * pkMat (D.ThTs_RB 2) := by rw [rowsMatrix_mulRows, hlx, hly]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    rw [hrows, getD_map_range hi, getD_map_range hj]
    exact hdist i hi j hj hij
  · rw [hrows, getD_map_range (by norm_num)]
    exact L.c611
  · intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := permOK_spec (hperm i hi)
    rw [hpx, hpy, getElem!_toArray_map_range hi, getElem!_toArray_map_range hi, hrows,
      getD_map_range hi, getD_map_range h1, getD_map_range h2]
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [frApply_frTable_v4OfNat L.c4 hlxG hlx, h3]
      exact V4.beq_iff.2 rfl
    · rw [frApply_frTable_v4OfNat L.c4 hly2G hly2, h4]
      exact V4.beq_iff.2 rfl
  · rw [htp, getElem!_toArray_map_range (by norm_num)]
    exact L.c612
  · intro k hk
    rw [htp, getElem!_toArray_map_range hk]
    exact (treeOK_spec (htree k hk)).1
  · intro i hi
    obtain ⟨h1, h2⟩ := invOK_spec (hinv i hi)
    refine ⟨D.ThTs_INV i, h1, ?_⟩
    rw [htp, getElem!_toArray_map_range h1]
    exact h2
  · intro k hk hk1
    obtain ⟨h1, h2⟩ := treeOK_spec (htree k hk)
    have hk0 : k ≠ 0 := by omega
    rcases h2 with h2 | ⟨h3, h4⟩
    · exact absurd h2 hk0
    · have hp : D.ThTs_TP (D.ThTs_TPA k) < 2457 := (treeOK_spec (htree _ (by omega))).1
      rw [htpa, htla, htp, hpx, hpy, getElem!_toArray_map_range hk,
        getElem!_toArray_map_range hk, getElem!_toArray_map_range hk,
        getElem!_toArray_map_range (by omega : D.ThTs_TPA k < 2457),
        getElem!_toArray_map_range hp, getElem!_toArray_map_range hp]
      exact ⟨h3, h4⟩
  ·
    refine eqRows_of_rowsMatrix_eq (hlxG.mulRows hlxG) wfRows_idRows ?_
    rw [rowsMatrix_mulRows, hlx, hid, ← pkMat_mulB L.c4, L.c613, pkMat_one L.c4]
  · refine eqRows_eq_false_of_matrix ?_
    rw [hlx, hid]
    intro h
    exact L.c614 (pkMat_inj (lay_ts1 L) (inLayout_one L.c4) (h.trans (pkMat_one L.c4).symm))
  · refine eqRows_of_rowsMatrix_eq ((hlyG.mulRows hlyG).mulRows hlyG) wfRows_idRows ?_
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, hly, hid, ← pkMat_mulB L.c4, ← pkMat_mulB L.c4,
      L.c615, pkMat_one L.c4]
  · refine eqRows_eq_false_of_matrix ?_
    rw [hly, hid]
    intro h
    exact L.c616 (pkMat_inj (lay_ts2 L) (inLayout_one L.c4) (h.trans (pkMat_one L.c4).symm))
  · refine eqRows_of_rowsMatrix_eq (hxy.powRows 21) wfRows_idRows ?_
    rw [rowsMatrix_powRows, hxyM, hid, ← pkMat_mulB L.c4, ← pkMat_powB L.c4 _ 21 5 (by norm_num),
      L.c617, pkMat_one L.c4]
  · refine eqRows_eq_false_of_matrix ?_
    rw [rowsMatrix_powRows, hxyM, hid, ← pkMat_mulB L.c4, ← pkMat_powB L.c4 _ 3 2 (by norm_num)]
    intro h
    exact L.c618 (pkMat_inj (inLayout_powB L.c4 _ _ _) (inLayout_one L.c4)
      (h.trans (pkMat_one L.c4).symm))
  · refine eqRows_eq_false_of_matrix ?_
    rw [rowsMatrix_powRows, hxyM, hid, ← pkMat_mulB L.c4, ← pkMat_powB L.c4 _ 7 3 (by norm_num)]
    intro h
    exact L.c619 (pkMat_inj (inLayout_powB L.c4 _ _ _) (inLayout_one L.c4)
      (h.trans (pkMat_one L.c4).symm))
  · exact imageKey_wKeyRow L.c4 hlxG hlx L.c620
  · exact imageKey_wKeyRow L.c4 hly2G hly2 L.c621

end Ts

end CFSG.KC.Th.Spec

end
