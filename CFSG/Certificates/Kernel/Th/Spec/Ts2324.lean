
module

public import CFSG.Certificates.Kernel.Th.Spec.Ts2324Base

public import CFSG.Certificates.Kernel.Th.Spec.Ts2313
public import CFSG.Certificates.Kernel.Th.Spec.Gj
public import CFSG.Certificates.Kernel.Th.Spec.Mirror

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.Gen CFSG.KC.Th.BigS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier CFSG.KC.Th.Spec.Mir

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (K : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)

end Consts

theorem rowsMatrix_zWord (rx ry : Array V4) :
    rowsMatrix (wordRows rx ry zWord) =
      rowsMatrix rx * (rowsMatrix ry * (rowsMatrix ry * rowsMatrix ry)) := by
  rw [rowsMatrix_wordRows]
  show (_ : Matrix (Fin 248) (Fin 248) (ZMod 2)) * (_ * (_ * (_ * 1))) = _
  rw [mul_one]
  rfl

section Ts

variable {D : TsData} (L : TsLeaves D) {RA RB : Array V4} (hA : WfRows RA) (hB : WfRows RB)
  (hSA : pkMat D.ThSeed_SA = rowsMatrix RA) (hSB : pkMat D.ThSeed_SB = rowsMatrix RB)

include L hA hB hSA hSB in
theorem ts_hR (w : List ℤ) (code n : ℕ)
    (hcodes : w.map wordCode = (List.range n).map fun i => bitsN code (2 * i) 2) :
    WfRows (hR RA RB w) ∧ rowsMatrix (hR RA RB w) =
      pkMat (wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThTs_RB 1) (D.ThTs_RB 2) (D.ThTs_RB 3) code
        n) := by
  obtain ⟨hlxG, hlx⟩ := ts_lx L hA hB hSA hSB
  obtain ⟨hlyG, hly⟩ := ts_ly L hA hB hSA hSB
  obtain ⟨hly2G, hly2⟩ := ts_ly2 L hA hB hSA hSB
  refine ⟨wfRows_signedRows fun l _ => wfRows_lett3 hlxG hlyG l, ?_⟩
  refine wordAB_matrix_eq L.c4 code n hlx.symm hly.symm ?_ (lett3 (lx RA RB) (ly RA RB)) w
    (fun l _ => rowsMatrix_lett3 _ _ l) hcodes
  rw [← hly2, rowsMatrix_mulRows]

include L hA hB hSA hSB in
theorem ts_h0 : WfRows (hR RA RB centWord0) ∧
    rowsMatrix (hR RA RB centWord0) = pkMat (D.ThTs_RB 4) := by
  rw [L.ts_4]
  exact ts_hR L hA hB hSA hSB centWord0 71641224 15 (by decide +kernel)

include L hA hB hSA hSB in
theorem ts_h1 : WfRows (hR RA RB centWord1) ∧
    rowsMatrix (hR RA RB centWord1) = pkMat (D.ThTs_RB 5) := by
  rw [L.ts_5]
  exact ts_hR L hA hB hSA hSB centWord1 74159786122 20 (by decide +kernel)

include L hA hB hSA hSB in
theorem ts_hk : WfRows (hR RA RB kWord) ∧ rowsMatrix (hR RA RB kWord) = pkMat (D.ThTs_RB 6) := by
  rw [L.ts_6]
  exact ts_hR L hA hB hSA hSB kWord 69 4 (by decide +kernel)

include L hA hB hSA hSB in
theorem ts_hki : WfRows (hR RA RB (invWord kWord)) ∧
    rowsMatrix (hR RA RB (invWord kWord)) = pkMat (D.ThTs_RB 7) := by
  rw [L.ts_7]
  exact ts_hR L hA hB hSA hSB (invWord kWord) 162 4 (by decide +kernel)

include L hA hB hSA hSB in
theorem ts_rv : WfRows (rv RA RB) ∧ rowsMatrix (rv RA RB) = pkMat (D.ThTs_RB 26) := by
  refine ⟨wfRows_signedRows fun l _ => wfRows_lett3 hA hB l, ?_⟩
  rw [L.ts_26]
  exact wordAB_matrix_eq L.c4 _ _ hSA hSB (pk_ts0 L hSB) _ _ (fun l _ => rowsMatrix_lett3 RA RB l)
    (by decide +kernel)

include L hA hB hSA hSB in
theorem ts_rvi : WfRows (rvi RA RB) ∧ rowsMatrix (rvi RA RB) = pkMat (D.ThTs_RB 27) := by
  refine ⟨wfRows_signedRows fun l _ => wfRows_lett3 hA hB l, ?_⟩
  rw [L.ts_27]
  exact wordAB_matrix_eq L.c4 _ _ hSA hSB (pk_ts0 L hSB) _ _ (fun l _ => rowsMatrix_lett3 RA RB l)
    (by decide +kernel)

include L hA hB hSA hSB in
theorem ts_rT : WfRows (rT RA RB) ∧ rowsMatrix (rT RA RB) = pkMat (D.ThTs_RB 28) := by
  obtain ⟨hv, hvM⟩ := ts_rv L hA hB hSA hSB
  obtain ⟨hvi, hviM⟩ := ts_rvi L hA hB hSA hSB
  refine ⟨(hvi.mulRows hA).mulRows hv, ?_⟩
  rw [rT, rowsMatrix_mulRows, rowsMatrix_mulRows, hvM, hviM, ← hSA, L.ts_28, pkMat_mulB L.c4,
    pkMat_mulB L.c4]

include L hA hB hSA hSB in
theorem ts_e3 : WfRows (Native.mulRows (Native.mulRows (hR RA RB kWord) (hR RA RB centWord0))
      (hR RA RB (invWord kWord))) ∧
    rowsMatrix (Native.mulRows (Native.mulRows (hR RA RB kWord) (hR RA RB centWord0))
      (hR RA RB (invWord kWord))) = pkMat (D.ThTs_RB 8) := by
  obtain ⟨h0, h0M⟩ := ts_h0 L hA hB hSA hSB
  obtain ⟨hk, hkM⟩ := ts_hk L hA hB hSA hSB
  obtain ⟨hki, hkiM⟩ := ts_hki L hA hB hSA hSB
  refine ⟨(hk.mulRows h0).mulRows hki, ?_⟩
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, hkM, h0M, hkiM, L.ts_8, pkMat_mulB L.c4,
    pkMat_mulB L.c4]

include L hA hB hSA hSB in
theorem ts_e4 : WfRows (Native.mulRows (Native.mulRows (hR RA RB kWord) (hR RA RB centWord1))
      (hR RA RB (invWord kWord))) ∧
    rowsMatrix (Native.mulRows (Native.mulRows (hR RA RB kWord) (hR RA RB centWord1))
      (hR RA RB (invWord kWord))) = pkMat (D.ThTs_RB 9) := by
  obtain ⟨h1, h1M⟩ := ts_h1 L hA hB hSA hSB
  obtain ⟨hk, hkM⟩ := ts_hk L hA hB hSA hSB
  obtain ⟨hki, hkiM⟩ := ts_hki L hA hB hSA hSB
  refine ⟨(hk.mulRows h1).mulRows hki, ?_⟩
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, hkM, h1M, hkiM, L.ts_9, pkMat_mulB L.c4,
    pkMat_mulB L.c4]

include L hA hB hSA hSB in
theorem ts_rG : WfRows (rG RA RB) ∧ rowsMatrix (rG RA RB) = pkMat (D.ThTs_RB 29) := by
  obtain ⟨hv, hvM⟩ := ts_rv L hA hB hSA hSB
  obtain ⟨hvi, hviM⟩ := ts_rvi L hA hB hSA hSB
  obtain ⟨hk, hkM⟩ := ts_hk L hA hB hSA hSB
  refine ⟨(hv.mulRows hk).mulRows hvi, ?_⟩
  rw [rG, rowsMatrix_mulRows, rowsMatrix_mulRows, hvM, hkM, hviM, L.ts_29, pkMat_mulB L.c4,
    pkMat_mulB L.c4]

include L hA hB hSA hSB in
theorem ts_rGi : WfRows (rGi RA RB) ∧ rowsMatrix (rGi RA RB) = pkMat (D.ThTs_RB 30) := by
  obtain ⟨hv, hvM⟩ := ts_rv L hA hB hSA hSB
  obtain ⟨hvi, hviM⟩ := ts_rvi L hA hB hSA hSB
  obtain ⟨hki, hkiM⟩ := ts_hki L hA hB hSA hSB
  refine ⟨(hv.mulRows hki).mulRows hvi, ?_⟩
  rw [rGi, rowsMatrix_mulRows, rowsMatrix_mulRows, hvM, hkiM, hviM, L.ts_30, pkMat_mulB L.c4,
    pkMat_mulB L.c4]

include L hA hB hSA hSB in
theorem ts_rR : WfRows (rR RA RB) ∧ rowsMatrix (rR RA RB) = pkMat (D.ThTs_RB 31) := by
  obtain ⟨hg, hgM⟩ := ts_rG L hA hB hSA hSB
  obtain ⟨hgi, hgiM⟩ := ts_rGi L hA hB hSA hSB
  refine ⟨(hg.mulRows hA).mulRows hgi, ?_⟩
  rw [rR, rowsMatrix_mulRows, rowsMatrix_mulRows, hgM, hgiM, ← hSA, L.ts_31, pkMat_mulB L.c4,
    pkMat_mulB L.c4]

include L hA hB hSA hSB in
theorem m3_regs :
    (WfRows (m3t3 RA RB) ∧ rowsMatrix (m3t3 RA RB) = pkMat (D.ThM3_RB 0)) ∧
    (WfRows (m3t4 RA RB) ∧ rowsMatrix (m3t4 RA RB) = pkMat (D.ThM3_RB 1)) ∧
    (WfRows (m3t5 RA RB) ∧ rowsMatrix (m3t5 RA RB) = pkMat (D.ThM3_RB 2)) ∧
    (WfRows (m3t6 RA RB) ∧ rowsMatrix (m3t6 RA RB) = pkMat (D.ThM3_RB 3)) ∧
    (WfRows (m3t7 RA RB) ∧ rowsMatrix (m3t7 RA RB) = pkMat (D.ThM3_RB 4)) ∧
    (WfRows (m3t8 RA RB) ∧ rowsMatrix (m3t8 RA RB) = pkMat (D.ThM3_RB 5)) ∧
    (WfRows (m3u RA RB) ∧ rowsMatrix (m3u RA RB) = pkMat (D.ThM3_RB 6)) ∧
    (WfRows (m3x RA RB) ∧ rowsMatrix (m3x RA RB) = pkMat (D.ThM3_RB 13)) ∧
    (WfRows (m3y RA RB) ∧ rowsMatrix (m3y RA RB) = pkMat (D.ThM3_RB 14)) ∧
    (WfRows (powRows (m3y RA RB) 5) ∧ rowsMatrix (powRows (m3y RA RB) 5) = pkMat (D.ThM3_RB 15)) ∧
    (WfRows (m3z RA RB) ∧ rowsMatrix (m3z RA RB) = pkMat (D.ThM3_RB 16)) := by
  have h0 : WfRows (m3t3 RA RB) ∧ rowsMatrix (m3t3 RA RB) = pkMat (D.ThM3_RB 0) := by
    refine ⟨hA.mulRows hB, ?_⟩
    rw [m3t3, rowsMatrix_mulRows, L.m3_0, pkMat_mulB L.c4, hSA, hSB]
  obtain ⟨h0G, h0M⟩ := h0
  have h1 : WfRows (m3t4 RA RB) ∧ rowsMatrix (m3t4 RA RB) = pkMat (D.ThM3_RB 1) := by
    refine ⟨h0G.mulRows hB, ?_⟩
    rw [m3t4, rowsMatrix_mulRows, h0M, L.m3_1, pkMat_mulB L.c4, hSB]
  obtain ⟨h1G, h1M⟩ := h1
  have h2 : WfRows (m3t5 RA RB) ∧ rowsMatrix (m3t5 RA RB) = pkMat (D.ThM3_RB 2) := by
    refine ⟨h0G.mulRows h1G, ?_⟩
    rw [m3t5, rowsMatrix_mulRows, h0M, h1M, L.m3_2, pkMat_mulB L.c4]
  obtain ⟨h2G, h2M⟩ := h2
  have h3 : WfRows (m3t6 RA RB) ∧ rowsMatrix (m3t6 RA RB) = pkMat (D.ThM3_RB 3) := by
    refine ⟨h0G.mulRows h2G, ?_⟩
    rw [m3t6, rowsMatrix_mulRows, h0M, h2M, L.m3_3, pkMat_mulB L.c4]
  obtain ⟨h3G, h3M⟩ := h3
  have h4 : WfRows (m3t7 RA RB) ∧ rowsMatrix (m3t7 RA RB) = pkMat (D.ThM3_RB 4) := by
    refine ⟨hA.mulRows h3G, ?_⟩
    rw [m3t7, rowsMatrix_mulRows, h3M, L.m3_4, pkMat_mulB L.c4, hSA]
  obtain ⟨h4G, h4M⟩ := h4
  have h5 : WfRows (m3t8 RA RB) ∧ rowsMatrix (m3t8 RA RB) = pkMat (D.ThM3_RB 5) := by
    refine ⟨h3G.mulRows hA, ?_⟩
    rw [m3t8, rowsMatrix_mulRows, h3M, L.m3_5, pkMat_mulB L.c4, hSA]
  obtain ⟨h5G, h5M⟩ := h5
  have h6 : WfRows (m3u RA RB) ∧ rowsMatrix (m3u RA RB) = pkMat (D.ThM3_RB 6) := by
    refine ⟨(h5G.powRows 2).mulRows h4G, ?_⟩
    rw [m3u, rowsMatrix_mulRows, rowsMatrix_powRows, h5M, h4M, L.m3_6, pkMat_mulB L.c4,
      pkMat_powB L.c4 _ 2 2 (by norm_num)]
  obtain ⟨h6G, h6M⟩ := h6
  have h7 : WfRows (m3s8 RA RB) ∧ rowsMatrix (m3s8 RA RB) = pkMat (D.ThM3_RB 7) := by
    refine ⟨h3G.mulRows h2G, ?_⟩
    rw [m3s8, rowsMatrix_mulRows, h3M, h2M, L.m3_7, pkMat_mulB L.c4]
  obtain ⟨h7G, h7M⟩ := h7
  have h8 : WfRows (m3s9 RA RB) ∧ rowsMatrix (m3s9 RA RB) = pkMat (D.ThM3_RB 8) := by
    refine ⟨h0G.mulRows h7G, ?_⟩
    rw [m3s9, rowsMatrix_mulRows, h0M, h7M, L.m3_8, pkMat_mulB L.c4]
  obtain ⟨h8G, h8M⟩ := h8
  have h9 : WfRows (m3s10 RA RB) ∧ rowsMatrix (m3s10 RA RB) = pkMat (D.ThM3_RB 9) := by
    refine ⟨h8G.mulRows h1G, ?_⟩
    rw [m3s10, rowsMatrix_mulRows, h8M, h1M, L.m3_9, pkMat_mulB L.c4]
  obtain ⟨h9G, h9M⟩ := h9
  have h10 : WfRows (m3s7 RA RB) ∧ rowsMatrix (m3s7 RA RB) = pkMat (D.ThM3_RB 10) := by
    refine ⟨hA.mulRows h9G, ?_⟩
    rw [m3s7, rowsMatrix_mulRows, h9M, L.m3_10, pkMat_mulB L.c4, hSA]
  obtain ⟨h10G, h10M⟩ := h10
  have h11 : WfRows (m3s8' RA RB) ∧ rowsMatrix (m3s8' RA RB) = pkMat (D.ThM3_RB 11) := by
    refine ⟨h9G.mulRows hA, ?_⟩
    rw [m3s8', rowsMatrix_mulRows, h9M, L.m3_11, pkMat_mulB L.c4, hSA]
  obtain ⟨h11G, h11M⟩ := h11
  have h12 : WfRows (m3v RA RB) ∧ rowsMatrix (m3v RA RB) = pkMat (D.ThM3_RB 12) := by
    refine ⟨(h11G.powRows 18).mulRows h10G, ?_⟩
    rw [m3v, rowsMatrix_mulRows, rowsMatrix_powRows, h11M, h10M, L.m3_12, pkMat_mulB L.c4,
      pkMat_powB L.c4 _ 18 5 (by norm_num)]
  obtain ⟨h12G, h12M⟩ := h12
  have h13 : WfRows (m3x RA RB) ∧ rowsMatrix (m3x RA RB) = pkMat (D.ThM3_RB 13) := by
    refine ⟨h12G.powRows 14, ?_⟩
    rw [m3x, rowsMatrix_powRows, h12M, L.m3_13, pkMat_powB L.c4 _ 14 4 (by norm_num)]
  obtain ⟨h13G, h13M⟩ := h13
  have h14 : WfRows (m3y RA RB) ∧ rowsMatrix (m3y RA RB) = pkMat (D.ThM3_RB 14) := by
    refine ⟨h4G.mulRows (h6G.powRows 9), ?_⟩
    rw [m3y, rowsMatrix_mulRows, rowsMatrix_powRows, h4M, h6M, L.m3_14, pkMat_mulB L.c4,
      pkMat_powB L.c4 _ 9 4 (by norm_num)]
  obtain ⟨h14G, h14M⟩ := h14
  have h15 : WfRows (powRows (m3y RA RB) 5) ∧
      rowsMatrix (powRows (m3y RA RB) 5) = pkMat (D.ThM3_RB 15) := by
    refine ⟨h14G.powRows 5, ?_⟩
    rw [rowsMatrix_powRows, h14M, L.m3_15, pkMat_powB L.c4 _ 5 3 (by norm_num)]
  have h16 : WfRows (m3z RA RB) ∧ rowsMatrix (m3z RA RB) = pkMat (D.ThM3_RB 16) := by
    refine ⟨(wfRows_wordRows h13G h14G zWord).powRows zExp, ?_⟩
    rw [m3z, rowsMatrix_powRows, rowsMatrix_zWord, h13M, h14M, L.m3_16,
      pkMat_powB L.c4 _ 9 4 (by norm_num), pk_word84 L.c4]
    rfl
  exact ⟨⟨h0G, h0M⟩, ⟨h1G, h1M⟩, ⟨h2G, h2M⟩, ⟨h3G, h3M⟩, ⟨h4G, h4M⟩, ⟨h5G, h5M⟩, ⟨h6G, h6M⟩,
    ⟨h13G, h13M⟩, ⟨h14G, h14M⟩, h15, h16⟩

include L hA hB hSA hSB in
theorem m3_pW (w : List ℤ) (code n : ℕ) (hl : ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2)
    (hcodes : w.map wordCode = (List.range n).map fun i => bitsN code (2 * i) 2) :
    WfRows (pW RA RB w) ∧ rowsMatrix (pW RA RB w) = pkMat (wordAB D.ThS_c D.ThS_rm D.ThS_ONE
      (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) code n) := by
  obtain ⟨-, -, -, -, -, -, -, ⟨h13G, h13M⟩, ⟨h14G, h14M⟩, ⟨-, h15M⟩, -⟩ :=
    m3_regs L hA hB hSA hSB
  refine ⟨wfRows_signedRows fun l _ => wfRows_pLet h13G h14G l, ?_⟩
  exact wordAB_matrix_eq L.c4 code n rfl rfl rfl (pLet RA RB) w
    (fun l hl' => rowsMatrix_pLet h13M h14M h15M (hl l hl')) hcodes

include L hA hB hSA hSB in
theorem ts_rE217 : WfRows (rE217 RA RB) ∧ rowsMatrix (rE217 RA RB) = pkMat (D.ThTs_RB 32) := by
  obtain ⟨w0G, w0M⟩ := m3_pW L hA hB hSA hSB Packet.coreZWord 1352160579797152663358438253090 52
    (by decide +kernel) (by decide +kernel)
  obtain ⟨w2G, w2M⟩ := m3_pW L hA hB hSA hSB (Packet.coreGeneratorWords 2) 85004562 14
    (by decide +kernel) (by decide +kernel)
  obtain ⟨w3G, w3M⟩ := m3_pW L hA hB hSA hSB (Packet.coreGeneratorWords 3) 340018248 16
    (by decide +kernel) (by decide +kernel)
  obtain ⟨w5G, w5M⟩ := m3_pW L hA hB hSA hSB (Packet.coreGeneratorWords 5) 18539942178 18
    (by decide +kernel) (by decide +kernel)
  obtain ⟨w6G, w6M⟩ := m3_pW L hA hB hSA hSB (Packet.coreGeneratorWords 6) 5655040296 18
    (by decide +kernel) (by decide +kernel)
  refine ⟨(((w0G.mulRows w2G).mulRows w3G).mulRows w5G).mulRows w6G, ?_⟩
  rw [rE217, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, w0M,
    w2M, w3M, w5M, w6M, L.ts_32, pkMat_mulB L.c4, pkMat_mulB L.c4, pkMat_mulB L.c4,
    pkMat_mulB L.c4]

end Ts

theorem TwEntry.of_inv {R : Array V4} {E F : Matrix (Fin 248) (Fin 248) (ZMod 2)} (hR : WfRows R)
    (hE : rowsMatrix R = E) (hEF : E * F = 1) : TwEntry R E F := by
  obtain ⟨h1, h2, -, -⟩ := invRows_spec R hR.1 hR.2 ⟨F, hE ▸ hEF⟩
  exact ⟨hR, hE, ⟨h1, h2⟩, rowsMatrix_invRows_eq R hR.1 hR.2 (hE ▸ hEF)⟩

theorem word_matrix {Rs : List (Array V4)} {n : ℕ} {E F : ℕ → Matrix (Fin 248) (Fin 248) (ZMod 2)}
    (h : TwEnts Rs n E F) {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ n) :
    WfRows (signedRows (tupleRows Rs) w) ∧
      rowsMatrix (signedRows (tupleRows Rs) w) = (w.map (tupM E F)).prod := by
  refine ⟨wfRows_signedRows fun l hl => (tupleRows_spec h (hw l hl).1 (hw l hl).2).1, ?_⟩
  rw [rowsMatrix_signedRows]
  congr 1
  exact List.map_congr_left fun l hl => (tupleRows_spec h (hw l hl).1 (hw l hl).2).2

theorem ents_step {Rs : List (Array V4)} {n : ℕ} {E F : ℕ → Matrix (Fin 248) (Fin 248) (ZMod 2)}
    (h : TwEnts Rs n E F) {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ n)
    (hprod : (w.map (tupM E F)).prod = E n) (hEF : E n * F n = 1) :
    TwEnts (twoRowsStep Rs w) (n + 1) E F := by
  obtain ⟨hG, hM⟩ := word_matrix h hw
  rw [hprod] at hM
  have hlen := h.1
  unfold twoRowsStep
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  by_cases hin : i < n
  · rw [List.getD_append _ _ _ _ (h.1 ▸ hin)]
    exact h.2 i hin
  · have hi' : i = n := by omega
    subst hi'
    rw [List.getD_append_right _ _ _ _ (by omega), h.1, Nat.sub_self]
    exact TwEntry.of_inv hG hM hEF

section Ts

variable {D : TsData} (L : TsLeaves D) {RA RB : Array V4} (hA : WfRows RA) (hB : WfRows RB)
  (hSA : pkMat D.ThSeed_SA = rowsMatrix RA) (hSB : pkMat D.ThSeed_SB = rowsMatrix RB)

include L in
theorem entry_mul_inv (i : ℕ) (hi : i < 10) :
    pkMat (D.ThTs_RB (twRegE i)) * pkMat (D.ThTs_RB (twRegF i)) = 1 := by
  interval_cases i
  · show pkMat (D.ThTs_RB 4) * pkMat (D.ThTs_RB 19) = 1
    rw [← pkMat_mulB L.c4, L.c587, pkMat_one L.c4]
  · show pkMat (D.ThTs_RB 5) * pkMat (D.ThTs_RB 12) = 1
    rw [← pkMat_mulB L.c4, L.c588, pkMat_one L.c4]
  · show pkMat (D.ThTs_RB 8) * pkMat (D.ThTs_RB 20) = 1
    rw [← pkMat_mulB L.c4, L.c589, pkMat_one L.c4]
  · show pkMat (D.ThTs_RB 9) * pkMat (D.ThTs_RB 10) = 1
    rw [← pkMat_mulB L.c4, L.c590, pkMat_one L.c4]
  · show pkMat (D.ThTs_RB 11) * pkMat (D.ThTs_RB 21) = 1
    rw [← pkMat_mulB L.c4, L.c591, pkMat_one L.c4]
  · show pkMat (D.ThTs_RB 13) * pkMat (D.ThTs_RB 22) = 1
    rw [← pkMat_mulB L.c4, L.c592, pkMat_one L.c4]
  · show pkMat (D.ThTs_RB 14) * pkMat (D.ThTs_RB 23) = 1
    rw [← pkMat_mulB L.c4, L.c593, pkMat_one L.c4]
  · show pkMat (D.ThTs_RB 15) * pkMat (D.ThTs_RB 24) = 1
    rw [← pkMat_mulB L.c4, L.c594, pkMat_one L.c4]
  · show pkMat (D.ThTs_RB 16) * pkMat (D.ThTs_RB 17) = 1
    rw [← pkMat_mulB L.c4, L.c595, pkMat_one L.c4]
  · show pkMat (D.ThTs_RB 18) * pkMat (D.ThTs_RB 25) = 1
    rw [← pkMat_mulB L.c4, L.c596, pkMat_one L.c4]

include L in
theorem step_prod0 : (([1, -4, 3, 4, 1] : List ℤ).map
    (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))).prod =
    pkMat (D.ThTs_RB 11) := by
  have e : (([1, -4, 3, 4, 1] : List ℤ).map
      (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))) =
      [pkMat (D.ThTs_RB 4), pkMat (D.ThTs_RB 10), pkMat (D.ThTs_RB 8), pkMat (D.ThTs_RB 9),
       pkMat (D.ThTs_RB 4)] := rfl
  rw [e, prod_cons_foldl, L.ts_11]
  simp only [pkMat_mulB L.c4]
  rfl

include L in
theorem step_prod1 : (([-2, -2, 1, 2, 2] : List ℤ).map
    (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))).prod =
    pkMat (D.ThTs_RB 13) := by
  have e : (([-2, -2, 1, 2, 2] : List ℤ).map
      (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))) =
      [pkMat (D.ThTs_RB 12), pkMat (D.ThTs_RB 12), pkMat (D.ThTs_RB 4), pkMat (D.ThTs_RB 5),
       pkMat (D.ThTs_RB 5)] := rfl
  rw [e, prod_cons_foldl, L.ts_13]
  simp only [pkMat_mulB L.c4]
  rfl

include L in
theorem step_prod2 : (([6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 6] : List ℤ).map
    (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))).prod =
    pkMat (D.ThTs_RB 14) := by
  have e : (([6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 6] : List ℤ).map
      (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))) =
      [pkMat (D.ThTs_RB 13), pkMat (D.ThTs_RB 11), pkMat (D.ThTs_RB 13), pkMat (D.ThTs_RB 11),
       pkMat (D.ThTs_RB 13), pkMat (D.ThTs_RB 11), pkMat (D.ThTs_RB 13), pkMat (D.ThTs_RB 11),
       pkMat (D.ThTs_RB 13), pkMat (D.ThTs_RB 11), pkMat (D.ThTs_RB 13), pkMat (D.ThTs_RB 11),
       pkMat (D.ThTs_RB 13)] := rfl
  rw [e, prod_cons_foldl, L.ts_14]
  simp only [pkMat_mulB L.c4]
  rfl

include L in
theorem step_prod3 : (([-2, -2, 3, 1, 4, 2] : List ℤ).map
    (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))).prod =
    pkMat (D.ThTs_RB 15) := by
  have e : (([-2, -2, 3, 1, 4, 2] : List ℤ).map
      (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))) =
      [pkMat (D.ThTs_RB 12), pkMat (D.ThTs_RB 12), pkMat (D.ThTs_RB 8), pkMat (D.ThTs_RB 4),
       pkMat (D.ThTs_RB 9), pkMat (D.ThTs_RB 5)] := rfl
  rw [e, prod_cons_foldl, L.ts_15]
  simp only [pkMat_mulB L.c4]
  rfl

include L in
theorem step_prod4 : (([8, 8] : List ℤ).map
    (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))).prod =
    pkMat (D.ThTs_RB 16) := by
  have e : (([8, 8] : List ℤ).map
      (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))) =
      [pkMat (D.ThTs_RB 15), pkMat (D.ThTs_RB 15)] := rfl
  rw [e, prod_cons_foldl, L.ts_16]
  simp only [pkMat_mulB L.c4]
  rfl

include L in
theorem step_prod5 : (([7, -9, -9, 7, 9, 9, 7, 9, 7] : List ℤ).map
    (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))).prod =
    pkMat (D.ThTs_RB 18) := by
  have e : (([7, -9, -9, 7, 9, 9, 7, 9, 7] : List ℤ).map
      (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))) =
      [pkMat (D.ThTs_RB 14), pkMat (D.ThTs_RB 17), pkMat (D.ThTs_RB 17), pkMat (D.ThTs_RB 14),
       pkMat (D.ThTs_RB 16), pkMat (D.ThTs_RB 16), pkMat (D.ThTs_RB 14), pkMat (D.ThTs_RB 16),
       pkMat (D.ThTs_RB 14)] := rfl
  rw [e, prod_cons_foldl, L.ts_18]
  simp only [pkMat_mulB L.c4]
  rfl

include L hA hB hSA hSB in
theorem ents_tw4 : TwEnts (tw4 RA RB) 4 (fun i => pkMat (D.ThTs_RB (twRegE i)))
    (fun i => pkMat (D.ThTs_RB (twRegF i))) := by
  refine ⟨rfl, fun i hi => ?_⟩
  interval_cases i
  · exact TwEntry.of_inv (ts_h0 L hA hB hSA hSB).1 (ts_h0 L hA hB hSA hSB).2
      (entry_mul_inv L 0 (by norm_num))
  · exact TwEntry.of_inv (ts_h1 L hA hB hSA hSB).1 (ts_h1 L hA hB hSA hSB).2
      (entry_mul_inv L 1 (by norm_num))
  · exact TwEntry.of_inv (ts_e3 L hA hB hSA hSB).1 (ts_e3 L hA hB hSA hSB).2
      (entry_mul_inv L 2 (by norm_num))
  · exact TwEntry.of_inv (ts_e4 L hA hB hSA hSB).1 (ts_e4 L hA hB hSA hSB).2
      (entry_mul_inv L 3 (by norm_num))

include L hA hB hSA hSB in
theorem ents_twL : TwEnts (twL RA RB) 10 (fun i => pkMat (D.ThTs_RB (twRegE i)))
    (fun i => pkMat (D.ThTs_RB (twRegF i))) := by
  have h4 := ents_tw4 L hA hB hSA hSB
  have h5 := ents_step h4 (w := [1, -4, 3, 4, 1]) (by decide) (step_prod0 L)
    (entry_mul_inv L 4 (by norm_num))
  have h6 := ents_step h5 (w := [-2, -2, 1, 2, 2]) (by decide) (step_prod1 L)
    (entry_mul_inv L 5 (by norm_num))
  have h7 := ents_step h6 (w := [6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 6]) (by decide)
    (step_prod2 L) (entry_mul_inv L 6 (by norm_num))
  have h8 := ents_step h7 (w := [-2, -2, 3, 1, 4, 2]) (by decide) (step_prod3 L)
    (entry_mul_inv L 7 (by norm_num))
  have h9 := ents_step h8 (w := [8, 8]) (by decide) (step_prod4 L)
    (entry_mul_inv L 8 (by norm_num))
  exact ents_step h9 (w := [7, -9, -9, 7, 9, 9, 7, 9, 7]) (by decide) (step_prod5 L)
    (entry_mul_inv L 9 (by norm_num))

include L in
theorem orig0_prod : ((origWord0).map
    (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))).prod =
    pkMat (D.ThTs_RB 1) := by
  have e : ((origWord0).map
      (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))) =
      [pkMat (D.ThTs_RB 15), pkMat (D.ThTs_RB 18), pkMat (D.ThTs_RB 14), pkMat (D.ThTs_RB 4),
        pkMat (D.ThTs_RB 14), pkMat (D.ThTs_RB 25), pkMat (D.ThTs_RB 15), pkMat (D.ThTs_RB 17),
        pkMat (D.ThTs_RB 14), pkMat (D.ThTs_RB 17), pkMat (D.ThTs_RB 14), pkMat (D.ThTs_RB 16),
        pkMat (D.ThTs_RB 14), pkMat (D.ThTs_RB 16), pkMat (D.ThTs_RB 18)] := rfl
  rw [e, prod_cons_foldl, ← L.c624]
  simp only [pkMat_mulB L.c4]
  rfl

include L in
theorem orig1_prod : ((origWord1).map
    (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))).prod =
    pkMat (D.ThTs_RB 2) := by
  have e : ((origWord1).map
      (tupM (fun i => pkMat (D.ThTs_RB (twRegE i))) (fun i => pkMat (D.ThTs_RB (twRegF i))))) =
      [pkMat (D.ThTs_RB 16), pkMat (D.ThTs_RB 16), pkMat (D.ThTs_RB 16), pkMat (D.ThTs_RB 9),
        pkMat (D.ThTs_RB 11), pkMat (D.ThTs_RB 25), pkMat (D.ThTs_RB 15), pkMat (D.ThTs_RB 11),
        pkMat (D.ThTs_RB 17), pkMat (D.ThTs_RB 14), pkMat (D.ThTs_RB 17),
        pkMat (D.ThTs_RB 25)] := rfl
  rw [e, prod_cons_foldl, ← L.c625]
  simp only [pkMat_mulB L.c4]
  rfl

include L hA hB hSA hSB in
theorem concl2324_of_leaves :
    eqRows (Native.mulRows (hR RA RB centWord0) (rT RA RB))
        (Native.mulRows (rT RA RB) (hR RA RB centWord0)) = true ∧
      eqRows (Native.mulRows (hR RA RB centWord1) (rT RA RB))
        (Native.mulRows (rT RA RB) (hR RA RB centWord1)) = true ∧
      (∀ R ∈ twL RA RB, eqRows (Native.mulRows R (invRows R)) idRows = true ∧
        (invRows R).size = 248 ∧ ∀ r ∈ invRows R, r.wf = true) ∧
      (twL RA RB).length = 10 ∧
      eqRows (signedRows (tupleRows (twL RA RB)) origWord0) (lx RA RB) = true ∧
      eqRows (signedRows (tupleRows (twL RA RB)) origWord1) (ly RA RB) = true ∧
      eqRows (rR RA RB) (rE217 RA RB) = true ∧ eqRows (rR RA RB) idRows = false ∧
      eqRows (rR RA RB) (m3z RA RB) = false := by
  obtain ⟨hH0G, hH0M⟩ := ts_h0 L hA hB hSA hSB
  obtain ⟨hH1G, hH1M⟩ := ts_h1 L hA hB hSA hSB
  obtain ⟨hTG, hTM⟩ := ts_rT L hA hB hSA hSB
  obtain ⟨hlxG, hlxM⟩ := ts_lx L hA hB hSA hSB
  obtain ⟨hlyG, hlyM⟩ := ts_ly L hA hB hSA hSB
  obtain ⟨hRG, hRM⟩ := ts_rR L hA hB hSA hSB
  obtain ⟨hEG, hEM⟩ := ts_rE217 L hA hB hSA hSB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨hZG, hZM⟩⟩ := m3_regs L hA hB hSA hSB
  have hEnts := ents_twL L hA hB hSA hSB
  refine ⟨?_, ?_, ?_, hEnts.1, ?_, ?_, ?_, ?_, ?_⟩
  · refine eqRows_of_rowsMatrix_eq (hH0G.mulRows hTG) (hTG.mulRows hH0G) ?_
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, hH0M, hTM, ← pkMat_mulB L.c4,
      ← pkMat_mulB L.c4, L.c622]
  · refine eqRows_of_rowsMatrix_eq (hH1G.mulRows hTG) (hTG.mulRows hH1G) ?_
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, hH1M, hTM, ← pkMat_mulB L.c4,
      ← pkMat_mulB L.c4, L.c623]
  · intro R hR
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hR
    have hi' : i < 10 := hEnts.1 ▸ hi
    have hent := hEnts.2 i hi'
    rw [List.getD_eq_getElem _ _ hi] at hent
    obtain ⟨h1, h2, h3, h4⟩ := hent
    refine ⟨eqRows_of_rowsMatrix_eq (h1.mulRows h3) wfRows_idRows ?_, h3.1, h3.2⟩
    rw [rowsMatrix_mulRows, h2, h4, rowsMatrix_idRows]
    exact entry_mul_inv L i hi'
  · obtain ⟨hG, hM⟩ := word_matrix hEnts (w := origWord0) (by decide)
    refine eqRows_of_rowsMatrix_eq hG hlxG ?_
    rw [hM, orig0_prod L, hlxM]
  · obtain ⟨hG, hM⟩ := word_matrix hEnts (w := origWord1) (by decide)
    refine eqRows_of_rowsMatrix_eq hG hlyG ?_
    rw [hM, orig1_prod L, hlyM]
  · refine eqRows_of_rowsMatrix_eq hRG hEG ?_
    rw [hRM, hEM, L.c626]
  · refine eqRows_eq_false_of_matrix ?_
    rw [hRM, rowsMatrix_idRows]
    intro h
    refine L.c627 (pkMat_inj ?_ (inLayout_one L.c4) (h.trans (pkMat_one L.c4).symm))
    rw [L.ts_31]
    exact inLayout_mulB L.c4 _ _
  · refine eqRows_eq_false_of_matrix ?_
    rw [hRM, hZM]
    intro h
    refine L.c628 (pkMat_inj ?_ ?_ h)
    · rw [L.ts_31]
      exact inLayout_mulB L.c4 _ _
    · rw [L.m3_16]
      exact inLayout_powB L.c4 _ _ _

end Ts

end CFSG.KC.Th.Spec

end
