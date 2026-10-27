module

public import CFSG.Certificates.Kernel.Census.SoundProof

public section

namespace CFSG.KC.Census.SP

open CFSG.KC.Enum CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.Monster.B.Fischer

variable {n w : Nat} (G : Good n w)
include G

theorem pword_eq {gs : Array Nat} (hg : ∀ x ∈ gs.toList, canon1 n w x = true) {wd : List Nat}
    (hw : ∀ i ∈ wd, i < gs.size) :
    wordG n (gs.map (unpackP n w)) wd = unpackP n w (pword n w gs wd) ∧
      canon1 n w (pword n w gs wd) = true := by
  have hl : ∀ x ∈ wd.map (fun i => gs[i]!), canon1 n w x = true := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact canon_get hg i (hw i hi)
  obtain ⟨hp, hpc⟩ := pprod_eq G hl
  refine ⟨?_, hpc⟩
  rw [wordG, pword, hp, List.map_map]
  exact congrArg _ (List.map_congr_left fun i hi => map_get _ _ (hw i hi))

omit G in
theorem lettersLt_of {m : Nat} {ws : List (List Nat)} (h : plettersLt m ws = true) :
    lettersLt m ws = true := by
  simp only [plettersLt, List.all_eq_true, Nat.blt_eq] at h
  simp only [lettersLt, List.all_eq_true, decide_eq_true_eq]
  exact h

omit G in
theorem perfW_default : PerfWP.toMain (default : PerfWP) = default := rfl

theorem witOKW2_of {ps : List Nat} {inX outX : Array Nat → Bool} {inXP outXP : Nat → Bool}
    {allowPW allowInX allowU : Bool}
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    (hout : ∀ P, canon1 n w P = true → pvalid n w P = true → outXP P = outX (unpackP n w P))
    {basis : Array Nat} (hb : ∀ x ∈ basis.toList, canon1 n w x = true)
    (hbv : ∀ k < basis.size, pvalid n w basis[k]! = true)
    {cE : ArrCertP} (hE : ∀ x ∈ cE.pts.toList, canon1 n w x = true ∧ pvalid n w x = true)
    {cs : Array ArrCertP} (hcs : ∀ j : Nat, ∀ x ∈ (cs[j]!).pts.toList, canon1 n w x = true)
    {pf : PerfWP} {wt : WitP} (hW : canonW n w wt = true)
    (h : pwitOK2 n w ps inXP outXP allowPW allowInX allowU basis cE cs pf wt = true) :
    witOKW2 n ps inX outX allowPW allowInX allowU (basis.map (unpackP n w)) (cE.toMain n w)
      (cs.map (ArrCertP.toMain n w)) pf.toMain (wt.toMain n w) = true := by
  cases wt with
  | perfect gens comms x k conjs e g =>
    simp only [canonW] at hW
    have hl : ∀ l ∈ gens, canonG n w l.1 = true := fun l hl => List.all_eq_true.1 hW l hl
    simp only [pwitOK2, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Bool.not_eq_true',
      List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPW, h1⟩, hL⟩, hV⟩, hcm⟩, hLQ⟩, hQ⟩, hx⟩, hxp⟩, hcj⟩, hLR⟩, hR⟩,
      hg⟩, hnc⟩ := h
    simp only [WitP.toMain, PerfWP.toMain, witOKW2, Bool.and_eq_true, List.all_map,
      Bool.not_eq_true', List.all_eq_true, List.mem_range]
    set gs := (gens.map fun l => ppow n w (pgamma n w l.1) l.2).toArray
    have hgs : ((gens.map fun l => (l.1.map (GFacP.toMain n w), l.2)).map fun l =>
        powA n (gammaA n l.1) l.2).toArray = gs.map (unpackP n w) := by
      refine arr_map_eq ?_
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun l hlm => ?_
      obtain ⟨e1, c1⟩ := gamma_eq G (hl l hlm)
      simp only [Function.comp_apply]
      rw [(ppow_eq G c1 l.2).1, e1]
    have hgc : ∀ y ∈ gs.toList, canon1 n w y = true := canon_arr fun y hy => by
      obtain ⟨l, hlm, rfl⟩ := List.mem_map.1 hy
      exact (ppow_eq G (gamma_eq G (hl l hlm)).2 l.2).2
    have hL' : ∀ wd ∈ pf.pw, ∀ i ∈ wd, i < gs.size := by
      simpa only [plettersLt, List.all_eq_true, Nat.blt_eq] using hL
    set pts := (pf.pw.map (pword n w gs)).toArray
    have hpts : (pf.pw.map (wordG n (gs.map (unpackP n w)))).toArray =
        pts.map (unpackP n w) := by
      refine arr_map_eq ?_
      rw [List.map_map]
      exact List.map_congr_left fun wd hwd => (pword_eq G hgc (hL' wd hwd)).1
    have hpc : ∀ y ∈ pts.toList, canon1 n w y = true := canon_arr fun y hy => by
      obtain ⟨wd, hwd, rfl⟩ := List.mem_map.1 hy
      exact (pword_eq G hgc (hL' wd hwd)).2
    have hP0 := canon_get hpc
    have hpt : ∀ j < pts.size, (pts.map (unpackP n w))[j]! = unpackP n w pts[j]! :=
      fun j hj => map_get _ _ hj
    set qs := (pf.comms.map fun ij => pcomm n w pts[ij.1]! pts[ij.2]!).toArray
    have hqs : (pf.comms.map fun ij => commutatorA n (pts.map (unpackP n w))[ij.1]!
        (pts.map (unpackP n w))[ij.2]!).toArray = qs.map (unpackP n w) := by
      refine arr_map_eq ?_
      rw [List.map_map]
      refine List.map_congr_left fun ij hij => ?_
      have hb1 := hcm ij hij
      simp only [Function.comp_apply]
      rw [hpt _ hb1.1, hpt _ hb1.2, pcomm_eq G (hP0 _ hb1.1) (hP0 _ hb1.2)]
    have hqc : ∀ y ∈ qs.toList, canon1 n w y = true := canon_arr fun y hy => by
      obtain ⟨ij, -, rfl⟩ := List.mem_map.1 hy
      exact pc_canon G _ _
    set rs := (pf.conjs.map fun p => pconj n w pts[p]! (pc n w pts[pf.x]! pts[pf.x]!)).toArray
    have hxc := hP0 _ hx
    have hrs : (pf.conjs.map fun p => conjA n (pts.map (unpackP n w))[p]!
        (compA n (pts.map (unpackP n w))[pf.x]! (pts.map (unpackP n w))[pf.x]!)).toArray =
        rs.map (unpackP n w) := by
      refine arr_map_eq ?_
      rw [List.map_map]
      refine List.map_congr_left fun p hp => ?_
      have hp' := hcj p hp
      simp only [Function.comp_apply]
      rw [hpt _ hp', hpt _ hx, ← pc_eq G hxc, pconj_eq G (hP0 _ hp') (pc_canon G _ _)]
    have hrc : ∀ y ∈ rs.toList, canon1 n w y = true := canon_arr fun y hy => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hy
      exact pc_canon G _ _
    have hLQ' : ∀ wd ∈ pf.genQ, ∀ i ∈ wd, i < qs.size := by
      simpa only [plettersLt, List.all_eq_true, Nat.blt_eq] using hLQ
    have hLR' : ∀ wd ∈ pf.genR, ∀ i ∈ wd, i < rs.size := by
      simpa only [plettersLt, List.all_eq_true, Nat.blt_eq] using hLR
    have hgetD : ∀ (ws : List (List Nat)) (i : Nat), ws.getD i [] ∈ ws ∨ ws.getD i [] = [] :=
      fun ws i => by
        by_cases hi : i < ws.length
        · left
          rw [List.getD_eq_getElem _ _ hi]
          exact List.getElem_mem hi
        · right
          exact List.getD_eq_default _ _ (by omega)
    have hwq : ∀ i, ∀ j ∈ pf.genQ.getD i [], j < qs.size := fun i j hj => by
      rcases hgetD pf.genQ i with h | h
      · exact hLQ' _ h j hj
      · rw [h] at hj
        simp at hj
    have hwr : ∀ i, ∀ j ∈ pf.genR.getD i [], j < rs.size := fun i j hj => by
      rcases hgetD pf.genR i with h | h
      · exact hLR' _ h j hj
      · rw [h] at hj
        simp at hj
    obtain ⟨hm, hmc⟩ := pmask_eq G hb pf.e
    simp only [hgs, hpts, hqs, hrs, Array.size_map, decide_eq_true_eq]
    rw [hpt _ hx, hpt _ hg, ← hm, commA_eq G hmc (hP0 _ hg), ← (ppow_eq G hxc (2 ^ pf.k)).1,
      eqA_pid G (ppow_eq G hxc (2 ^ pf.k)).2]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPW, fun l hlm => ?_⟩, lettersLt_of hL⟩, fun j hj => ?_⟩, hcm⟩,
      lettersLt_of hLQ⟩, fun i hi => ?_⟩, hx⟩, Nat.beq_eq.mpr hxp⟩, hcj⟩, lettersLt_of hLR⟩,
      fun i hi => ?_⟩, hg⟩, hnc⟩
    · simp only [Function.comp_apply, List.all_map, List.all_eq_true]
      exact fun f hf => gok_of G hin hb (by
        have := List.all_eq_true.1 (hl l hlm) f hf
        simpa only [Bool.and_eq_true] using this) (h1 l hlm f hf)
    · rw [validK_eq, hpt _ hj, validA_unpack G.hw (hP0 _ hj)]
      exact hV j hj
    · rw [map_get _ _ hi, (pword_eq G hqc (hwq i)).1,
        eqA_unpack (canon_get hgc i hi) (pword_eq G hqc (hwq i)).2]
      exact Nat.beq_eq.mpr (hQ i hi)
    · rw [map_get _ _ hi, (pword_eq G hrc (hwr i)).1,
        eqA_unpack (canon_get hgc i hi) (pword_eq G hrc (hwr i)).2]
      exact Nat.beq_eq.mpr (hR i hi)
  | order4 l m =>
    exact witOKW_of G (ps := ps) (allowPW := allowPW) (allowInX := allowInX) (allowU := allowU)
      hin hout hb hbv hE hcs hW h
  | twoGroup gens k =>
    exact witOKW_of G (ps := ps) (allowPW := allowPW) (allowInX := allowInX) (allowU := allowU)
      hin hout hb hbv hE hcs hW h
  | inX =>
    exact witOKW_of G (ps := ps) (allowPW := allowPW) (allowInX := allowInX) (allowU := allowU)
      hin hout hb hbv hE hcs hW h
  | small =>
    exact witOKW_of G (ps := ps) (allowPW := allowPW) (allowInX := allowInX) (allowU := allowU)
      hin hout hb hbv hE hcs hW h
  | closing s t c kc v gens comms =>
    exact witOKW_of G (ps := ps) (allowPW := allowPW) (allowInX := allowInX) (allowU := allowU)
      hin hout hb hbv hE hcs hW h

theorem nodeOKW2_of {ps : List Nat} {inX outX : Array Nat → Bool} {inXP outXP : Nat → Bool}
    {allowPW allowInX allowU : Bool}
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    (hout : ∀ P, canon1 n w P = true → pvalid n w P = true → outXP P = outX (unpackP n w P))
    {sG : Array Nat} {nodes : Array NodeP} {cS : ArrCertP} {wcs : Array (Array ArrCertP)}
    {pfs : Array PerfWP}
    (C : Canon n w sG nodes cS wcs) {i : Nat} (hi : i < nodes.size)
    (h : pnodeOK2 n w ps inXP outXP allowPW allowInX allowU cS nodes (pcN n w nodes) wcs pfs i =
      true) :
    nodeOKW2 n ps inX outX allowPW allowInX allowU (cS.toMain n w) (nodes.map (NodeP.toMain n w))
      ((nodes.map (NodeP.toMain n w)).map fun nd => maskCert n nd.basis)
      (wcs.map fun cs => cs.map (ArrCertP.toMain n w)) (pfs.map PerfWP.toMain) i = true := by
  unfold pnodeOK2 at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hE, hW⟩, hch⟩ := h
  have hni : (nodes.map (NodeP.toMain n w))[i]! = (nodes[i]!).toMain n w := map_get _ _ hi
  have hbi : ((nodes[i]!).toMain n w).basis = (nodes[i]!).basis.map (unpackP n w) := rfl
  have hwi : ((nodes[i]!).toMain n w).wit = (nodes[i]!).wit.toMain n w := rfl
  have hci : ((nodes[i]!).toMain n w).children = (nodes[i]!).children := rfl
  have hwcs : (wcs.map fun cs => cs.map (ArrCertP.toMain n w))[i]! =
      (wcs[i]!).map (ArrCertP.toMain n w) := map_get' _ (default_map _) wcs i
  have hpf : (pfs.map PerfWP.toMain)[i]! = (pfs[i]!).toMain := map_get' _ perfW_default pfs i
  unfold nodeOKW2
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  rw [hni, hbi, hwi, hci, cN_get G C.basis, hwcs, hpf, isMono_toMain]
  have hcN := cN_canon G C.basis i
  refine ⟨⟨enumOKK_of_penumOK G (C.basis i) hcN hE, witOKW2_of G hin hout (C.basis i)
    (fun k hk => pvalid_of_penumOK hE hk)
    (fun x hx => ⟨hcN x hx, pvalid_pts_of_penumOK hE x hx⟩) (C.wcs i) (C.wit i) hW⟩, ?_⟩
  rcases hch with hm | hwk
  · exact Or.inl hm
  · right
    rw [allLt_iff]
    intro p hp
    have hp' : p < cS.pts.size := by simpa [ArrCertP.toMain] using hp
    have hf := walkAll_spec _ _ hwk p (by simpa using hp')
    rw [getD_toList_nat] at hf
    have hu : cS.pts.toList[p] = cS.pts[p]! := by
      rw [getElem!_pos cS.pts p hp']
      simp
    rw [hu] at hf
    have huc := canon_get C.cS p hp'
    have hcomm : (allLt ((nodes[i]!).basis.map (unpackP n w)).size fun k =>
        commA n (unpackP n w cS.pts[p]!) ((nodes[i]!).basis.map (unpackP n w))[k]!) =
        (List.range (nodes[i]!).basis.size).all fun k =>
          pcommA n w cS.pts[p]! (nodes[i]!).basis[k]! := by
      apply Bool.eq_iff_iff.mpr
      rw [allLt_iff, List.all_eq_true, Array.size_map]
      refine forall_congr' fun k => ?_
      rw [List.mem_range]
      refine imp_congr_right fun hk => ?_
      rw [map_get _ _ hk, commA_eq G huc (canon_get (C.basis i) k hk)]
    rw [getPts hp', ← pc_eq G huc, eqA_pid G (pc_canon G _ _), memA_eq hcN huc, hcomm]
    simp only [Bool.or_eq_true] at hf ⊢
    rcases hf with ((h1 | h1) | h1) | h1
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h1))
    · exact Or.inl (Or.inr h1)
    · exact Or.inr (childOK_of G C.basis hi huc h1)

end CFSG.KC.Census.SP

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native

theorem pcensus_sound2_proved {n w : Nat} {ps : List Nat} {inX outX : Array Nat → Bool}
    {inXP outXP : Nat → Bool} {allowPW allowInX allowU : Bool} {sG roots : Array Nat}
    {nodes : Array NodeP} {cS : ArrCertP} {wcs : Array (Array ArrCertP)} {pfs : Array PerfWP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonP n w sG nodes cS wcs = true)
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    (hout : ∀ P, canon1 n w P = true → pvalid n w P = true → outXP P = outX (unpackP n w P))
    (hS : penumOK n w sG ps cS = true)
    (hR : ((List.range cS.pts.size).all fun p =>
      prootOK n w nodes (pcN n w nodes) cS.pts[p]! roots[p]!) = true)
    (hN : ∀ i < nodes.size,
      pnodeOK2 n w ps inXP outXP allowPW allowInX allowU cS nodes (pcN n w nodes) wcs pfs i =
        true) :
    censusOKW2 n ps inX outX allowPW allowInX allowU (sG.map (unpackP n w)) roots
      (nodes.map (NodeP.toMain n w)) (cS.toMain n w)
      (wcs.map fun cs => cs.map (ArrCertP.toMain n w)) (pfs.map PerfWP.toMain) = true := by
  have C := SP.canon_of hc
  have hS' := hS
  unfold penumOK at hS'
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hS'
  obtain ⟨-, ⟨⟨h0, hid⟩, -⟩, -⟩ := hS'
  have hv0 := pvalid_pts_of_penumOK hS cS.pts[0]! (by
    rw [getElem!_pos cS.pts 0 h0]
    exact Array.getElem_mem_toList h0)
  rw [hid] at hv0
  obtain ⟨e1, e2⟩ := SP.pid_good hw hv0
  have G : SP.Good n w := ⟨hn, hw, e1, e2⟩
  unfold censusOKW2
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨SP.enumOKK_of_penumOK G C.sG C.cS hS, fun p hp => ?_⟩, fun i hi => ?_⟩
  · have hp' : p < cS.pts.size := by simpa [ArrCertP.toMain] using hp
    rw [SP.getPts hp']
    exact SP.rootOK_of G C.basis (SP.canon_get C.cS p hp')
      (List.all_eq_true.1 hR p (List.mem_range.2 hp'))
  · have hi' : i < nodes.size := by simpa using hi
    exact SP.nodeOKW2_of G hin hout C hi' (hN i hi')

end CFSG.KC.Census

end
