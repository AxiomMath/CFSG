module

public import CFSG.Certificates.Kernel.Census.SoundProof
public import CFSG.Certificates.Kernel.Census.ToMainExc
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicExcW

public section

namespace CFSG.KC.Census.SP

open CFSG.KC.Enum CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.Monster.B.Fischer

variable {n w : Nat} (G : Good n w)
include G

theorem excOKW_of {ps : List Nat} {inW : Array Nat → Bool} {inWP : Nat → Bool}
    (hinW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = inW (unpackP n w P))
    {e0 : Array Nat} (he0 : ∀ x ∈ e0.toList, canon1 n w x = true) {excs : List ExcRefP}
    (hex : ∀ r ∈ excs, canon1 n w r.w = true) {nodes : Array NodeP}
    (Cb : ∀ i : Nat, ∀ x ∈ (nodes[i]!).basis.toList, canon1 n w x = true) {i : Nat}
    (h : pexcOK n w ps inWP e0 (pcN n w nodes) excs i = true) :
    excOKW n ps inW (e0.map (unpackP n w))
      ((nodes.map (NodeP.toMain n w)).map fun nd => maskCert n nd.basis)
      (excs.map (ExcRefP.toMain n w)) i = true := by
  unfold pexcOK at h
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range,
    Nat.beq_eq] at h
  obtain ⟨hE, r, hr, ⟨⟨⟨⟨hnode, hv⟩, hin⟩, hall⟩, hsz⟩⟩ := h
  have hrc := hex r hr
  unfold excOKW
  simp only [Bool.and_eq_true, List.any_eq_true, List.mem_map, allLt_iff, beq_iff_eq,
    Array.size_map]
  rw [← pmaskCert_toMain G he0]
  refine ⟨enumOKK_of_penumOK G he0 (pmaskCert_canon G he0) hE, ⟨_, ⟨r, hr, rfl⟩, ?_⟩⟩
  have hw' : (r.toMain n w).w = unpackP n w r.w := rfl
  have hn' : (r.toMain n w).node = r.node := rfl
  rw [hw', hn', cN_get G Cb, validK_eq, validA_unpack G.hw hrc]
  refine ⟨⟨⟨⟨hnode, hv⟩, inX_eq hinW hrc hv hin⟩, fun j hj => ?_⟩, ?_⟩
  · have hjc := canon_get he0 j hj
    rw [map_get _ _ hj, ← pconj_eq G hrc hjc,
      memA_eq (a := pconj n w r.w e0[j]!) (cN_canon G Cb i) (pc_canon G _ _)]
    exact hall j hj
  · simp only [ArrCertP.toMain, Array.size_map]
    exact hsz

theorem childrenOK_of {cS : ArrCertP} (hcS : ∀ x ∈ cS.pts.toList, canon1 n w x = true)
    {nodes : Array NodeP} (Cb : ∀ i : Nat, ∀ x ∈ (nodes[i]!).basis.toList, canon1 n w x = true)
    {i : Nat} (hi : i < nodes.size) (h : pchildrenOK n w cS nodes (pcN n w nodes) i = true) :
    childrenOK n (cS.toMain n w) (nodes.map (NodeP.toMain n w))
      ((nodes.map (NodeP.toMain n w)).map fun nd => maskCert n nd.basis) i = true := by
  unfold pchildrenOK at h
  unfold childrenOK
  have hni : (nodes.map (NodeP.toMain n w))[i]! = (nodes[i]!).toMain n w := map_get _ _ hi
  have hbi : ((nodes[i]!).toMain n w).basis = (nodes[i]!).basis.map (unpackP n w) := rfl
  have hci : ((nodes[i]!).toMain n w).children = (nodes[i]!).children := rfl
  rw [hni, hbi, hci, cN_get G Cb]
  have hcN := cN_canon G Cb i
  rw [allLt_iff]
  intro p hp
  have hp' : p < cS.pts.size := by simpa [ArrCertP.toMain] using hp
  have hf := walkAll_spec _ _ h p (by simpa using hp')
  rw [getD_toList_nat] at hf
  have hu : cS.pts.toList[p] = cS.pts[p]! := by
    rw [getElem!_pos cS.pts p hp']
    simp
  rw [hu] at hf
  have huc := canon_get hcS p hp'
  have hcomm : (allLt ((nodes[i]!).basis.map (unpackP n w)).size fun k =>
      commA n (unpackP n w cS.pts[p]!) ((nodes[i]!).basis.map (unpackP n w))[k]!) =
      (List.range (nodes[i]!).basis.size).all fun k =>
        pcommA n w cS.pts[p]! (nodes[i]!).basis[k]! := by
    apply Bool.eq_iff_iff.mpr
    rw [allLt_iff, List.all_eq_true, Array.size_map]
    refine forall_congr' fun k => ?_
    rw [List.mem_range]
    refine imp_congr_right fun hk => ?_
    rw [map_get _ _ hk, commA_eq G huc (canon_get (Cb i) k hk)]
  rw [getPts hp', ← pc_eq G huc, eqA_pid G (pc_canon G _ _), memA_eq hcN huc, hcomm]
  simp only [Bool.or_eq_true] at hf ⊢
  rcases hf with ((h1 | h1) | h1) | h1
  · exact Or.inl (Or.inl (Or.inl h1))
  · exact Or.inl (Or.inl (Or.inr h1))
  · exact Or.inl (Or.inr h1)
  · exact Or.inr (childOK_of G Cb hi huc h1)

end CFSG.KC.Census.SP

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native

theorem pcensusExc_sound_proved {n w : Nat} {ps : List Nat} {inX outX inW : Array Nat → Bool}
    {inXP outXP inWP : Nat → Bool} {allowPW allowInX allowU : Bool} {sG roots e0 : Array Nat}
    {nodes : Array NodeP} {cS : ArrCertP} {wcs : Array (Array ArrCertP)} {excs : List ExcRefP}
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) (hc : canonP n w sG nodes cS wcs = true)
    (he0 : e0.toList.all (canon1 n w) = true) (hex : excs.all (fun r => canon1 n w r.w) = true)
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    (hout : ∀ P, canon1 n w P = true → pvalid n w P = true → outXP P = outX (unpackP n w P))
    (hinW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = inW (unpackP n w P))
    (hS : penumOK n w sG ps cS = true)
    (hR : ((List.range cS.pts.size).all fun p =>
      prootOK n w nodes (pcN n w nodes) cS.pts[p]! roots[p]!) = true)
    (hN : ∀ i < nodes.size, pnodeExcOK n w ps inXP outXP inWP allowPW allowInX allowU cS nodes
      (pcN n w nodes) wcs e0 excs i = true) :
    censusExcOKW n ps inX outX inW allowPW allowInX allowU (sG.map (unpackP n w)) roots
      (nodes.map (NodeP.toMain n w)) (cS.toMain n w)
      (wcs.map fun cs => cs.map (ArrCertP.toMain n w)) (e0.map (unpackP n w))
      (excs.map (ExcRefP.toMain n w)) = true := by
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
  have he0' : ∀ x ∈ e0.toList, canon1 n w x = true := List.all_eq_true.1 he0
  have hex' : ∀ r ∈ excs, canon1 n w r.w = true := List.all_eq_true.1 hex
  unfold censusExcOKW
  simp only [Bool.and_eq_true, Bool.or_eq_true, allLt_iff]
  refine ⟨⟨SP.enumOKK_of_penumOK G C.sG C.cS hS, fun p hp => ?_⟩, fun i hi => ?_⟩
  · have hp' : p < cS.pts.size := by simpa [ArrCertP.toMain] using hp
    rw [SP.getPts hp']
    exact SP.rootOK_of G C.basis (SP.canon_get C.cS p hp')
      (List.all_eq_true.1 hR p (List.mem_range.2 hp'))
  · have hi' : i < nodes.size := by simpa using hi
    have h := hN i hi'
    unfold pnodeExcOK at h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨hE, hX⟩, hC⟩
    · exact Or.inl (SP.nodeOKW_of G hin hout C hi' h)
    · right
      have hni : (nodes.map (NodeP.toMain n w))[i]! = (nodes[i]!).toMain n w :=
        SP.map_get _ _ hi'
      have hbi : ((nodes[i]!).toMain n w).basis = (nodes[i]!).basis.map (unpackP n w) := rfl
      refine ⟨⟨?_, SP.excOKW_of G hinW he0' hex' C.basis hX⟩, SP.childrenOK_of G C.cS C.basis hi' hC⟩
      rw [hni, hbi, SP.cN_get G C.basis]
      exact SP.enumOKK_of_penumOK G (C.basis i) (SP.cN_canon G C.basis i) hE

end CFSG.KC.Census

end
