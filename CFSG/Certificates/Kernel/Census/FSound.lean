module

public import CFSG.Certificates.Kernel.Census.ToMainF
import CFSG.Certificates.Kernel.Census.FProof
import CFSG.Certificates.Kernel.Census.ConjProof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFullW

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Monster.B.Co2.Native

open CFSG.Monster.B.Co2 CFSG.RankThree.Native in
private theorem fullOK_of_pfullOK {n w : Nat} (G : SP.Good n w) {inX : Array Nat → Bool}
    {inXP : Nat → Bool}
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    {xG : Array Nat} (hxg : ∀ x ∈ xG.toList, canon1 n w x = true) {nd : FNodeP}
    (hb : ∀ x ∈ nd.basis.toList, canon1 n w x = true)
    (hf : ∀ f ∈ nd.facs, canonG n w f.γ = true) (h : pfullOK n w inXP xG nd = true) :
    fullOK n inX (xG.map (unpackP n w)) (nd.toMain n w) = true := by
  have hyc : ∀ x ∈ (nd.facs.map (NFacP.val n w nd.basis)).toArray.toList,
      canon1 n w x = true := by
    intro x hx
    simp only [List.toList_toArray, List.mem_map] at hx
    obtain ⟨f, -, rfl⟩ := hx
    exact SP.pc_canon G _ _
  have hys : ((nd.facs.map (NFacP.toMain n w)).map (NFac.val n (nd.basis.map (unpackP n w)))).toArray =
      (nd.facs.map (NFacP.val n w nd.basis)).toArray.map (unpackP n w) := by
    rw [List.map_toArray (f := unpackP n w) (l := nd.facs.map (NFacP.val n w nd.basis)),
      List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left fun f hf' => (SP.nval_eq G hb (hf f hf')).symm
  obtain ⟨hregs, hrc⟩ := SP.regs_unpack G.hn G.hw hyc nd.prog
  have hslp := pslpOK_eq_proved (prog := nd.prog) G.hn G.hw (List.all_eq_true.2 hyc)
  unfold pfullOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨hv, hok⟩, hs⟩, hx⟩ := h
  have hfacs : (nd.toMain n w).facs = nd.facs.map (NFacP.toMain n w) := rfl
  have hbasis : (nd.toMain n w).basis = nd.basis.map (unpackP n w) := rfl
  have hprog : (nd.toMain n w).prog = nd.prog := rfl
  have hgIdx : (nd.toMain n w).gIdx = nd.gIdx := rfl
  unfold fullOK
  simp only [hfacs, hbasis, hprog, hgIdx]
  rw [hys, ← hregs, ← hslp]
  simp only [Bool.and_eq_true, allLt_iff, Array.size_map, decide_eq_true_eq]
  refine ⟨⟨⟨fun k hk => ?_, ?_⟩, hs⟩, fun k hk => ?_⟩
  · rw [SP.map_get _ _ hk, SP.validA_unpack G.hw (SP.canon_get hb k hk)]
    exact hv k hk
  · refine List.all_eq_true.2 fun f hf' => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
    rw [← NFac.okK_eq]
    exact SP.nok_of G hin hb (hf g hg) (hok g hg)
  · obtain ⟨hlt, he⟩ := hx k hk
    refine ⟨hlt, ?_⟩
    rw [SP.map_get _ _ hk, SP.map_get _ _ hlt,
      SP.eqA_unpack (SP.canon_get hxg k hk) (SP.canon_get hrc _ hlt), Nat.beq_eq]
    exact he

open CFSG.Monster.B.Co2 CFSG.RankThree.Native in
private theorem pairOKW_of_ppairOK {n w : Nat} (G : SP.Good n w) {ps : List Nat}
    {nodes : Array FNodeP}
    (hnb : ∀ k < nodes.size, ∀ x ∈ (nodes[k]!).basis.toList, canon1 n w x = true)
    {x y : Nat} (hx : canon1 n w x = true) (hy : canon1 n w y = true)
    (h : ppairOK n w ps nodes x y = true) :
    pairOKW n ps (nodes.map (FNodeP.toMain n w)) (unpackP n w x) (unpackP n w y) = true := by
  have hb : ∀ z ∈ (#[x, y] : Array Nat).toList, canon1 n w z = true := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have e : (#[unpackP n w x, unpackP n w y] : Array (Array Nat)) =
      (#[x, y] : Array Nat).map (unpackP n w) := by simp
  have hm := SP.pmaskCert_toMain G hb
  have hmc := SP.pmaskCert_canon G hb
  unfold ppairOK at h
  simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range, List.all_eq_true] at h
  obtain ⟨hE, k, hk, hall⟩ := h
  unfold pairOKW
  rw [e, ← hm]
  simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range, allLt_iff, Array.size_map]
  refine ⟨enumOK_of_enumOKK (SP.enumOKK_of_penumOK G hb hmc hE), k, hk, ?_⟩
  have hbk : ((nodes[k]!).toMain n w).basis = (nodes[k]!).basis.map (unpackP n w) := rfl
  rw [SP.map_get _ _ hk, hbk]
  intro j hj
  rw [Array.size_map] at hj
  rw [SP.map_get _ _ hj, SP.memA_eq hmc (SP.canon_get (hnb k hk) j hj)]
  exact hall j hj

theorem pfCensus_sound {n w : Nat} {ps : List Nat} {inX : Array Nat → Bool} {inXP : Nat → Bool}
    {sG xG : Array Nat} {nodes : Array FNodeP} {cS : ArrCertP}
    (h24 : n ≤ 2 ^ 24) (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hsg : sG.toList.all (canon1 n w) = true)
    (hxg : xG.toList.all (canon1 n w) = true) (hnc : canonF n w nodes = true)
    (hcs : cS.pts.toList.all (canon1 n w) = true)
    (hin : ∀ P, canon1 n w P = true → pvalid n w P = true → inXP P = inX (unpackP n w P))
    (hS : penumOK n w sG ps cS = true)
    (hX : ((List.range xG.size).all fun k => pvalid n w xG[k]!) = true)
    (hN : ∀ k < nodes.size, pfullOK n w inXP xG nodes[k]! = true)
    (hP : cS.pts.toList.all (ppairsAt n w ps nodes cS) = true) :
    fCensusOKW n ps inX (xG.map (unpackP n w)) (sG.map (unpackP n w))
      (nodes.map (FNodeP.toMain n w)) (cS.toMain n w) = true := by
  obtain ⟨e1, e2, -⟩ := SP.pid_good24 hw h24
  have G : SP.Good n w := ⟨hn, hw, e1, e2⟩
  have hsg' := List.all_eq_true.1 hsg
  have hxg' := List.all_eq_true.1 hxg
  have hcs' := List.all_eq_true.1 hcs
  unfold canonF at hnc
  have hnc' : ∀ k < nodes.size, (∀ x ∈ (nodes[k]!).basis.toList, canon1 n w x = true) ∧
      ∀ f ∈ (nodes[k]!).facs, canonG n w f.γ = true := by
    intro k hk
    have := List.all_eq_true.1 hnc (nodes[k]!) (by
      rw [getElem!_pos nodes k hk]
      exact Array.getElem_mem_toList hk)
    simpa only [Bool.and_eq_true, List.all_eq_true] using this
  have hpts : (cS.toMain n w).pts = cS.pts.map (unpackP n w) := rfl
  unfold fCensusOKW
  simp only [Bool.and_eq_true, CFSG.Monster.B.Co2.allLt_iff, Array.size_map, hpts]
  refine ⟨⟨⟨enumOK_of_enumOKK (SP.enumOKK_of_penumOK G hsg' hcs' hS), fun k hk => ?_⟩,
    fun k hk => ?_⟩, fun i hi j hj => ?_⟩
  · rw [SP.map_get _ _ hk, SP.validA_unpack hw (SP.canon_get hxg' k hk)]
    exact List.all_eq_true.1 hX k (List.mem_range.2 hk)
  · rw [SP.map_get _ _ hk]
    exact fullOK_of_pfullOK G hin hxg' (hnc' k hk).1 (hnc' k hk).2 (hN k hk)
  · have hxc := SP.canon_get hcs' i hi
    have hyc := SP.canon_get hcs' j hj
    have hp := List.all_eq_true.1 (List.all_eq_true.1 hP cS.pts[i]! (by
      rw [getElem!_pos cS.pts i hi]
      exact Array.getElem_mem_toList hi)) cS.pts[j]! (by
      rw [getElem!_pos cS.pts j hj]
      exact Array.getElem_mem_toList hj)
    rw [SP.map_get _ _ hi, SP.map_get _ _ hj, ← SP.pc_eq G hxc (q := cS.pts[i]!),
      SP.eqA_pid G (SP.pc_canon G _ _), SP.eqA_pid G hxc, SP.eqA_pid G hyc,
      SP.eqA_unpack hxc hyc, SP.commA_eq G hxc hyc]
    simp only [Bool.or_eq_true] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr (pairOKW_of_ppairOK G (fun k hk => (hnc' k hk).1) hxc hyc hp)

end CFSG.KC.Census
