module

public import CFSG.Certificates.Kernel.Census.ConjProof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjT
public import Certificates.Data.Kernel.Census.PackedTree

public section

namespace CFSG.KC.Census.SP

open CFSG.KC.Enum CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.Monster.B.Fischer

variable {n w : Nat} (G : Good n w)
include G

theorem nodeOKT_of (hid : ∀ i < n, at' w (pid n w) i = i) {ps : List Nat}
    {inW : Array Nat → Bool} {inWP : Nat → Bool}
    (hinW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = inW (unpackP n w P))
    {d : ConjDataP} (C : CanonC n w d) {e0 : Array Nat} (he0 : ∀ x ∈ e0.toList, canon1 n w x = true)
    (hsz : d.ci.size = d.cs.size) (hUV : ∀ u ∈ d.us.toList, pvalid n w u = true)
    (Cv : ∀ i < d.nodes.size, ∀ k < (d.nodes[i]!).basis.size,
      pvalid n w (d.nodes[i]!).basis[k]! = true)
    {i : Nat} (hi : i < d.nodes.size)
    (h : pnodeOKT n w ps inWP d (pcN n w d.nodes) e0 i = true) :
    nodeOKT n ps inW (d.toMain n w)
      ((d.nodes.map (NodeP.toMain n w)).map fun nd => maskCert n nd.basis)
      (e0.map (unpackP n w)) i = true := by
  unfold pnodeOKT at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hE, hrest⟩ := h
  have hni : (d.nodes.map (NodeP.toMain n w))[i]! = (d.nodes[i]!).toMain n w := map_get _ _ hi
  have hbi : ((d.nodes[i]!).toMain n w).basis = (d.nodes[i]!).basis.map (unpackP n w) := rfl
  have hwi : ((d.nodes[i]!).toMain n w).wit = (d.nodes[i]!).wit.toMain n w := rfl
  have hcN := cN_canon G C.basis i
  unfold nodeOKT
  simp only [Bool.and_eq_true, Bool.or_eq_true, ConjDataP.toMain]
  rw [hni, hbi, hwi, cN_get G C.basis, isMono_toMain]
  refine ⟨enumOKK_of_penumOK G (C.basis i) hcN hE, ?_⟩
  rcases hrest with hm | ⟨hwx, hents⟩
  · exact Or.inl hm
  · right
    unfold pentsOK at hents
    simp only [Bool.and_eq_true] at hents
    obtain ⟨hl, hall⟩ := hents
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rcases hwx with hs | hx
      · left
        simp only [decide_eq_true_eq, ArrCertP.toMain, Array.size_map]
        exact Nat.blt_eq.mp hs
      · exact Or.inr (excOKW_of G hinW he0 C.excs C.basis hx)
    · rw [Array.size_map]
      exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true hl)
    · rw [Array.toList_map, List.zip_map_left, List.all_map]
      refine all_of (fun ue hue hu => ?_) hall
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      have hu1 := (List.of_mem_zip hue).1
      exact entOK_of G hid C.basis Cv C.cs hsz hi (C.us _ hu1)
        (inj_of_pvalid (hUV _ hu1)).1 hu

end CFSG.KC.Census.SP

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native

theorem ptree_sound_proved {n w : Nat} {ps : List Nat} {inW : Array Nat → Bool}
    {inWP : Nat → Bool} {d : ConjDataP} {e0 : Array Nat} (h24 : n ≤ 2 ^ 24) (hn : n < 2 ^ 32)
    (hw : n ≤ 2 ^ w) (hc : canonC n w d = true)
    (he0 : e0.toList.all (canon1 n w) = true)
    (hinW : ∀ P, canon1 n w P = true → pvalid n w P = true → inWP P = inW (unpackP n w P))
    (hpc : ppcOK n w d.xs d.rs d.cjs d.bs = true) (hinv : pinvOK n w d.xs d.us d.im d.wt = true)
    (htab : ptabOK n w d.xs d.cm d.cs d.ci = true)
    (hrl : Nat.beq d.roots.length d.us.size = true)
    (hR : (d.us.toList.zip d.roots).all
      (fun ur => prootOKC n w (d.nodes.map NodeP.basis) (pcN n w d.nodes) d.cs d.ci ur.1 ur.2) =
        true)
    (hN : ∀ i < d.nodes.size, pnodeOKT n w ps inWP d (pcN n w d.nodes) e0 i = true) :
    conjTreeOKW n ps inW (d.toMain n w) (e0.map (unpackP n w)) = true := by
  obtain ⟨e1, e2, hid⟩ := SP.pid_good24 hw h24
  have G : SP.Good n w := ⟨hn, hw, e1, e2⟩
  have hpidv : pvalid n w (pid n w) = true :=
    pvalid_of_inj hw (fun i hi => by rw [hid i hi]; exact hi)
      (fun i hi j hj e => by rwa [hid i hi, hid j hj] at e)
  have C := SP.canonC_facts hc
  have he0' : ∀ x ∈ e0.toList, canon1 n w x = true := List.all_eq_true.1 he0
  obtain ⟨hpcM, hxv⟩ := SP.pcOK_of G d.xs d.rs d.cjs d.bs C.xs hpc
  have hxcv : ∀ x ∈ d.xs, canon1 n w x = true ∧ pvalid n w x = true :=
    fun x hx => ⟨C.xs x hx, hxv x hx⟩
  obtain ⟨hinvM, hz⟩ := SP.invOK_of G hxcv C.us hinv
  obtain ⟨htabM, hsz⟩ := SP.conjTabOK_of G C.xs C.cs C.ci htab
  have hlen : d.im.length = d.us.size := by
    unfold pinvOK at hinv
    simp only [Bool.and_eq_true] at hinv
    exact Nat.eq_of_beq_eq_true hinv.1.1.1
  have hUV : ∀ u ∈ d.us.toList, pvalid n w u = true := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
    have hk' : k < d.im.length := by simp at hk; omega
    have hm : (d.us.toList[k], d.im[k]) ∈ d.us.toList.zip d.im :=
      List.mem_iff_getElem.2 ⟨k, by simp; omega, by simp⟩
    have e := hz _ hm
    dsimp only at e
    rw [e]
    exact SP.ppcA_valid G hpidv d.xs _ hxcv
  have Cv : ∀ i < d.nodes.size, ∀ k < (d.nodes[i]!).basis.size,
      pvalid n w (d.nodes[i]!).basis[k]! = true := by
    intro i hi k hk
    have h := hN i hi
    unfold pnodeOKT at h
    simp only [Bool.and_eq_true] at h
    exact pvalid_of_penumOK h.1 hk
  unfold conjTreeOKW
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨⟨⟨⟨hpcM, hinvM⟩, htabM⟩, ?_⟩, ?_⟩, fun i hi => ?_⟩
  · simp only [ConjDataP.toMain, Array.size_map]
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true hrl)
  · simp only [ConjDataP.toMain]
    rw [Array.toList_map, List.zip_map_left, List.all_map]
    refine SP.all_of (fun ur hur hr => ?_) hR
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    have hu1 := (List.of_mem_zip hur).1
    exact SP.rootOKC_of G hid C.basis C.cs hsz (C.us _ hu1) (inj_of_pvalid (hUV _ hu1)).1 hr
  · have hi' : i < d.nodes.size := by simpa [ConjDataP.toMain] using hi
    exact SP.nodeOKT_of G hid hinW C he0' hsz hUV Cv hi' (hN i hi')

end CFSG.KC.Census

end
