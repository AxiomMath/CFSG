module

public import CFSG.Certificates.Kernel.TitsOver.Cover

public section

namespace CFSG.KS.TitsOver

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open CFSG.KS.MaxD2 Certificates.MaxD2Perm

variable {D : Data} {w kG : Nat} {Gp GIp : Nat → Nat}

theorem checkInv_ofM (hGs : D.gT.size = kG) (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hGp : allN kG (fun j => permOK D.n w (mask w) (D.n * w) (Gp j) (GIp j)) = true) :
    checkInv D = true := by
  unfold checkInv
  rw [allBelow_iff']
  intro j hj
  have hj' : j < kG := by rw [← hGs]; exact hj
  have hp := (PK.allN_iff.1 hGp) j hj'
  have hgi : (giT D)[j]! = unpack D.n w (GIp j) := by
    unfold giT
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, ← getElem!_pos D.gT j hj,
      hGb j hj', inv_u hp]
  rw [hgi, hGb j hj', inv_comp hp]
  simp [size_u]

theorem wT_bindM (hGs : D.gT.size = kG) (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hGp : allN kG (fun j => permOK D.n w (mask w) (D.n * w) (Gp j) (GIp j)) = true)
    {wd : List Int} {r : Nat} (h : wordEqK D.n w (mask w) (pidn D.n w) Gp GIp kG wd r = true) :
    wT D wd = unpack D.n w r := by
  unfold wT giT
  exact wordT_u ⟨hGs, hGb⟩ hGp h

theorem nGens_bindM (hGs : D.gT.size = kG) (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hGp : allN kG (fun j => permOK D.n w (mask w) (D.n * w) (Gp j) (GIp j)) = true)
    {kN : Nat} {NG : Nat → Nat} (hk : D.nW.length = kN)
    (h : ∀ j < kN, wordEqK D.n w (mask w) (pidn D.n w) Gp GIp kG (D.nW[j]!) (NG j) = true ∧
      Cn D.n w (NG j)) :
    GensOK D.n w kN NG (nGens D) := by
  refine ⟨by simp [nGens, hk], fun j hj => ⟨?_, (h j hj).2⟩⟩
  unfold nGens
  rw [map_get _ (by rw [hk]; exact hj), wT_bindM hGs hGb hGp (h j hj).1]

theorem checkN_ofM {cnt : Nat} {T PL : Nat → Nat}
    (hE : enumBFS D.n (nGens D) D.nOrder = penumRec D.n w cnt T PL ∧
      enumOK D.n (nGens D) (penumRec D.n w cnt T PL) = true) (hc : cnt = D.nOrder) :
    checkN D = true := by
  unfold checkN nEnum
  rw [hE.1, hE.2, rec_size, hc]
  simp

theorem invsN_ofM {kN : Nat} {NG NGI : Nat → Nat} (hgN : GensOK D.n w kN NG (nGens D))
    (hNI : ∀ j < kN, permOK D.n w (mask w) (D.n * w) (NG j) (NGI j) = true) :
    invsOK D.n (nGens D) (nGensI D) = true := by
  have hs : (nGens D).size = kN := hgN.1
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [nGensI], allBelow_iff'.2 fun k hk => ?_⟩
  rw [hs] at hk
  have hngi : (nGensI D)[k]! = unpack D.n w (NGI k) := by
    unfold nGensI
    rw [getElem!_pos _ k (by simpa [hs] using hk), Array.getElem_map,
      ← getElem!_pos (nGens D) k (by rw [hs]; exact hk), (hgN.2 k hk).1, inv_u (hNI k hk)]
  rw [hngi, (hgN.2 k hk).1, inv_comp (hNI k hk)]
  simp [size_u]

section

variable {nr : Nat} {REP REPI : Nat → Nat}

theorem repT_bindM (hn : szOK D.n w = true) (hGs : D.gT.size = kG)
    (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hGp : allN kG (fun j => permOK D.n w (mask w) (D.n * w) (Gp j) (GIp j)) = true)
    (hnr : nr = D.repW.length + 1) (hR0 : REP 0 = pidn D.n w)
    (hRw : ∀ i < D.repW.length,
      wordEqK D.n w (mask w) (pidn D.n w) Gp GIp kG (D.repW[i]!) (REP (i + 1)) = true) :
    RepB D.n w nr REP (repT D) := by
  have e : repT D = (idTab D.n :: D.repW.map (wT D)).toArray := by simp [repT]
  refine ⟨by simp [repT, hnr], fun i hi => ?_⟩
  rw [e, getElem!_pos _ i (by simp; omega)]
  rcases i with _ | j
  · simp [hR0, id_u hn]
  · have hj : j < D.repW.length := by omega
    simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_map]
    rw [← getElem!_pos D.repW j hj]
    exact wT_bindM hGs hGb hGp (hRw j hj)

theorem repI_bindM (hr : RepB D.n w nr REP (repT D))
    (hRi : ∀ i < nr, permOK D.n w (mask w) (D.n * w) (REP i) (REPI i) = true) :
    RepB D.n w nr REPI (repI D) := by
  refine ⟨by simp [repI, hr.1], fun i hi => ?_⟩
  unfold repI
  rw [getElem!_pos _ i (by simpa [hr.1] using hi), Array.getElem_map,
    ← getElem!_pos (repT D) i (by rw [hr.1]; exact hi), hr.2 i hi, inv_u (hRi i hi)]

theorem dcGenerate_ofM {kN : Nat} {NG NGI : Nat → Nat} (hn : szOK D.n w = true)
    (hGs : D.gT.size = kG) (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hgN : GensOK D.n w kN NG (nGens D))
    (hNI : ∀ j < kN, permOK D.n w (mask w) (D.n * w) (NG j) (NGI j) = true)
    (hr : RepB D.n w nr REP (repT D)) (hri : RepB D.n w nr REPI (repI D))
    (hRi : ∀ i < nr, permOK D.n w (mask w) (D.n * w) (REP i) (REPI i) = true)
    (hnr : nr = D.repW.length + 1) (hgl : D.genW.length = D.repW.length)
    (hGen : ∀ i < D.repW.length, (D.genW[i]!).length = kG ∧ ∀ j < kG,
      wordEqK D.n w (mask w) (pidn D.n w) (fun l => nIf(Nat.blt l kN, NG l, REP (i + 1)))
        (fun l => nIf(Nat.blt l kN, NGI l, REPI (i + 1))) (kN + 1) ((D.genW[i]!)[j]!) (Gp j) =
        true) :
    dcGenerate D (repT D) (repI D) = true := by
  have hs : (nGens D).size = kN := hgN.1
  unfold dcGenerate
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨hgl, allBelow_iff'.2 fun i hi => ?_⟩
  have hi1 : i + 1 < nr := by rw [hnr]; omega
  obtain ⟨hl, hw⟩ := hGen i hi
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by rw [hl, hGs], allBelow_iff'.2 fun j hj => ?_⟩
  rw [hGs] at hj
  have hgi : nGensI D ++ #[(repI D)[i + 1]!] =
      (nGens D ++ #[(repT D)[i + 1]!]).map (invTab D.n) := by
    rw [Array.map_append]
    congr 1
    unfold repI
    rw [getElem!_pos _ (i + 1) (by simp [hr.1]; exact hi1), Array.getElem_map,
      ← getElem!_pos (repT D) (i + 1) (by rw [hr.1]; exact hi1)]
    simp
  have hga : (nGens D ++ #[(repT D)[i + 1]!]).size = kN + 1 ∧ ∀ l < kN + 1,
      (nGens D ++ #[(repT D)[i + 1]!])[l]! =
        unpack D.n w (nIf(Nat.blt l kN, NG l, REP (i + 1))) := by
    refine ⟨by simp [hs], fun l hl => ?_⟩
    rw [getElem!_pos _ l (by simp [hs]; omega)]
    by_cases h : l < kN
    · rw [Array.getElem_append_left (by rw [hs]; exact h),
        ← getElem!_pos (nGens D) l (by rw [hs]; exact h), (hgN.2 l h).1, PK.nIf_eq,
        if_pos (Nat.blt_eq.mpr h)]
    · have hl' : l = kN := by omega
      subst hl'
      rw [PK.nIf_eq, if_neg (by simp [Nat.blt_eq]), Array.getElem_append_right (by rw [hs])]
      simp [hs, hr.2 (i + 1) hi1]
  have hperm : allN (kN + 1) (fun l => permOK D.n w (mask w) (D.n * w)
      (nIf(Nat.blt l kN, NG l, REP (i + 1))) (nIf(Nat.blt l kN, NGI l, REPI (i + 1)))) = true :=
    PK.allN_iff.2 fun l hl => by
      by_cases h : l < kN
      · rw [PK.nIf_eq, PK.nIf_eq, if_pos (Nat.blt_eq.mpr h), if_pos (Nat.blt_eq.mpr h)]
        exact hNI l h
      · rw [PK.nIf_eq, PK.nIf_eq, if_neg (by simp [Nat.blt_eq]; omega),
          if_neg (by simp [Nat.blt_eq]; omega)]
        exact hRi _ hi1
  rw [hgi, wordT_u hga hperm (hw j hj), hGb j hj]
  exact beq_self_eq_true _

end

theorem checkMax_ofM {C : Pk} (H : HypsC C D.fpPts D.nOrder D.gOrder) (hCn : C.n = D.n)
    (hEN : nEnum D = penumRec C.n C.w C.cnt C.NT C.NPL)
    (hr : RepB C.n C.w C.nr C.REP (repT D)) (hri : RepB C.n C.w C.nr C.REPI (repI D))
    (hgen : dcGenerate D (repT D) (repI D) = true) :
    checkMax D = true := by
  unfold checkMax
  dsimp only
  rw [hEN, ← hCn, fpOK_of (fp_injC H), invsOK_ofC H hr hri, dcSum_ofC H hr hri,
    dcDisjoint_ofC H hr hri, hgen]
  simp

end CFSG.KS.TitsOver

end
