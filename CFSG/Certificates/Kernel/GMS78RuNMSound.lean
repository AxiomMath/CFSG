module

public import Certificates.Data.Kernel.GMS78RuNM
public import CFSG.Certificates.Kernel.GMS78RuGenN
import CFSG.Certificates.Kernel.GMS78RuNMGlue

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuN

theorem packV_linId : packV linId = LINID := by decide +kernel

theorem maskAppK_two_pow (A : Nat) {k : Nat} (hk : k < 8) : maskAppK A (2 ^ k) = fget A k 8 := by
  rw [NG.maskAppK_eq, NG.selN_two_pow _ hk]

theorem inv_closed : (glList.all fun r => glList.contains (linInv r) && linComp (linInv r) r == linId &&
    linComp r (linInv r) == linId) = true := by
  decide +kernel

theorem trans_closed : ((List.finRange 8).all fun t => (List.finRange 8).all fun t' =>
    t == 0 || t' == 0 || glList.any fun s => linApply s t == t') = true := by
  decide +kernel

theorem idx_mem {r : Lin8} (hr : r ∈ glList) :
    glList.idxOf r < 168 ∧ glList.getD (glList.idxOf r) linId = r := by
  have hl := List.idxOf_lt_length_of_mem hr
  rw [NG.glList_length] at hl
  refine ⟨hl, ?_⟩
  rw [NG.getD_of_lt _ _ (by rw [NG.glList_length]; exact hl), List.getElem_idxOf]

theorem valid_of {p : NTrip} (hp : p.1 < 256) (hg : glK (trR (packT p)) = true) : nValid p = true := by
  obtain ⟨m, t, r⟩ := p
  simp only at hp
  rw [(NG.tr_pack m t r hp).2.2] at hg
  simp only [nValid, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hp, List.contains_iff_mem.2 (NG.Facts.mem r hg)⟩

public section

theorem nm_sound (nbt ntw : List (List (Fin 8))) (nc nb sb : List Nat) (dct : List (Fin 8 × Fin 8 × Fin 8))
    (img imgInv rT : List (Nat × Fin 8 × (Fin 8 × Fin 8 × Fin 8))) (rels rW kW : List (List Nat))
    (a0 : List (List (Fin 7 × Bool))) {GLL TW ADC TAU INV FW NIMG NIMGI NRT : Nat}
    (hN : bindNC sb nbt nc nb dct ntw = true) (hI : invTabOK INV = true) (hG : gllOK GLL = true)
    (hT : bindTW ntw GLL TW = true) (hB : bindImg img imgInv rT NIMG NIMGI NRT = true)
    (hRT : smallM rT = true)
    (hZ : zeroOK ADC TAU = true) (hR : ∀ i < 168, nmR GLL INV TW ADC TAU (gllAt GLL i) = true)
    (hId : kId GLL INV ADC TAU = true) (hF : kFaith FW = true) (hIm : kImg ADC TAU NIMG NIMGI = true)
    (hRel : kRel rels ADC TAU NIMG NIMGI = true) (hClo : kClo rW kW GLL ADC TAU NIMG NIMGI NRT = true)
    (hA0 : kA0 a0 ADC TAU NIMG NIMGI = true) :
    Gen.nQuadCheck nbt ntw nc nb = true ∧ Gen.nCompCheck nbt ntw nc nb = true ∧
      Gen.nIdCheck nbt ntw nc nb = true ∧ Gen.nFaithCheck nbt nc = true ∧
      Gen.nImgCheck nbt ntw nc nb img imgInv = true ∧
      Gen.nRelCheck nbt ntw nc nb img imgInv rels = true ∧
      Gen.nCloCheck nbt ntw nc nb img imgInv rW kW rT = true ∧
      Gen.nA0Check nbt ntw nc nb img imgInv a0 = true := by
  obtain ⟨-, hNBT, hNC, hNB, -, -⟩ := NG.bindNC_facts hN
  have hGLL := NG.gll_eq hG
  have hGr : ∀ r ∈ glList, gllAt GLL (glList.idxOf r) = packV r := fun r hr => by
    rw [hGLL _ (idx_mem hr).1, (idx_mem hr).2]
  obtain ⟨hTl, hTW⟩ := NG.recIdx (P := fun row i => bindFin8 row (fget TW (gllAt GLL i) 24) 8) hT
  have F : NG.Facts nbt ntw nc nb GLL TW ADC TAU INV :=
    { hNBT := hNBT, hNC := hNC, hNB := hNB, hI := hI,
      hTW := fun r hr j hj => by
        have hi := (idx_mem hr).1
        rw [NG.getD_of_lt ntw [] (by rw [hTl]; exact hi)]
        rw [← hGr r hr]
        exact NG.bindFin8_getD (hTW _ (by rw [hTl]; exact hi)) hj
      hR := fun r hr => by rw [← hGr r hr]; exact hR _ (idx_mem hr).1
      hZ := hZ }
  obtain ⟨hI1, hI2, hRTl, hRTp⟩ := NG.bindImg_facts hB
  simp only [kId, NG.strictB_eq] at hId
  obtain ⟨hId1, hId⟩ := NG.andB_true hId
  obtain ⟨-, hId3⟩ := NG.andB_true hId
  have hid : ∀ m < 256, maskAppK NBAS (maskAppK NCOLS m) = m := fun m hm =>
    Nat.eq_of_beq_eq_true (NG.andB_true (NG.andB_true (NG.allN_of hId1 hm)).2).2
  have hnB : ∀ j < 8, Gen.nB nb j = fget NBAS j 8 := fun j hj => hNB j hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Gen.nQuadCheck, List.all_eq_true, List.mem_range, beq_iff_eq]
    intro r hr m hm j hj
    rw [hnB j hj]
    have hb := NG.fget_lt NBAS j 8
    have hmb : m ^^^ fget NBAS j 8 < 256 := Nat.xor_lt_two_pow (n := 8) hm hb
    apply Fin.ext
    rw [NG.fxor_val, NG.fxor_val, NG.fxor_val, NG.tauTab_val F r hmb, NG.tauTab_val F r hm,
      NG.tauTab_val F r hb, NG.linApply_val, NG.betaArr_val F (NG.adTab_lt F r hm) (NG.adTab_lt F r hb),
      NG.betaArr_val F hm hb, NG.adTab_eq F r hm, NG.adTab_eq F r hb]
    obtain ⟨-, hT⟩ := NG.rOK_facts (F.rok hr)
    have hq := (NG.andB_true (NG.andB_true (F.hR r hr)).2).1
    simp only [kQuad, NG.strictB_eq] at hq
    rw [hT _ hmb, hT _ hm, hT _ hb]
    refine NG.quad_of (A := fget ADC (packV r) 64) (fun i hi j' hj' => ?_) hid hm hj
    have e := Nat.eq_of_beq_eq_true (NG.allN_of (NG.allN_of hq hi) hj')
    have hi8 := NG.fget_lt NBAS i 8
    have hj8 := NG.fget_lt NBAS j' 8
    rw [← hT _ (Nat.xor_lt_two_pow (n := 8) hi8 hj8), ← hT _ hi8, ← hT _ hj8]
    exact e
  · simp only [Gen.nCompCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
    intro r hr s hs k hk
    have hc := (NG.andB_true (NG.andB_true (F.hR r hr)).2).2
    simp only [kComp, NG.strictB_eq] at hc
    have hcs := NG.allN_of hc (idx_mem hs).1
    rw [hGr s hs, NG.linComp_pack] at hcs
    obtain ⟨e1, e2⟩ := NG.andB_true (NG.allN_of hcs hk)
    have hk2 : 2 ^ k < 256 := Nat.pow_lt_pow_right (by decide) hk
    have hb := NG.fget_lt NBAS k 8
    have hsb := NG.adTab_lt F s hb
    refine ⟨?_, ?_⟩
    · rw [NG.adTab_eq F _ hk2, NG.adTab_eq F _ (NG.adTab_lt F s hk2), NG.adTab_eq F _ hk2]
      simp only [adA]
      rw [maskAppK_two_pow _ hk, maskAppK_two_pow _ hk]
      exact Nat.eq_of_beq_eq_true e1
    · rw [hnB k hk]
      apply Fin.ext
      rw [NG.fxor_val, NG.tauTab_val F _ hb, NG.tauTab_val F _ hsb, NG.linApply_val, NG.tauTab_val F _ hb,
        NG.adTab_eq F _ hb]
      exact Nat.eq_of_beq_eq_true e2
  · rw [Gen.nIdCheck, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, inv_closed⟩, ?_⟩
    · rw [List.all_eq_true]
      intro m hm
      rw [List.mem_range] at hm
      obtain ⟨h1, h⟩ := NG.andB_true (NG.allN_of hId1 hm)
      obtain ⟨h2, -⟩ := NG.andB_true h
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [NG.adTab_eq F _ hm, packV_linId]
        exact Nat.eq_of_beq_eq_true h1
      · apply Fin.ext
        rw [NG.tauTab_val F _ hm, packV_linId]
        exact Nat.eq_of_beq_eq_true h2
      · rw [NG.maskApply_eq_maskAppK hNB, NG.coArr_eq F hm]
        exact hid m hm
    · rw [List.all_eq_true]
      intro r hr
      rw [List.all_eq_true]
      intro s hs
      have := NG.allN_of (NG.allN_of hId3 (idx_mem hr).1) (idx_mem hs).1
      rw [hGr r hr, hGr s hs, NG.linComp_pack] at this
      exact List.contains_iff_mem.2 (NG.Facts.mem _ this)
  · rw [Gen.nFaithCheck, Bool.and_eq_true]
    refine ⟨?_, trans_closed⟩
    rw [List.all_eq_true]
    intro m hm
    rw [List.mem_range] at hm
    simp only [kFaith] at hF
    obtain ⟨hF1, -⟩ := NG.andB_true hF
    obtain ⟨h1, h2⟩ := NG.andB_true (NG.allN_of hF1 hm)
    have hn : fget FW m 8 < 256 := Nat.le_of_ble_eq_true h1
    rw [List.any_eq_true]
    refine ⟨fget FW m 8, List.mem_range.2 hn, ?_⟩
    rw [bne_iff_ne]
    intro e
    have e' := congrArg Fin.val e
    rw [NG.betaArr_val F (by omega) hn, NG.betaArr_val F hn (by omega)] at e'
    rw [NG.notB_eq, e', Nat.beq_refl] at h2
    exact absurd h2 (by decide)
  · rw [Gen.nImgCheck, List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    simp only [kImg] at hIm
    obtain ⟨g1, h⟩ := NG.andB_true (NG.allN_of hIm hi)
    obtain ⟨g2, g3⟩ := NG.andB_true h
    obtain ⟨p1, p2⟩ := hI1 i hi
    obtain ⟨q1, q2⟩ := hI2 i hi
    rw [← p1] at g1
    rw [← q1] at g2
    rw [← p1, ← q1, (NG.mulT_pack F _ _ p2 q2).1, NG.ONET_eq] at g3
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨valid_of p2 g1, valid_of q2 g2⟩,
      NG.packT_inj (NG.mulT_pack F _ _ p2 q2).2 (by decide) (Nat.eq_of_beq_eq_true g3)⟩
  · rw [Gen.nRelCheck, List.all_eq_true]
    intro w hw
    have e := Nat.eq_of_beq_eq_true (NG.recAll (P := fun w => Nat.beq (evalC ADC TAU NIMG NIMGI w) ONET) hRel w hw)
    obtain ⟨h1, h2⟩ := NG.evalC_pack F hI1 hI2 w nOneT (by decide)
    rw [NG.evalC_eq, NG.ONET_eq, h1] at e
    rw [beq_iff_eq]
    exact NG.packT_inj h2 (by decide) e
  · simp only [kClo] at hClo
    obtain ⟨c1, c2⟩ := NG.andB_true hClo
    obtain ⟨l1, c1⟩ := NG.recIdx (P := fun w i => Nat.beq (evalC ADC TAU NIMG NIMGI w) (fget NRT i 20)) c1
    obtain ⟨l2, c2⟩ := NG.recIdx
      (P := fun w i => Nat.beq (evalC ADC TAU NIMG NIMGI w) (Nat.shiftLeft (gllAt GLL i) 11)) c2
    rw [Gen.nCloCheck, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [List.mem_range] at hi
      have hi' : i < rW.length := by rw [l1]; exact hi
      have e := Nat.eq_of_beq_eq_true (c1 i hi')
      obtain ⟨h1, h2⟩ := NG.evalC_pack F hI1 hI2 rW[i] nOneT (by decide)
      rw [NG.evalC_eq, NG.ONET_eq, h1, ← hRTp i hi] at e
      rw [NG.getD_of_lt rW [] hi', beq_iff_eq]
      exact NG.packT_inj h2 (NG.smallM_spec hRT _ (NG.getD_mem _ (by rw [hRTl]; exact hi))) e
    · rw [List.mem_range] at hi
      have hi' : i < kW.length := by rw [l2]; exact hi
      have e := Nat.eq_of_beq_eq_true (c2 i hi')
      obtain ⟨h1, h2⟩ := NG.evalC_pack F hI1 hI2 kW[i] nOneT (by decide)
      rw [NG.evalC_eq, NG.ONET_eq, h1, hGLL i hi] at e
      have e2 : Nat.shiftLeft (packV (glList.getD i linId)) 11 = packT (0, 0, glList.getD i linId) := by
        rw [NG.packT_eq _ _ _ (by decide), Nat.shiftLeft_eq']
        rw [Nat.shiftLeft_eq]
        have h11 : (2 : Nat) ^ 11 = 2048 := rfl
        rw [h11]
        simp only [Fin.val_zero]
        omega
      rw [e2] at e
      rw [NG.getD_of_lt kW [] hi', beq_iff_eq]
      exact NG.packT_inj h2 (Nat.zero_lt_succ 255) e
  · rw [Gen.nA0Check, List.all_eq_true]
    intro w hw
    have h := NG.recAll (P := fun w => (fun P => andB (Nat.beq (trM P) 0) (Nat.beq (trR P) LINID))
      (evalS ADC TAU NIMG NIMGI w)) hA0 w hw
    obtain ⟨h1, h2⟩ := NG.evalS_pack F hI1 hI2 w nOneT (by decide)
    rw [NG.evalS_eq, NG.ONET_eq, h1] at h
    obtain ⟨e1, e2⟩ := NG.andB_true h
    generalize hX : w.foldl (fun x p => Gen.nMulT nbt ntw nc nb x (Gen.nSign img imgInv p)) nOneT = X at h2 e1 e2
    obtain ⟨m, t, r⟩ := X
    simp only at h2
    obtain ⟨t1, -, t3⟩ := NG.tr_pack m t r h2
    rw [t1] at e1
    rw [t3] at e2
    have hX' : Gen.nEvalW nbt ntw nc nb img imgInv w = (m, t, r) := hX
    simp only [hX', Bool.and_eq_true, beq_iff_eq]
    exact ⟨Nat.eq_of_beq_eq_true e1, NG.packV_inj ((Nat.eq_of_beq_eq_true e2).trans packV_linId.symm)⟩

end

end CFSG.KC.GMS
