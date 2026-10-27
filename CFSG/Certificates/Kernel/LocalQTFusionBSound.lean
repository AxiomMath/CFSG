module

public import Certificates.Data.Kernel.LocalQT.FusionB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion
import CFSG.Certificates.Kernel.LocalQTFusionSSound
import CFSG.Certificates.Kernel.LocalQTEnumAProved
import CFSG.Certificates.Kernel.LocalQTFusionBReg

public section

namespace CFSG.KC.LQT.FB.Pf

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.BS CFSG.KC.LQT.RW CFSG.KC.LQT.RB
open CFSG.KC.LQT.FS CFSG.KC.LQT.FB CFSG.KC.LQT.BSP
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BS.Pf CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf CFSG.KC.LQT.FS.Pf
open CFSG.KC.LQT.BW.App CFSG.KC.LQT.FB.Reg CFSG.KC.LQT.BW.Cl
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2 CFSG.QuasithinUnique.Lin2.RankCert
open CFSG.QuasithinUnique.Lin2.FusionCert
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

private theorem head {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat)
    (hta : tabL n ta = true) (htb : tabL n tb = true) (hso : slpOKK prog 2 = true)
    (hTF0 : Nat.beq (TF 0) (codeK w ta) = true) (hTF1 : Nat.beq (TF 1) (codeK w tb) = true)
    (hKm : Nat.ble (Nat.add (lenA prog) 2) (Nat.mul K m) = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true) :
    (slpTabsA ta.toArray tb.toArray prog).size = prog.length + 2 ∧
    ∀ j < (slpTabsA ta.toArray tb.toArray prog).size,
      Rep n w (TF j) (slpTabsA ta.toArray tb.toArray prog)[j]! := by
  have hnodes : ∀ q < prog.length, TF (2 + q) =
      mulW n w (TF (prog.getD q (0, 0)).1) (TF (prog.getD q (0, 0)).2) := by
    intro q hq
    have hKm' := Nat.le_of_ble_eq_true hKm
    rw [lenA_eq, Nat.add_eq, Nat.mul_eq] at hKm'
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, Nat.mul_zero] at hKm'
        omega
      · exact h0
    have hc : (2 + q) / m < K := by
      rw [Nat.div_lt_iff_lt_mul hm0]
      omega
    have := allR_true (hnd _ hc) ((2 + q) % m) (Nat.mod_lt _ hm0)
    rw [Nat.div_add_mod'] at this
    dsimp only at this
    have h2 : CFSG.KC.Ord.andB (Nat.ble 2 (2 + q)) (Nat.blt (2 + q) (Nat.add (lenA prog) 2)) = true := by
      rw [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, lenA_eq, Nat.add_eq]
      constructor <;> omega
    have := impB_true this h2
    rw [P.beq_iff, nthP_eq, show Nat.sub (2 + q) 2 = q by rw [Nat.sub_eq]; omega] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [slpTabsA, foldl_slpStepA_size]
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    omega
  · rw [slpTabsA]
    apply slpTF_rep prog #[ta.toArray, tb.toArray]
    · intro j hj
      rcases j with _ | _ | j
      · rw [P.beq_iff.1 hTF0]
        exact rep_codeK hw hta
      · rw [P.beq_iff.1 hTF1]
        exact rep_codeK hw htb
      · simp at hj
    · exact slpOKK_spec' prog 2 hso
    · intro q hq
      exact hnodes q hq

private theorem core {n w : Nat} (hw : n ≤ 2 ^ w) (W : Nat) (B ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat)
    (k fuel dd zi PK CK RP RC : Nat) (PT CT : Nat → Nat) (ZT : Nat) (TS : Nat → Nat)
    (wits : List (List Nat × List Nat × Nat)) (gws : List (List Nat)) (s R : Nat)
    (CP : Nat → Nat)
    (h : fusBH n w W B ta tb prog qp TF K m RS RT k fuel dd zi PK CK RP RC PT CT ZT TS wits gws =
      true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true)
    (hcp : ∀ q < (wordsOf wits).length * R, wordCk n w (TF 0) (TF 1) (wordsOf wits) s R CP q = true)
    (hwit : ∀ j < wits.length, fusBW n w B qp TF ZT TS wits s R CP j = true) :
    FusionCert.FusionCertS n B ta.toArray tb.toArray prog qp
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k zi wits gws := by
  rw [fusBH] at h
  dsimp only at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hTF0, hTF1, hKm, hRS, hqpb, hqinv, hB, hrows, hBE⟩ := h
  obtain ⟨hTs, hRepT⟩ := head hw B ta tb prog qp TF K m RS RT hta htb hso hTF0 hTF1 hKm hnd
  have hRa : Rep n w (TF 0) ta.toArray := by rw [P.beq_iff.1 hTF0]; exact rep_codeK hw hta
  have hRb : Rep n w (TF 1) tb.toArray := by rw [P.beq_iff.1 hTF1]; exact rep_codeK hw htb
  unfold FusionCert.FusionCertS
  generalize slpTabsA ta.toArray tb.toArray prog = T at hTs hRepT ⊢
  have hNT : Nat.add (lenA prog) 2 = T.size := by rw [hTs, lenA_eq, Nat.add_eq]
  rw [hNT] at hqpb
  rw [allA_eq, List.all_eq_true] at hqpb hqinv
  have hq1' : ∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size := by
    intro p hp
    have := hqpb p hp
    rw [andB_eq, Bool.and_eq_true, P.blt_iff, P.blt_iff] at this
    exact this
  rw [allL_eq, List.all_eq_true] at hB
  have hB' : ∀ b ∈ B, b < n := fun b hb => P.blt_iff.1 (hB b hb)
  have hqinvT : ∀ p ∈ qp, ∀ x < n, img T[p.2]! (img T[p.1]! x) = x := by
    intro p hp x hx
    have e : mulW n w (TF p.2) (TF p.1) = oneW n w := P.beq_iff.1 (hqinv p hp)
    have h2 := fr_rep (hRepT p.2 (hq1' p hp).2)
    have h1 := fr_rep (hRepT p.1 (hq1' p hp).1)
    have h3 := (fr_mul h2 h1 x hx).1
    rw [e, (fr_one hw x hx).1] at h3
    exact h3.symm
  set G := qp.map fun p => T[p.1]! with hGdef
  set Gi := qp.map fun p => T[p.2]! with hGidef
  have hGl : G.length = qp.length := by rw [hGdef, List.length_map]
  have hGil : Gi.length = qp.length := by rw [hGidef, List.length_map]
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGij : ∀ j (hj : j < qp.length), Gi[j]! = T[qp[j].2]! := by
    intro j hj
    rw [getElem!_pos Gi j (by omega)]
    simp only [hGidef, List.getElem_map]
  have hfor : ∀ l : List (Nat × Nat), (∀ p ∈ l, p.1 < T.size) →
      List.Forall₂ (fun c s => Rep n w c s) (l.map fun p => TF p.1) (l.map fun p => T[p.1]!) := by
    intro l hl
    induction l with
    | nil => exact List.Forall₂.nil
    | cons p l ih =>
      exact List.Forall₂.cons (hRepT _ (hl p (List.mem_cons_self ..)))
        (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
  have hpts : ptsW w B (fstT TF qp) = ptsOf B G := by
    rw [fstT_eq]
    exact ptsW_eq hB' (hfor qp fun p hp => (hq1' p hp).1)
  have hRS' : n ≤ 64 * RS := Nat.le_of_ble_eq_true hRS
  have hrowsT : ∀ t (ht : t < qp.length), ∀ k' < RS,
      RT (t * RS + k') = rowW w (TF qp[t].1) k' := by
    intro t ht k' hk'
    have := rowsT_go (fstT TF qp) 0 hrows t (by rw [fstT_eq, List.length_map]; exact ht) k' hk'
    rw [Nat.zero_add, fstT_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht] at this
    exact this
  have hGrepj : ∀ t (ht : t < qp.length), Rep n w (TF qp[t].1) G[t]! := by
    intro t ht
    rw [hGj t ht]
    exact hRepT _ (hq1' _ (List.getElem_mem ht)).1
  rw [fusBE] at hBE
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hBE
  obtain ⟨hE, hpar, hcl, hPK, hCK, hRP, hRC, hZT, hfq⟩ := hBE
  rw [hpts, lenA_eq, lenA_eq, rangeK_eq'] at hE hpar hcl hPK hCK hRP hRC hZT hfq
  set Gp : List (Nat × Array Nat) := (List.range qp.length).map fun t => (t, G[t]!) with hGpdef
  have hGs : Gp.map Prod.snd = G := by
    rw [hGpdef, List.map_map]
    apply List.ext_getElem (by simp [hGl])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Function.comp]
    exact getElem!_pos G i h2
  have hGf : Gp.map Prod.fst = List.range qp.length := by
    rw [hGpdef, List.map_map]
    exact List.map_id' _
  have hAR : ∀ p ∈ Gp, AR n (imgsR w RS RT) p.1 p.2 := by
    intro p hp
    rw [hGpdef, List.mem_map] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    have ht' := List.mem_range.1 ht
    exact ⟨fun q hq => ((hGrepj t ht').2 q hq).1, fun l hl =>
      imgsR_rep hRS' (hrowsT t ht') (hGrepj t ht') hl⟩
  have hinv : ∀ j < G.length, ∀ q < n, img Gi[j]! (img G[j]! q) = q := by
    intro j hj q hq
    rw [hGj j (by omega), hGij j (by omega)]
    exact hqinvT _ (List.getElem_mem _) q hq
  generalize hEd : enumW w B.length qp.length (imgsR w RS RT) (List.range qp.length)
    (ptsOf B G) dd = E at hE hpar hcl hPK hCK hRP hRC hZT hfq
  have hEd' : enumW w B.length G.length (imgsR w RS RT) (Gp.map Prod.fst) (ptsOf B G) dd = E := by
    rw [hGf, hGl]
    exact hEd
  obtain ⟨hbe, hsz, hcnt, hpl, hparE, hcll, hclE, hval, hXr⟩ :=
    enumA_bfs hw hB' hAR hGs (by rw [hGl, hGil]) hinv _ rfl E hEd' hE
  generalize bfsEnumB n B G Gi fuel = X at hbe hsz hcnt hpl hparE hcll hclE hval hXr ⊢
  rw [hcnt] at hRP hRC hZT hfq
  rw [hGl] at hcll hclE
  have hPK' : PK = codeK W E.1.par.reverse := by
    rw [P.beq_iff, revOn_eq, List.append_nil] at hPK
    exact hPK
  have hCK' : CK = codeK W E.1.cl.reverse := by
    rw [P.beq_iff, revOn_eq, List.append_nil] at hCK
    exact hCK
  have hparlt : ∀ x ∈ E.1.par.reverse, x < 2 ^ W := fun x hx =>
    allL_lt hpar x (List.mem_reverse.1 hx)
  have hcllt : ∀ x ∈ E.1.cl.reverse, x < 2 ^ W := fun x hx =>
    allL_lt hcl x (List.mem_reverse.1 hx)
  have hfPall : ∀ i < X.1.size, fieldT W PT i = X.2.1[i]! := by
    intro i hi
    rw [field_code hRP hPK' hparlt (by rw [List.length_reverse, hpl]) hi, hparE i hi]
  have hfC : ∀ i < X.1.size, ∀ j < qp.length,
      fieldT W CT (i * (qp.length + qp.length) + j) = X.2.2[i * (qp.length + qp.length) + j]! := by
    intro i hi j hj
    have hRC' : rowsOK W (X.1.size * (qp.length + qp.length)) RC CK CT = true := hRC
    rw [field_code hRC' hCK' hcllt (by rw [List.length_reverse, hcll]) (pos_lt hi (by omega)),
      hclE i hi j hj]
  have hbe' := hbe
  obtain ⟨hM, hX0, -, hparB, hkeys, hstepG, -⟩ := hbe'
  rw [hGl, hGil] at hstepG
  have hfP : ∀ i < X.1.size, 0 < i → fieldT W PT i = X.2.1[i]! := fun i hi _ => hfPall i hi
  have hpar' : ∀ i < X.1.size, 0 < i → X.2.1[i]! < i ∧ 0 < qp.length := by
    intro i hi hi0
    obtain ⟨h1, s', hs', -⟩ := hparB i hi hi0
    refine ⟨h1, ?_⟩
    rw [← hGl]
    exact List.length_pos_of_mem hs'
  have hcl' : ∀ i < X.1.size, ∀ j < qp.length, X.2.2[i * (qp.length + qp.length) + j]! < X.1.size :=
    fun i hi j hj => (hstepG i hi j (by omega)).1
  have hmulS := mulG_spec' (N := X.1.size) (g := qp.length) (gi := qp.length) (par := X.2.1)
    (cl := X.2.2) (fP := fieldT W PT) (fC := fieldT W CT) hfP hfC hpar' hcl' X.1.size
  have hmT : ∀ i < X.1.size, ∀ k < X.1.size, mulT W qp.length X.1.size PT CT i k =
      mulIdx qp.length qp.length X.2.1 X.2.2 X.1.size i k ∧
      mulIdx qp.length qp.length X.2.1 X.2.2 X.1.size i k < X.1.size :=
    fun i hi k hk => hmulS i k hi hk
  have hcj : ∀ j < qp.length, X.2.2[j]! = fieldT W CT j := by
    intro j hj
    have := hfC 0 hM j hj
    rw [Nat.zero_mul, Nat.zero_add] at this
    exact this.symm
  have hcjlt : ∀ j < qp.length, fieldT W CT j < X.1.size := by
    intro j hj
    have := hcl' 0 hM j hj
    rw [Nat.zero_mul, Nat.zero_add, hcj j hj] at this
    exact this
  have hGlt : ∀ t < G.length, ∀ y < n, img G[t]! y < n := by
    intro t ht y hy
    exact ((hGrepj t (by omega)).2 y hy).1
  have hov : ∀ x ∈ ptsOf B G, x < n := by
    intro x hx
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s', hs, hx⟩
    · exact hB' x hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
      rw [← getElem!_pos G t ht]
      exact hGlt t ht b (hB' b hb)
  have hGrep : ∀ j < qp.length, Rep n w (genW n w (fstT TF qp) j) (G.getD j #[]) := by
    intro j hj
    have e1 : (fstT TF qp).getD j (oneW n w) = TF qp[j].1 := by
      rw [fstT_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
      rfl
    have e2 : G.getD j #[] = T[qp[j].1]! := by
      rw [List.getD_eq_getElem?_getD, hGdef, List.getElem?_map, List.getElem?_eq_getElem hj]
      rfl
    rw [genW_eq, e1, e2]
    exact hRepT _ (hq1' _ (List.getElem_mem hj)).1
  rw [fusQ] at hfq
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hfq
  obtain ⟨hzM, hz0, hzz, hzc, hcov, hwb, hgws⟩ := hfq
  have hzlt : zi < X.1.size := P.blt_iff.1 hzM
  have hZrep : Rep n w ZT (idxTab n G qp.length qp.length X.2.1 X.2.2 X.1.size zi) := by
    rw [P.beq_iff.1 hZT]
    exact idx_rep hw hGrep hfP hfC hpar' X.1.size zi hzlt
  have hwI : ∀ j (hj : j < wits.length), getK (witIdx wits) j = wits[j].2.2 := by
    intro j hj
    rw [getK_eq, witIdx_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hj]
    rfl
  have hTsL : ∀ c < X.1.size, getLL (revOn E.1.rev []) c = X.1[c]! := by
    intro c hc
    rw [getLL_eq, revOn_eq, List.append_nil, ← hXr, arr_getL]
  have hwit2 : ∀ j (hj : j < wits.length), wits[j].2.2 < X.1.size ∧
      codeK w X.1[wits[j].2.2]! = TS j := by
    intro j hj
    have h1 := allR_true hwb j (by rw [lenA_eq]; exact hj)
    rw [Nat.zero_add, hwI j hj] at h1
    rw [andB_eq, Bool.and_eq_true] at h1
    have hc := P.blt_iff.1 h1.1
    refine ⟨hc, ?_⟩
    rw [← hTsL _ hc]
    exact P.beq_iff.1 h1.2
  have hwM : ∀ j (hj : j < wits.length), wits[j].2.2 < X.1.size := fun j hj => (hwit2 j hj).1
  have hwb' : ∀ c ∈ wits.map (fun wt => wt.2.2), c < X.1.size := by
    intro c hc
    obtain ⟨wt, hwt, rfl⟩ := List.mem_map.1 hc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hwt
    exact hwM j hj
  have hlt2 : ∀ i < X.1.size, ∀ x ∈ X.1[i]!, x < 2 ^ w := fun i hi x hx =>
    Nat.lt_of_lt_of_le ((hval i hi).2 x hx) hw
  have hTdec : ∀ j (hj : j < wits.length),
      X.1[wits[j].2.2]! = decW w (ptsOf B G).length (TS j) := by
    intro j hj
    rw [← (hwit2 j hj).2, decW_codeK' (hlt2 _ (hwM j hj)) (hval _ (hwM j hj)).1]
  have hcomm : ∀ x < X.1.size, allL (rangeK qp.length) (fun j => Nat.beq
      (mulT W qp.length X.1.size PT CT (fieldT W CT j) x)
      (mulT W qp.length X.1.size PT CT x (fieldT W CT j))) = true ↔
        ((List.range qp.length).all fun j =>
          mulIdx qp.length qp.length X.2.1 X.2.2 X.1.size X.2.2[j]! x ==
            mulIdx qp.length qp.length X.2.1 X.2.2 X.1.size x X.2.2[j]!) = true := by
    intro x hx
    rw [allL_eq, rangeK_eq', List.all_eq_true, List.all_eq_true]
    refine forall_congr' fun j => imp_congr_right fun hj => ?_
    have hj' := List.mem_range.1 hj
    rw [hcj j hj', ← (hmT _ (hcjlt j hj') _ hx).1, ← (hmT _ hx _ (hcjlt j hj')).1, P.beq_iff,
      beq_iff_eq]
  have hzne : zi ≠ 0 := by
    intro h0
    have := P.notB_iff.1 hz0
    rw [h0] at this
    exact this (by decide)
  have hcover : ∀ x < X.1.size, (((List.range qp.length).all fun j =>
      mulIdx qp.length qp.length X.2.1 X.2.2 X.1.size X.2.2[j]! x ==
        mulIdx qp.length qp.length X.2.1 X.2.2 X.1.size x X.2.2[j]!) = false ∨ x = 0) ∨
        x = zi := by
    intro x hx
    have h2 := allR_true hcov x hx
    rw [Nat.zero_add] at h2
    rcases P.orB_iff.1 h2 with h | h
    · left
      left
      exact Bool.eq_false_iff.2 fun hall => P.notB_iff.1 h ((hcomm x hx).2 hall)
    · rcases P.orB_iff.1 h with h | h
      · left
        right
        exact P.beq_iff.1 h
      · right
        exact P.beq_iff.1 h
  have hgwE : ∀ x < qp.length, evalIdxWord (mulIdx qp.length qp.length X.2.1 X.2.2 X.1.size)
      (wits.map fun w => w.2.2) (gws.getD x []) = X.2.2[x]! := by
    intro x hx
    have h1 := hgws
    rw [allL_eq, rangeK_eq', List.all_eq_true] at h1
    have h2 := P.beq_iff.1 (h1 x (List.mem_range.2 hx))
    rw [hcj x hx, ← h2, getLL_eq, witIdx_eq]
    have hwb'' : ∀ c ∈ wits.map (fun wt => wt.2.2), c < X.1.size := hwb'
    exact ((evalIdx_eq hM hmT (by rw [← witIdx_eq]; rw [witIdx_eq]; exact hwb'') _).1).symm
  have hEinj : ∀ a < X.1.size, ∀ b < X.1.size, X.1[a]! = X.1[b]! → a = b := by
    intro a ha b hb e
    rw [List.nodup_iff_injective_get] at hkeys
    have := @hkeys ⟨a, by simpa using ha⟩ ⟨b, by simpa using hb⟩ (by
      simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList]
      rw [← getElem!_pos X.1 a ha, ← getElem!_pos X.1 b hb, e])
    simpa using this
  have hGinj : ∀ t < G.length, ∀ x < n, ∀ y < n, img G[t]! x = img G[t]! y → x = y := by
    intro t ht x hx y hy e
    have ht' : t < qp.length := by omega
    have hq := hqinvT qp[t] (List.getElem_mem ht')
    rw [hGj t ht'] at e
    rw [← hq x hx, ← hq y hy, e]
  have hPtr : ∀ t < G.length, ∀ x ∈ (ptsOf B G).take B.length, img G[t]! x ∈ ptsOf B G := by
    intro t ht x hx
    have hxB : x ∈ B := by
      rw [ptsOf, List.take_left] at hx
      exact hx
    rw [ptsOf, List.mem_append]
    right
    rw [List.mem_flatMap]
    refine ⟨G[t]!, ?_, List.mem_map.2 ⟨x, hxB, rfl⟩⟩
    rw [getElem!_pos G t ht]
    exact List.getElem_mem ht
  have hGsz : ∀ t < G.length, G[t]!.size = n := fun t ht => (hGrepj t (by omega)).1
  have hkeyI : ∀ a < X.1.size, ∀ b < X.1.size,
      keyNat n B.length X.1[a]! = keyNat n B.length X.1[b]! → a = b := by
    intro a ha b hb e
    rw [List.nodup_iff_injective_get] at hkeys
    have := @hkeys ⟨a, by simpa using ha⟩ ⟨b, by simpa using hb⟩ (by
      simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList]
      rw [← getElem!_pos X.1 a ha, ← getElem!_pos X.1 b hb, e])
    simpa using this
  have hS : SetupW n B.length X.1.size G (fun i => X.1[i]!) (fun k => X.2.1[k]!)
      (fun i t => X.2.2[i * (G.length + G.length) + t]!) (ptsOf B G) := by
    refine ⟨⟨hkeyI, fun i hi t ht => ?_, fun k hk hk0 => ?_⟩, hM, hval, hX0, hGlt, hGinj, hPtr⟩
    · rw [hGl]
      exact hstepG i hi t (by omega)
    · obtain ⟨h1, s', hs', e⟩ := hparB k hk hk0
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs'
      refine ⟨h1, t, ht, ?_⟩
      have hst := hstepG X.2.1[k]! (by omega) t (by omega)
      rw [← hGl] at hst
      apply hkeyI _ hst.1 _ hk
      rw [hst.2, e, getElem!_pos G t ht]
  have hparL : ∀ k' < X.1.size, 0 < k' → X.2.1[k']! = (fun k => X.2.1[k]!) k' := fun _ _ _ => rfl
  have hclAL : ∀ i < X.1.size, ∀ t < G.length, X.2.2[i * (G.length + G.length) + t]! =
      (fun i t => X.2.2[i * (G.length + G.length) + t]!) i t := fun _ _ _ _ => rfl
  have hR0case : R = 0 → ∀ j0 (hj0 : j0 < wits.length), witOK n ta.toArray tb.toArray
      (idxTab n G qp.length qp.length X.2.1 X.2.2 X.1.size zi) (ptsOf B G) X.1 wits[j0] = true := by
    intro hR0 j0 hj0
    subst hR0
    have hfw : ∀ j (hj : j < wits.length), (wits[j].1.length = 0 ∧ wits[j].2.1.length = 0) ∧
        codeK w (List.rec (motive := fun _ => List Nat) []
          (fun p _ ih => List.cons (cjW w ZT (CP 0) (CP 0) p) ih)
          (ptsW w B (fstT TF qp))) = TS j := by
      intro j hj
      have h1 := hwit j hj
      have hg : getW wits j = wits[j] := by
        rw [getW_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      rw [fusBW, hg] at h1
      dsimp only at h1
      simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h1
      obtain ⟨l1, l2, -, hcode⟩ := h1
      refine ⟨⟨?_, ?_⟩, P.beq_iff.1 hcode⟩
      · have := Nat.le_of_ble_eq_true l1
        rw [lenA_eq] at this
        simpa [Nat.mul_eq] using this
      · have := Nat.le_of_ble_eq_true l2
        rw [lenA_eq] at this
        simpa [Nat.mul_eq] using this
    have hcc : ∀ j (hj : j < wits.length), wits[j].2.2 = wits[j0].2.2 := by
      intro j hj
      have e := (hwit2 j hj).2.trans ((hfw j hj).2.symm.trans ((hfw j0 hj0).2.trans
        (hwit2 j0 hj0).2.symm))
      exact hEinj _ (hwM j hj) _ (hwM j0 hj0) (codeK_inj (hlt2 _ (hwM j hj)) (hlt2 _ (hwM j0 hj0))
        (by rw [(hval _ (hwM j hj)).1, (hval _ (hwM j0 hj0)).1]) e)
    have hcs : ∀ c ∈ wits.map (fun wt => wt.2.2), c = wits[j0].2.2 := by
      intro c hc
      obtain ⟨wt, hwt, rfl⟩ := List.mem_map.1 hc
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hwt
      exact hcc j hj
    have hcover' : ∀ x < X.1.size, (((List.range G.length).all fun j =>
        mulIdx G.length G.length X.2.1 X.2.2 X.1.size X.2.2[j]! x ==
          mulIdx G.length G.length X.2.1 X.2.2 X.1.size x X.2.2[j]!) = false ∨ x = 0) ∨
          x = zi := by
      rw [hGl]
      exact hcover
    have hgw' : ∀ x < G.length, evalIdxWord (mulIdx G.length G.length X.2.1 X.2.2 X.1.size)
        (wits.map fun w => w.2.2) (gws.getD x []) = X.2.2[x]! := by
      rw [hGl]
      exact hgwE
    have hz : wits[j0].2.2 = zi :=
      c0_eq_ziW hS hparL hclAL hGsz hzlt hzne (hwM j0 hj0) hcs hcover' hgw'
    have hw1 : wits[j0].1 = [] := List.length_eq_zero_iff.1 (hfw j0 hj0).1.1
    have hw2 : wits[j0].2.1 = [] := List.length_eq_zero_iff.1 (hfw j0 hj0).1.2
    have hwt : wordTab n ta.toArray tb.toArray [] = Array.range n := rfl
    obtain ⟨hs1, hs2⟩ := idxTab_propW hS hparL hclAL hGsz X.1.size zi hzlt
    have hU := U_idxW hS hparL hclAL hGsz hzlt
    rw [hGl] at hs1 hs2 hU
    unfold witOK
    rw [hw1, hw2, hwt]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hwM j0 hj0, ?_⟩, ?_⟩
    · rw [invTabs, List.all_eq_true]
      intro q hq
      rw [List.mem_range] at hq
      simp [CFSG.KC.LQT.FS.Reg.img_range' hq]
    · rw [hz]
      rw [hU]
      refine List.map_congr_left fun p hp => ?_
      have hpn := hov p hp
      rw [conjImg, CFSG.KC.LQT.FS.Reg.img_range' hpn, CFSG.KC.LQT.FS.Reg.img_range' (hs2 p hpn)]
  refine ⟨hq1', hqinvT, hbe, hsz, ?_⟩
  change FusionCert.fusionCheck n B ta.toArray tb.toArray G X.1 X.2.1 X.2.2 zi wits gws = true
  simp only [FusionCert.fusionCheck, hGl, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨hzlt, hzne⟩, ?_⟩, ?_⟩, hcover⟩, ?_⟩, hgwE⟩
  · rw [← (hmT _ hzlt _ hzlt).1]
    exact P.beq_iff.1 hzz
  · intro x hx
    have h1 := hzc
    rw [allL_eq, rangeK_eq', List.all_eq_true] at h1
    have h2 := P.beq_iff.1 (h1 x (List.mem_range.2 hx))
    rw [hcj x hx, ← (hmT _ (hcjlt x hx) _ hzlt).1, ← (hmT _ hzlt _ (hcjlt x hx)).1]
    exact h2
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    by_cases hR : 0 < R
    · exact witOK_of hw hR hRa hRb hZrep hov hpts hcp hj (hwit j hj) (hwM j hj) (hTdec j hj)
    · exact hR0case (by omega) j hj

end CFSG.KC.LQT.FB.Pf

namespace CFSG.KC.LQT.FB

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2 CFSG.KC.LQT.BT

theorem fusB_sound {n w : Nat} (hw : n ≤ 2 ^ w) (W : Nat) (B ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat)
    (k fuel dd zi PK CK RP RC : Nat) (PT CT : Nat → Nat) (ZT : Nat) (TS : Nat → Nat)
    (wits : List (List Nat × List Nat × Nat)) (gws : List (List Nat)) (s R : Nat)
    (CP : Nat → Nat)
    (h : fusBH n w W B ta tb prog qp TF K m RS RT k fuel dd zi PK CK RP RC PT CT ZT TS wits gws =
      true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true)
    (hcp : ∀ q < (wordsOf wits).length * R, wordCk n w (TF 0) (TF 1) (wordsOf wits) s R CP q = true)
    (hwit : ∀ j < wits.length, fusBW n w B qp TF ZT TS wits s R CP j = true) :
    FusionCert.FusionCertS n B ta.toArray tb.toArray prog qp
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k zi wits gws := by
  exact Pf.core hw W B ta tb prog qp TF K m RS RT k fuel dd zi PK CK RP RC PT CT ZT TS wits gws s R CP
    h hnd hcp hwit

end CFSG.KC.LQT.FB

end
