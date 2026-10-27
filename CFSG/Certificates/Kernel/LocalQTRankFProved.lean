module

public import CFSG.Certificates.Kernel.LocalQTEnumFProved
public import CFSG.Certificates.Kernel.LocalQTRankCheckProved
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.KC.LQT.RF

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.RW
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BW.Cl CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RF.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem allL_ltW {W : Nat} {l : List Nat}
    (h : allL l (fun x => Nat.blt x (Nat.shiftLeft 1 W)) = true) : ∀ x ∈ l, x < 2 ^ W := by
  rw [allL_eq, List.all_eq_true] at h
  intro x hx
  have := h x hx
  rw [Nat.blt_eq] at this
  have e : Nat.shiftLeft 1 W = 2 ^ W := by
    change 1 <<< W = 2 ^ W
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rwa [e] at this

theorem rankF_sound_proved {n w : Nat} (hw : n ≤ 2 ^ w) (W : Nat) (ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (d k fuel dd zi K L : Nat)
    (h : rankFH n w W ta tb prog qp k fuel dd zi K L = true)
    (hp : ∀ j < K, rankFP n w W ta tb prog qp d dd zi (j * L) L = true) :
    RankCert.RankCertS n (List.range n) (slpTabsA ta.toArray tb.toArray prog) qp (d + 1)
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k := by
  rw [rankFH, andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hR⟩ := h
  obtain ⟨hlen, hrep⟩ := slpW_rep hw hta htb hso
  unfold rankFP enumT at hp
  generalize slpTabsA ta.toArray tb.toArray prog = T at hlen hrep ⊢
  generalize slpW n w (codeK w ta) (codeK w tb) prog = R at hlen hrep hR hp
  dsimp only at hR hp
  rw [andB_eq, Bool.and_eq_true] at hR
  obtain ⟨hqp, hEF⟩ := hR
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hEF
  obtain ⟨hnil, hfuel, hk, hpar, hcl, hzi, hz0, hzz, hcen, hcov⟩ := hEF
  have hqp' : qpW n w (List.range n) R qp = true := by
    rw [qpW, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hqp ⊢
    refine ⟨hqp.1, hqp.2.1, ?_⟩
    rw [allL_eq, List.all_eq_true]
    intro b hb
    exact P.blt_iff.2 (List.mem_range.1 hb)
  have hq1 : ∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size := by
    rw [qpW, andB_eq, Bool.and_eq_true, allA_eq, List.all_eq_true] at hqp
    intro p hp
    have := hqp.1 p hp
    rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, hlen] at this
    exact this
  set G := qp.map fun p => T[p.1]! with hGdef
  set Gp := qp.map fun p => (nodeK R p.1, T[p.1]!) with hGpdef
  have hGp : ∀ p ∈ Gp, Rep n w p.1 p.2 ∧ p.2 ∈ G := by
    intro p hp
    rw [hGpdef, List.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact ⟨hrep a.1 (hq1 a ha).1, List.mem_map.2 ⟨a, ha, rfl⟩⟩
  have hGs : Gp.map Prod.snd = G := by rw [hGpdef, hGdef, List.map_map]; rfl
  have hfst : fstN R qp = Gp.map Prod.fst := by rw [fstN_eq, hGpdef, List.map_map]; rfl
  have hGrep : ∀ s ∈ G, ∃ c, Rep n w c s := by
    intro s hs
    rw [← hGs, List.mem_map] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact ⟨p.1, (hGp p hp).1⟩
  have hB' : ∀ b ∈ List.range n, b < n := fun b hb => List.mem_range.1 hb
  have hpts : ptsW w (List.range n) (fstN R qp) = ptsOf (List.range n) G := by
    rw [hfst, ptsW_eq hB' (forall2_pairs Gp fun p hp => (hGp p hp).1), hGs]
  have hov : Val n (ptsOf (List.range n) G).length (ptsOf (List.range n) G) := by
    refine ⟨rfl, fun x hx => ?_⟩
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact hB' x hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨c, hc⟩ := hGrep s hs
      exact (hc.2 b (hB' b hb)).1
  have hnL : n ≤ (ptsOf (List.range n) G).length := by
    rw [ptsOf, List.length_append, List.length_range]
    omega
  have hoid : ∀ p ∈ ptsOf (List.range n) G, (ptsOf (List.range n) G).getD p 0 = p := by
    intro p hp
    have hpn := hov.2 p hp
    rw [ptsOf, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      List.getElem?_range hpn, Option.getD_some]
  obtain ⟨hP1, hP2, hP3⟩ := enumF_proj (gi := lenA qp) hw hGp hGs dd
  have hok := enum_ok (gi := lenA qp) hw hGp hGs hov hoid hnL dd
  rw [hfst] at hnil hfuel hk hpar hcl hzi hzz hcen hcov hp
  generalize enumF n w (lenA qp) (Gp.map Prod.fst) dd = EF
    at hnil hfuel hk hpar hcl hzi hzz hcen hcov hp hP1 hP2 hP3
  generalize hEd : enumW w n (lenA qp) (imgsW w) (Gp.map Prod.fst) (ptsOf (List.range n) G) dd
    = EW at hP1 hP2 hP3 hok
  have hcnt : EF.1.cnt = EW.1.cnt := by rw [← hP1]; rfl
  have hparE : EF.1.par = EW.1.par := by rw [← hP1]; rfl
  have hclE : EF.1.cl = EW.1.cl := by rw [← hP1]; rfl
  have hnil' : EW.2.2 = [] := by
    have e : EF.2.2 = [] := by
      revert hnil
      cases EF.2.2 with
      | nil => exact fun _ => rfl
      | cons _ _ => exact fun h => absurd h Bool.false_ne_true
    rw [← hP3] at e
    exact List.map_eq_nil_iff.1 e
  have hEOK : enumOK k fuel EW = true := by
    simp only [enumOK, allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨by rw [hnil'], by rw [← hcnt]; exact hfuel, by rw [← hcnt]; exact hk, hok.1⟩
  have hEd' : enumW w (lenA (List.range n)) (lenA qp) (imgsW w) (fstN R qp)
      (ptsW w (List.range n) (fstN R qp)) dd = EW := by
    rw [hpts, hfst, lenA_eq (List.range n), List.length_range, hEd]
  obtain ⟨hq1', hinv, hbe, hsz, hcntX, hpl, hparX, hcll, hclX⟩ :=
    enumW_bfs hw hlen hrep hqp' _ rfl EW hEd' hEOK
  generalize bfsEnumB n (List.range n) (qp.map fun p => T[p.1]!) (qp.map fun p => T[p.2]!) fuel = X
    at hbe hsz hcntX hpl hparX hcll hclX ⊢
  refine ⟨hq1', hinv, hbe, hsz, ?_⟩
  unfold invsF at hcov
  rw [lenA_eq] at hzz hcen hcov hp
  rw [hcnt, hcntX] at hzi hcen hcov hp
  have hparlt : ∀ x ∈ EW.1.par.reverse, x < 2 ^ W := fun x hx =>
    allL_ltW (hparE ▸ hpar) x (List.mem_reverse.1 hx)
  have hcllt : ∀ x ∈ EW.1.cl.reverse, x < 2 ^ W := fun x hx =>
    allL_ltW (hclE ▸ hcl) x (List.mem_reverse.1 hx)
  have hmF : ∀ i k', mulF W qp.length EF i k' =
      mulG (imgW W (codeK W EW.1.par.reverse)) (imgW W (codeK W EW.1.cl.reverse)) qp.length
        (qp.length + qp.length) X.1.size i k' := by
    intro i k'
    rw [mulF, mulIdxW_eq, revOn_eq, revOn_eq, List.append_nil, List.append_nil, hparE, hclE,
      hcnt, hcntX]
    rfl
  have hfP : ∀ i < X.1.size, imgW W (codeK W EW.1.par.reverse) i = X.2.1[i]! := by
    intro i hi
    rw [imgW_codeK _ hparlt i (by rw [List.length_reverse, hpl]; exact hi), hparX i hi]
  have hfC : ∀ i < X.1.size, ∀ j < qp.length,
      imgW W (codeK W EW.1.cl.reverse) (i * (qp.length + qp.length) + j) =
        X.2.2[i * (qp.length + qp.length) + j]! := by
    intro i hi j hj
    rw [imgW_codeK _ hcllt _ (by rw [List.length_reverse, hcll]; exact pos_lt hi (by omega)),
      hclX i hi j hj]
  obtain ⟨-, -, -, hparB, -, hstep, -⟩ := hbe
  have hGl : (qp.map fun p => T[p.1]!).length = qp.length := List.length_map _
  have hGil : (qp.map fun p => T[p.2]!).length = qp.length := List.length_map _
  rw [hGl, hGil] at hstep
  have hmul := mulG_spec (N := X.1.size) (g := qp.length) (gi := qp.length) hfP hfC
    (fun i hi hi0 => by
      obtain ⟨h1, s, hs, -⟩ := hparB i hi hi0
      refine ⟨h1, ?_⟩
      rcases qp with _ | ⟨q, qp⟩
      · simp at hs
      · simp)
    (fun i hi j hj => (hstep i hi j hj).1) X.1.size
  apply rankCheck_of_parts (zi := zi) (K := K) (L := L) (g := qp.length) (gi := qp.length)
    (par := X.2.1) (cl := X.2.2) (mul := mulF W qp.length EF)
    (fun i hi k hk => by rw [hmF, (hmul i k hi hk).1]; exact ⟨rfl, (hmul i k hi hk).2⟩)
  · exact P.blt_iff.1 hzi
  · rw [notB_eq, Bool.not_eq_true', ← Bool.not_eq_true] at hz0
    exact fun e => hz0 (P.beq_iff.2 e)
  · exact P.beq_iff.1 hzz
  · intro i hi
    have := allR_true hcen i hi
    rw [Nat.zero_add] at this
    exact P.beq_iff.1 this
  · rw [lenA_eq] at hcov
    exact Nat.le_of_ble_eq_true hcov
  · exact hp

end CFSG.KC.LQT.RF

end
