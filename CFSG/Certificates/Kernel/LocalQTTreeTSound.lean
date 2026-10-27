module

public import Certificates.Data.Kernel.LocalQT.TreeT
public import CFSG.Certificates.Kernel.LocalQTBaseSProved
public import CFSG.Quasithin.Vol2.KGFactRankInputs

public section

namespace CFSG.KC.LQT.TT.Pf

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.TT

theorem lenA_codesL (TF : Nat → Nat) : ∀ N, lenA (codesL TF N) = N
  | 0 => rfl
  | N + 1 => by
    change lenA (TF N :: codesL TF N) = N + 1
    rw [lenA_eq, List.length_cons, ← lenA_eq, lenA_codesL TF N]

theorem getD_codesL (TF : Nat → Nat) : ∀ N i, i < N → (codesL TF N).getD i 0 = TF (N - 1 - i)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | N + 1, i, h => by
    change (TF N :: codesL TF N).getD i 0 = _
    rcases i with _ | i
    · rw [List.getD_cons_zero]
      congr 1
    · rw [List.getD_cons_succ, getD_codesL TF N i (by omega)]
      congr 1
      omega

theorem nodeK_codesL (TF : Nat → Nat) {N j : Nat} (hj : j < N) : nodeK (codesL TF N) j = TF j := by
  rw [nodeK, getK_eq, lenA_codesL]
  change (codesL TF N).getD (N - 1 - j) 0 = TF j
  rw [getD_codesL TF N _ (by omega)]
  congr 1
  omega

theorem filter_range_le (p : Nat → Bool) (N : Nat) :
    ((List.range N).filter p).length ≤ ((List.range N).filter fun x => x != 0 && p x).length + 1 := by
  rcases N with _ | N
  · simp
  · rw [List.range_succ_eq_map, List.filter_cons, List.filter_cons]
    have e : (List.map Nat.succ (List.range N)).filter (fun x => x != 0 && p x) =
        (List.map Nat.succ (List.range N)).filter p := by
      apply List.filter_congr
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      simp
    have e0 : ((0 != 0) && p 0) = false := by simp
    rw [e0, e]
    cases p 0 <;> simp

end CFSG.KC.LQT.TT.Pf

end

public section

namespace CFSG.KC.LQT.TT

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF CFSG.KC.LQT.RB
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BW.Cl CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf CFSG.KC.LQT.BS.Pf
open CFSG.KC.LQT.TT.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2 CFSG.Quasithin.H13.KGRank
open CFSG.QuasithinUnique.Lin2.RankCert
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem treeT_sound {n w : Nat} (hw : n ≤ 2 ^ w) (W : Nat) (B ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (TF : Nat → Nat) (K m k fuel dd zi PK CK RP RC : Nat)
    (PT CT : Nat → Nat)
    (h : treeTH n w W B ta tb prog qp TF K m k fuel dd zi PK CK RP RC PT CT = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true) :
    treeCheck
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1.size
      qp.length qp.length
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 zi #[] = true := by
  rw [treeTH] at h
  dsimp only at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hTF0, hTF1, hKm, hqp, hBE⟩ := h
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
    rw [P.beq_iff, CFSG.KC.LQT.BS.Pf.nthP_eq,
      show Nat.sub (2 + q) 2 = q by rw [Nat.sub_eq]; omega] at this
    exact this
  have hTs : (slpTabsA ta.toArray tb.toArray prog).size = prog.length + 2 := by
    rw [slpTabsA, foldl_slpStepA_size]
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    omega
  have hRepT : ∀ j < (slpTabsA ta.toArray tb.toArray prog).size,
      Rep n w (TF j) (slpTabsA ta.toArray tb.toArray prog)[j]! := by
    rw [slpTabsA]
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
  generalize slpTabsA ta.toArray tb.toArray prog = T at hTs hRepT ⊢
  have hNT : Nat.add (lenA prog) 2 = T.size := by rw [hTs, lenA_eq, Nat.add_eq]
  have hlen : lenA (codesL TF (Nat.add (lenA prog) 2)) = T.size := by rw [lenA_codesL, hNT]
  have hrep : ∀ j < T.size, Rep n w (nodeK (codesL TF (Nat.add (lenA prog) 2)) j) T[j]! := by
    intro j hj
    rw [nodeK_codesL TF (by rw [hNT]; exact hj)]
    exact hRepT j hj
  generalize codesL TF (Nat.add (lenA prog) 2) = R at hlen hrep hqp hBE
  rw [rankBE] at hBE
  dsimp only at hBE
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hBE
  obtain ⟨hE, hpar, hcl, hPK, hCK, hRP, hRC, hzi, -, hzz, hcen, hcov⟩ := hBE
  generalize hEd : enumW w (lenA B) (lenA qp) (imgsW w) (fstN R qp) (ptsW w B (fstN R qp)) dd = E
    at hE hpar hcl hPK hCK hRP hRC hzi hzz hcen hcov
  obtain ⟨-, -, hbe, -, hcnt, hpl, hparE, hcll, hclE⟩ :=
    enumW_bfs hw hlen hrep hqp _ rfl E hEd hE
  generalize bfsEnumB n B (qp.map fun p => T[p.1]!) (qp.map fun p => T[p.2]!) fuel = X
    at hbe hcnt hpl hparE hcll hclE ⊢
  rw [lenA_eq] at hRC hzz hcen hcov
  rw [hcnt] at hRP hRC hzi hzz hcen hcov
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
  have hfP : ∀ i < X.1.size, fieldT W PT i = X.2.1[i]! := by
    intro i hi
    rw [field_code hRP hPK' hparlt (by rw [List.length_reverse, hpl]) hi, hparE i hi]
  have hfC : ∀ i < X.1.size, ∀ j < qp.length,
      fieldT W CT (i * (qp.length + qp.length) + j) = X.2.2[i * (qp.length + qp.length) + j]! := by
    intro i hi j hj
    have hRC' : rowsOK W (X.1.size * (qp.length + qp.length)) RC CK CT = true := hRC
    rw [field_code hRC' hCK' hcllt (by rw [List.length_reverse, hcll]) (pos_lt hi (by omega)),
      hclE i hi j hj]
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
  have hmT : ∀ i k, mulT W qp.length X.1.size PT CT i k =
      mulG (fieldT W PT) (fieldT W CT) qp.length (qp.length + qp.length) X.1.size i k :=
    fun _ _ => rfl
  generalize hM : mulIdx qp.length qp.length X.2.1 X.2.2 X.1.size = M at hmul
  have hMT : ∀ i < X.1.size, ∀ k < X.1.size, mulT W qp.length X.1.size PT CT i k = M i k :=
    fun i hi k hk => by rw [hmT]; exact (hmul i k hi hk).1
  have hzi' : zi < X.1.size := P.blt_iff.1 hzi
  have hzz' : M zi zi = 0 := by rw [← hMT zi hzi' zi hzi']; exact P.beq_iff.1 hzz
  have hcen' : ∀ i < X.1.size, M zi i = M i zi := by
    intro i hi
    have := allR_true hcen i hi
    rw [Nat.zero_add, P.beq_iff, hMT zi hzi' i hi, hMT i hi zi hzi'] at this
    exact this
  have hinv : ((List.range X.1.size).filter fun x => x != 0 && M x x == 0).length ≤ 254 := by
    unfold invsB at hcov
    rw [lenA_eq, filterN_eq] at hcov
    have e : ((List.range X.1.size).filter fun i => CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq i 0))
        (Nat.beq (mulT W qp.length X.1.size PT CT i i) 0)) =
        (List.range X.1.size).filter fun x => x != 0 && M x x == 0 := by
      apply List.filter_congr
      intro x hx
      rw [List.mem_range] at hx
      rw [andB_eq, notB_eq, hMT x hx x hx]
      apply Bool.eq_iff_iff.2
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, beq_iff_eq]
      have e1 : Nat.beq x 0 = false ↔ x ≠ 0 := by
        rw [← Bool.not_eq_true, P.beq_iff]
      have e2 : Nat.beq (M x x) 0 = true ↔ M x x = 0 := P.beq_iff
      rw [e1, e2]
    rw [e] at hcov
    have := Nat.le_of_ble_eq_true hcov
    omega
  have hle := filter_range_le (fun x => M x x == 0) X.1.size
  unfold treeCheck
  rw [hM]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨hzi', hzz'⟩, fun i hi => hcen' i hi⟩, ?_⟩
  simp only [Array.size_empty, nodeCheck, Bool.or_eq_true, decide_eq_true_eq]
  left
  omega

end CFSG.KC.LQT.TT

end
