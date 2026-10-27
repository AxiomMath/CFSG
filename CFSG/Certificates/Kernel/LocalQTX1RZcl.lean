module

public import Certificates.Data.Kernel.LocalQT.X1R
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RowNative
public import CFSG.Certificates.Kernel.LocalQTX1RProved
public import CFSG.Certificates.Kernel.LocalQTBfsSProved

public section

namespace CFSG.KC.LQT.XR.Zcl

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF CFSG.KC.LQT.RB
open CFSG.KC.LQT.FS CFSG.KC.LQT.XH CFSG.KC.LQT.XR CFSG.KC.LQT.BS
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf CFSG.KC.LQT.RF.Pf CFSG.KC.LQT.BS.Pf
open CFSG.KC.LQT.XH.Pf CFSG.KC.LQT.BSP CFSG.KC.LQT.XR.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem eqB_true {a b : Bool} (h : eqB a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem getD_lt_n {n : Nat} {T : List Nat} (hT : ∀ x ∈ T, x < n) {i : Nat} (hi : i < T.length) :
    T.getD i 0 < n := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact hT _ (List.getElem_mem hi)

theorem getD_map_tab {n w : Nat} {Gc : List Nat} {j : Nat} (hj : j < Gc.length) :
    (Gc.map (tabC n w)).getD j #[] = tabC n w (Gc.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj]
  rfl

theorem passK_eq {n w nb : Nat} {Gc Zc : List Nat} {T : List Nat}
    (hG : ∀ c ∈ Gc, ∀ i < n, imgW w c i < n) (hZ : ∀ c ∈ Zc, ∀ i < n, imgW w c i < n)
    (hT : ∀ x ∈ T, x < n) (hlen : nb * (1 + Gc.length) ≤ T.length) :
    passK w nb Gc Zc T = passAll nb (Gc.map (tabC n w)) (Zc.map (tabC n w)) T := by
  apply Bool.eq_iff_iff.2
  unfold passK passAll commInR
  rw [allL_eq, lenA_eq, rangeK_eq', List.length_map]
  simp only [List.all_eq_true, List.mem_range, anyL_eq, allL_eq, rangeK_eq', List.any_eq_true,
    List.mem_map]
  have key : ∀ j < Gc.length, ∀ Yc ∈ Zc, ∀ x < nb,
      ((getK T ((nb.mul j.succ).add x)).beq (imgW w Yc (imgW w (getK Gc j) (getK T x))) = true ↔
      (T.getD (nb * (1 + j) + x) 0 ==
        img (tabC n w Yc) (img ((List.map (tabC n w) Gc).getD j #[]) (T.getD x 0))) = true) := by
    intro j hj Yc hY x hx
    have hnb : nb ≤ nb * (1 + Gc.length) := Nat.le_mul_of_pos_right _ (by omega)
    have h1 : nb * (1 + j) + x < nb * (1 + Gc.length) := by
      have : nb * (1 + j) + nb = nb * (1 + j + 1) := by rw [Nat.mul_succ]
      have h2 : nb * (1 + j + 1) ≤ nb * (1 + Gc.length) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hxT := getD_lt_n hT (show x < T.length by omega)
    have hgj : Gc.getD j 0 ∈ Gc := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact List.getElem_mem hj
    have hy1 := hG _ hgj _ hxT
    rw [getD_map_tab hj, img_tabC hxT, img_tabC hy1]
    simp only [getK_eq]
    rw [show (nb.mul j.succ).add x = nb * (1 + j) + x by
        rw [Nat.mul_eq, Nat.add_eq, Nat.succ_eq_add_one, Nat.add_comm 1 j],
      P.beq_iff, beq_iff_eq]
  refine forall_congr' fun j => imp_congr_right fun hj => ?_
  constructor
  · rintro ⟨Yc, hY, hk⟩
    exact ⟨tabC n w Yc, ⟨Yc, hY, rfl⟩, fun x hx => (key j hj Yc hY x hx).1 (hk x hx)⟩
  · rintro ⟨_, ⟨Yc, hY, rfl⟩, hk⟩
    exact ⟨Yc, hY, fun x hx => (key j hj Yc hY x hx).2 (hk x hx)⟩

theorem rowOf_tab {n w : Nat} {P : List Nat} (hP : ∀ x ∈ P, x < n) (c : Nat) :
    rowOf P (tabC n w c) = P.map (imgW w c) := by
  unfold rowOf
  exact List.map_congr_left fun x hx => img_tabC (hP x hx)

theorem rowK_eq (w : Nat) (P : List Nat) (c : Nat) : rowK w P c = codeK w (P.map (imgW w c)) := by
  rw [rowK, mapW_eq]

theorem contains_eq {n w r : Nat} (hw : n ≤ 2 ^ w) {P Lc T : List Nat} {c : Nat}
    (hP : ∀ x ∈ P, x < n) (hr : P.length = r) (hT : Val n r T) (hc : c = codeK w T) :
    ((Lc.map (tabC n w)).map (rowOf P)).contains T =
      anyL (Lc.map (rowK w P)) (Nat.beq c) := by
  have hTw : ∀ x ∈ T, x < 2 ^ w := fun x hx => Nat.lt_of_lt_of_le (hT.2 x hx) hw
  have hinj : ∀ Yc, rowK w P Yc = c ↔ P.map (imgW w Yc) = T := by
    intro Yc
    rw [rowK_eq, hc]
    constructor
    · intro h
      exact codeK_inj (fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        exact imgW_lt _ _ _) hTw (by rw [List.length_map, hr, hT.1]) h
    · intro h
      rw [h]
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, anyL_eq, List.any_eq_true]
  simp only [List.mem_map]
  constructor
  · rintro ⟨_, ⟨Yc, hY, rfl⟩, h⟩
    refine ⟨rowK w P Yc, ⟨Yc, hY, rfl⟩, ?_⟩
    rw [beq_iff, eq_comm, hinj, ← h, rowOf_tab hP]
  · rintro ⟨_, ⟨Yc, hY, rfl⟩, h⟩
    refine ⟨tabC n w Yc, ⟨Yc, hY, rfl⟩, ?_⟩
    rw [rowOf_tab hP, ← hinj]
    exact (beq_iff.1 h).symm

theorem claim_core {n w nb M r lg : Nat} (hw : n ≤ 2 ^ w) {Gc Zc Lc P : List Nat}
    {E BO : Nat → Nat} {Ts : Array (List Nat)} {G Z L : List (Array Nat)}
    (hGeq : G = Gc.map (tabC n w)) (hZeq : Z = Zc.map (tabC n w)) (hLeq : L = Lc.map (tabC n w))
    (hG : ∀ c ∈ Gc, ∀ i < n, imgW w c i < n) (hZ : ∀ c ∈ Zc, ∀ i < n, imgW w c i < n)
    (hP : ∀ x ∈ P, x < n) (hr : P.length = r) (hrlen : nb * (1 + Gc.length) ≤ r)
    (hM : 0 < M) (hsurj : ∀ j < M, ∃ i < M, BO i = j)
    (hVal : ∀ i < M, Val n r (decW w r (E (BO i))) ∧ E (BO i) = codeK w (decW w r (E (BO i))))
    (hTs : Ts.size = M) (hTi : ∀ i < M, Ts[i]! = decW w r (E (BO i)))
    (hcl : ∀ i < M, claimK w nb Gc Zc (Lc.map (rowK w P)) (decW w r (E (BO i))) (E (BO i)) = true)
    (hmem : ∀ c ∈ Lc, memS w nb M lg E (rowK w P c) = true) :
    zClaimOK nb G P Ts Z L = true := by
  subst hGeq hZeq hLeq
  unfold zClaimOK
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro T hT
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
    have hiM : i < M := by
      rw [← hTs]
      simpa using hi
    have hTi' : Ts.toList[i] = decW w r (E (BO i)) := by
      rw [← hTi i hiM, getElem!_pos Ts i (by omega)]
      simp
    rw [hTi']
    obtain ⟨hv, hcode⟩ := hVal i hiM
    have h := eqB_true (by have := hcl i hiM; unfold claimK at this; exact this)
    rw [passK_eq hG hZ hv.2 (by rw [hv.1]; exact hrlen)] at h
    rw [contains_eq hw hP hr hv hcode, h]
    exact beq_self_eq_true _
  · rw [List.all_eq_true]
    intro Y hY
    obtain ⟨Yc, hYc, rfl⟩ := List.mem_map.1 hY
    obtain ⟨j, hj, hej⟩ := memS_spec hM (hmem Yc hYc)
    obtain ⟨i, hi, rfl⟩ := hsurj j hj
    obtain ⟨hv, hcode⟩ := hVal i hi
    have hTw : ∀ x ∈ decW w r (E (BO i)), x < 2 ^ w :=
      fun x hx => Nat.lt_of_lt_of_le (hv.2 x hx) hw
    have heq : rowOf P (tabC n w Yc) = Ts[i]! := by
      rw [hTi i hi, rowOf_tab hP]
      refine codeK_inj (fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        exact imgW_lt _ _ _) hTw (by rw [List.length_map, hr, hv.1]) ?_
      rw [← rowK_eq, hej.symm.trans rfl, ← hcode]
    rw [heq, getElem!_pos Ts i (by omega)]
    exact Array.contains_eq_true_of_mem (Array.getElem_mem _)

theorem ptsOf_length (B : List Nat) (G : List (Array Nat)) :
    (ptsOf B G).length = B.length + G.length * B.length := by
  unfold ptsOf
  induction G with
  | nil => simp
  | cons s t ih =>
    rw [List.flatMap_cons, List.length_append, List.length_append, List.length_map] at *
    simp only [List.length_append, List.length_flatMap] at *
    rw [List.length_cons, Nat.succ_mul]
    simp only [List.length_map] at *
    omega

theorem zcl_main {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat) (zn gn gin hn hin k fuel M lg : Nat)
    (E : Nat → Nat) (K2 L2 : Nat) (PG : Nat → Nat) (W : Nat) (BO IB PT CT : Nat → Nat)
    (K3 L3 : Nat) (prog2 : List (Nat × Nat)) (TF2 : Nat → Nat) (K5 m5 : Nat)
    (nodes1 nodes2 nodes3 : List Nat) (K6 L6 : Nat)
    (h : baseSK n w B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true)
    (hs : ∀ c < K2, setS w B qp TF RS RT zn M lg E PG (c * L2) L2 = true)
    (hb : ∀ c < K3, bfsS w B qp TF RS RT M lg W E BO IB PT CT (c * L3) L3 = true)
    (hcov : M ≤ K3 * L3 ∧ M ≤ K6 * L6)
    (h2 : slp2H n w ta tb prog2 TF2 K5 m5 = true)
    (hn2 : ∀ c < K5, nodesT n w prog2 TF2 (c * m5) m5 = true)
    (hz : zcH w B qp TF M lg E (prog2.length + 2) TF2 nodes1 nodes2 nodes3 = true)
    (hzs : ∀ c < K6, zcS n w B qp TF E BO M TF2 nodes1 nodes2 nodes3 (c * L6) L6 = true) :
    zClaimOK B.length (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
      (ptsOf B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!))
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      [Array.range n] (nodes1.map fun i => (slpTabsA ta.toArray tb.toArray prog2)[i]!) = true ∧
    zClaimOK B.length (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
      (ptsOf B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!))
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (nodes1.map fun i => (slpTabsA ta.toArray tb.toArray prog2)[i]!)
      (nodes2.map fun i => (slpTabsA ta.toArray tb.toArray prog2)[i]!) = true ∧
    zClaimOK B.length (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
      (ptsOf B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!))
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (nodes2.map fun i => (slpTabsA ta.toArray tb.toArray prog2)[i]!)
      (nodes3.map fun i => (slpTabsA ta.toArray tb.toArray prog2)[i]!) = true := by
  obtain ⟨hTs, hRepT, hq1', hB', happ, hpts, hMk, hMf, hstrict, hRa, hRb⟩ :=
    base_setup hw B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 PG h hnd hs
  obtain ⟨hM, -, hBO, hsurj, hVal, -, -, hX⟩ :=
    bfsS_enum hw B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 PG W BO IB PT
      CT K3 L3 h hnd hs hb hcov.1
  obtain ⟨hXs, hX1, -, -⟩ := hX _ rfl
  rw [slp2H] at h2
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h2
  obtain ⟨hta, htb, hso, hTF0, hTF1, hKm⟩ := h2
  have h0 : Rep n w (TF2 0) ta.toArray := by
    rw [beq_iff.1 hTF0]
    exact rep_codeK hw hta
  have h1 : Rep n w (TF2 1) tb.toArray := by
    rw [beq_iff.1 hTF1]
    exact rep_codeK hw htb
  obtain ⟨hlen2, hrep2⟩ := nodes_rep prog2 TF2 K5 m5 _ _ h0 h1 hso hKm hn2
  generalize bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
    (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel = X at hXs hX1 ⊢
  generalize slpTabsA ta.toArray tb.toArray prog = T at hTs hRepT hq1' happ hpts hVal hX1 ⊢
  generalize slpTabsA ta.toArray tb.toArray prog2 = T2 at hlen2 hrep2 ⊢
  set G := qp.map fun p => T[p.1]! with hGdef
  have hGl : G.length = qp.length := List.length_map _
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGlt : ∀ t < G.length, ∀ y < n, img G[t]! y < n := by
    intro t ht y hy
    have ht' : t < qp.length := by omega
    rw [hGj t ht']
    exact ((hRepT _ (hq1' _ (List.getElem_mem ht')).1).2 y hy).1
  have hov : ∀ x ∈ ptsOf B G, x < n := by
    intro x hx
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact hB' x hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
      rw [← getElem!_pos G t ht]
      exact hGlt t ht b (hB' b hb)
  have hGeq : G = (fstT TF qp).map (tabC n w) := by
    rw [fstT_eq, List.map_map]
    apply List.map_congr_left
    intro p hp
    exact rep_unique (hRepT _ (hq1' p hp).1) (rep_tabC (rep_fields (hRepT _ (hq1' p hp).1)))
  have hGc : ∀ c ∈ fstT TF qp, ∀ i < n, imgW w c i < n := by
    intro c hc
    rw [fstT_eq, List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    exact rep_fields (hRepT _ (hq1' p hp).1)
  have hGcl : (fstT TF qp).length = qp.length := by rw [fstT_eq, List.length_map]
  have hrlen : B.length * (1 + (fstT TF qp).length) ≤ (ptsOf B G).length := by
    rw [ptsOf_length, hGl, hGcl, Nat.mul_add, Nat.mul_one, Nat.mul_comm B.length]
  have htab : ∀ i < T2.size, T2[i]! = tabC n w (TF2 i) := fun i hi =>
    rep_unique (hrep2 i hi) (rep_tabC (rep_fields (hrep2 i hi)))
  have hmapT : ∀ l : List Nat, (∀ i ∈ l, i < T2.size) →
      l.map (fun i => T2[i]!) = (l.map TF2).map (tabC n w) := by
    intro l hl
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact htab i (hl i hi)
  have hfld : ∀ l : List Nat, (∀ i ∈ l, i < T2.size) →
      ∀ c ∈ l.map TF2, ∀ i < n, imgW w c i < n := by
    intro l hl c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    exact rep_fields (hrep2 i (hl i hi))
  rw [zcH] at hz
  dsimp only at hz
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hz
  obtain ⟨hl1, hl2, hl3, hm1, hm2, hm3⟩ := hz
  have hlt : ∀ l : List Nat, allL l (fun i => Nat.blt i (prog2.length + 2)) = true →
      ∀ i ∈ l, i < T2.size := by
    intro l hl i hi
    rw [allL_eq, List.all_eq_true] at hl
    have := hl i hi
    rw [Nat.blt_eq] at this
    omega
  have hmemL : ∀ l : List Nat, allL l (fun i => memS w (lenA B) M lg E
      (rowK w (ptsW w B (fstT TF qp)) (TF2 i))) = true →
      ∀ c ∈ l.map TF2, memS w (lenA B) M lg E (rowK w (ptsW w B (fstT TF qp)) c) = true := by
    intro l hl c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    rw [allL_eq, List.all_eq_true] at hl
    exact hl i hi
  have l1 := hlt _ hl1
  have l2 := hlt _ hl2
  have l3 := hlt _ hl3
  have hmem1 := hmemL _ hm1
  have hmem2 := hmemL _ hm2
  have hmem3 := hmemL _ hm3
  rw [hpts, lenA_eq] at hmem1 hmem2 hmem3
  have hL6 : 0 < L6 := by
    rcases Nat.eq_zero_or_pos L6 with h0 | h0
    · have := hcov.2
      rw [h0, Nat.mul_zero] at this
      omega
    · exact h0
  have hcl : ∀ i < M, ∀ c : Nat, c = E (BO i) →
      allBs [claimK w B.length (fstT TF qp) [oneW n w] (mapW (rowK w (ptsOf B G))
          (mapW TF2 nodes1)) (decW w (ptsOf B G).length c) c,
        claimK w B.length (fstT TF qp) (mapW TF2 nodes1) (mapW (rowK w (ptsOf B G))
          (mapW TF2 nodes2)) (decW w (ptsOf B G).length c) c,
        claimK w B.length (fstT TF qp) (mapW TF2 nodes2) (mapW (rowK w (ptsOf B G))
          (mapW TF2 nodes3)) (decW w (ptsOf B G).length c) c] = true := by
    intro i hi c hc
    have hK : i / L6 < K6 := by
      rw [Nat.div_lt_iff_lt_mul hL6]
      exact lt_of_lt_of_le hi hcov.2
    have := hzs (i / L6) hK
    rw [zcS] at this
    dsimp only at this
    rw [hpts] at this
    have := allR_true this (i % L6) (Nat.mod_lt _ hL6)
    rw [Nat.div_add_mod' i L6] at this
    have := impB_true this (blt_iff.2 hi)
    simp only [lenA_eq] at this
    rw [hc]
    exact this
  have hcl' : ∀ i < M, _ := fun i hi => by
    have := hcl i hi _ rfl
    simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true, mapW_eq] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · refine claim_core hw (Z := [Array.range n]) (Zc := [oneW n w]) (Lc := nodes1.map TF2)
      hGeq (by rw [List.map_cons, List.map_nil, tabC_one hw]) (hmapT _ l1) hGc ?_ hov rfl hrlen hM
      hsurj hVal hXs hX1 (fun i hi => (hcl' i hi).1) hmem1
    intro c hc i hi
    rw [List.mem_singleton] at hc
    subst hc
    exact (vc_one hw).1 i hi
  · exact claim_core hw (Zc := nodes1.map TF2) (Lc := nodes2.map TF2) hGeq (hmapT _ l1)
      (hmapT _ l2) hGc (hfld _ l1) hov rfl hrlen hM hsurj hVal hXs hX1
      (fun i hi => (hcl' i hi).2.1) hmem2
  · exact claim_core hw (Zc := nodes2.map TF2) (Lc := nodes3.map TF2) hGeq (hmapT _ l2)
      (hmapT _ l3) hGc (hfld _ l2) hov rfl hrlen hM hsurj hVal hXs hX1
      (fun i hi => (hcl' i hi).2.2) hmem3

end CFSG.KC.LQT.XR.Zcl

end
