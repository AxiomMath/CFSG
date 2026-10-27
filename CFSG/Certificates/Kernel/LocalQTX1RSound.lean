module

public import Certificates.Data.Kernel.LocalQT.X1R
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RowNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RuData
import CFSG.Certificates.Kernel.LocalQTX1RZcl

public section

namespace CFSG.KC.LQT.XR

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.BT
open CFSG.KC.LQT.BS CFSG.KC.LQT.FS CFSG.KC.Ord

def pairsK : List Nat → List (Nat × Nat)
  | x :: y :: r => (x, y) :: pairsK r
  | _ => []

theorem pairsL_eq (l : List Nat) :
    (List.range (l.length / 2)).map (fun i => (l.getD (2 * i) 0, l.getD (2 * i + 1) 0)) =
      pairsK l := by
  induction l using pairsK.induct with
  | case1 x y r ih =>
    rw [pairsK, ← ih]
    have : (x :: y :: r).length / 2 = r.length / 2 + 1 := by simp; omega
    rw [this, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1
  | case2 l h =>
    have : l.length / 2 = 0 := by
      match l, h with
      | [], _ => rfl
      | [_], _ => simp
      | _ :: _ :: _, h => exact absurd rfl (h _ _ _)
    rw [this]
    simp [pairsK.eq_def]

theorem pairsR_eq (l : List Nat) :
    pairsR l none = pairsK l ∧ ∀ y, pairsR l (some y) = pairsK (y :: l) := by
  induction l with
  | nil => exact ⟨rfl, fun y => rfl⟩
  | cons x t ih =>
    refine ⟨?_, fun y => ?_⟩
    · change pairsR t (some x) = pairsK (x :: t)
      exact ih.2 x
    · change (y, x) :: pairsR t none = pairsK (y :: x :: t)
      rw [ih.1, pairsK]

theorem pairsOfFlat_eq (a : Array Nat) : pairsOfFlat a = pairsR a.toList none := by
  rw [(pairsR_eq _).1, ← pairsL_eq]
  unfold pairsOfFlat
  simp [Array.getD_eq_getD_getElem?]

theorem andB_true {a b : Bool} (h : CFSG.KC.Ord.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KC.Ord.andB]

theorem eqPL_spec (l m : List (Nat × Nat)) (h : eqPL l m = true) : l = m := by
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => rfl
    | cons q m' => exact absurd h (by simp [eqPL])
  | cons p l ih =>
    cases m with
    | nil => exact absurd h (by simp [eqPL])
    | cons q m' =>
      change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.beq p.1 q.1) (Nat.beq p.2 q.2)) (eqPL l m') = true at h
      obtain ⟨h1, h2⟩ := andB_true h
      obtain ⟨h3, h4⟩ := andB_true h1
      rw [Nat.beq_eq] at h3 h4
      rw [ih m' h2, Prod.ext h3 h4]

theorem x1RA_sound {n w : Nat} (hw : n ≤ 2 ^ w) (ta tb : List Nat)
    (prog2 qp wprog : List (Nat × Nat)) (TF2 : Nat → Nat) (K m : Nat) (TF3 : Nat → Nat)
    (K' m' gn gin hn hin an bn : Nat) (nodes1 nodes2 nodes3 : List Nat)
    (h : x1RA n w ta tb prog2 qp wprog TF2 K m TF3 K' m' gn gin hn hin an bn nodes1 nodes2 nodes3 =
      true)
    (hn2 : ∀ c < K, nodesT n w prog2 TF2 (c * m) m = true)
    (hn3 : ∀ c < K', nodesT n w wprog TF3 (c * m') m' = true) :
    qpOK n (slpTabsA ta.toArray tb.toArray prog2) qp ∧
    (gn < (slpTabsA ta.toArray tb.toArray prog2).size ∧
      gin < (slpTabsA ta.toArray tb.toArray prog2).size ∧
      hn < (slpTabsA ta.toArray tb.toArray prog2).size ∧
      hin < (slpTabsA ta.toArray tb.toArray prog2).size ∧
      an < (slpTabsA (slpTabsA ta.toArray tb.toArray prog2)[gn]!
        (slpTabsA ta.toArray tb.toArray prog2)[hn]! wprog).size ∧
      bn < (slpTabsA (slpTabsA ta.toArray tb.toArray prog2)[gn]!
        (slpTabsA ta.toArray tb.toArray prog2)[hn]! wprog).size) ∧
    (nodesLt (slpTabsA ta.toArray tb.toArray prog2).size nodes1 = true ∧
      nodesLt (slpTabsA ta.toArray tb.toArray prog2).size nodes2 = true ∧
      nodesLt (slpTabsA ta.toArray tb.toArray prog2).size nodes3 = true) ∧
    invPairOK (Array.range n) (slpTabsA ta.toArray tb.toArray prog2)[gn]!
      (slpTabsA ta.toArray tb.toArray prog2)[gin]! = true ∧
    invPairOK (Array.range n) (slpTabsA ta.toArray tb.toArray prog2)[hn]!
      (slpTabsA ta.toArray tb.toArray prog2)[hin]! = true ∧
    normOK (nodes1.map fun i => (slpTabsA ta.toArray tb.toArray prog2)[i]!)
      (slpTabsA ta.toArray tb.toArray prog2)[gn]! (slpTabsA ta.toArray tb.toArray prog2)[gin]! =
        true ∧
    normOK (nodes3.map fun i => (slpTabsA ta.toArray tb.toArray prog2)[i]!)
      (slpTabsA ta.toArray tb.toArray prog2)[hn]! (slpTabsA ta.toArray tb.toArray prog2)[hin]! =
        true ∧
    notNormOK (nodes3.map fun i => (slpTabsA ta.toArray tb.toArray prog2)[i]!)
      (slpTabsA ta.toArray tb.toArray prog2)[gn]! (slpTabsA ta.toArray tb.toArray prog2)[gin]! =
        true ∧
    notNormOK (nodes1.map fun i => (slpTabsA ta.toArray tb.toArray prog2)[i]!)
      (slpTabsA ta.toArray tb.toArray prog2)[hn]! (slpTabsA ta.toArray tb.toArray prog2)[hin]! =
        true ∧
    (slpTabsA (slpTabsA ta.toArray tb.toArray prog2)[gn]!
        (slpTabsA ta.toArray tb.toArray prog2)[hn]! wprog)[an]! = ta.toArray ∧
    (slpTabsA (slpTabsA ta.toArray tb.toArray prog2)[gn]!
        (slpTabsA ta.toArray tb.toArray prog2)[hn]! wprog)[bn]! = tb.toArray := by
  open CFSG.KC.LQT.PW CFSG.KC.LQT.L CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.RW
    CFSG.KC.LQT.RB CFSG.KC.LQT.RF CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf
    CFSG.KC.LQT.RF.Pf CFSG.KC.LQT.BS.Pf CFSG.KC.LQT.XH CFSG.KC.LQT.XH.Pf
    CFSG.KC.LQT.XR.Pf in
  rw [x1RA] at h
  dsimp only at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hs2, hq1, hq2, hgn, hgin, hhn, hhin, hl1, hl2, hl3, hg1, hg2, hh1, hh2, hN1, hN3,
    hnN3, hnN1, hwso, h30, h31, hKm3, han, hbn, hTa, hTb⟩ := h
  rw [slp2H] at hs2
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hs2
  obtain ⟨hta, htb, hso, hTF0, hTF1, hKm⟩ := hs2
  have h0 : Rep n w (TF2 0) ta.toArray := by
    rw [P.beq_iff.1 hTF0]
    exact rep_codeK hw hta
  have h1 : Rep n w (TF2 1) tb.toArray := by
    rw [P.beq_iff.1 hTF1]
    exact rep_codeK hw htb
  obtain ⟨hlen, hrep⟩ := nodes_rep prog2 TF2 K m _ _ h0 h1 hso hKm hn2
  have hb0 : ∀ p, w * n ≤ p → (TF2 0).testBit p = false := by
    rw [P.beq_iff.1 hTF0]
    exact (vc_codeK hw hta).2
  have hb1 : ∀ p, w * n ≤ p → (TF2 1).testBit p = false := by
    rw [P.beq_iff.1 hTF1]
    exact (vc_codeK hw htb).2
  have hbits := nodes_hb prog2 TF2 hb0 hb1 (nodes_eqn prog2 TF2 K m hKm hn2)
  generalize slpTabsA ta.toArray tb.toArray prog2 = T at hlen hrep ⊢
  have hvc : ∀ j < T.size, VC n w (TF2 j) := fun j hj =>
    ⟨rep_fields (hrep j hj), hbits j (by omega)⟩
  have hN2 : Nat.add (lenA prog2) 2 = T.size := by
    rw [lenA_eq, Nat.add_eq, hlen]
  rw [P.blt_iff, hN2] at hgn hgin hhn hhin
  rw [P.beq_iff] at hg1 hg2 hh1 hh2
  rw [allA_eq, List.all_eq_true] at hq1 hq2
  have hq1' : ∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size := by
    intro p hp
    have := hq1 p hp
    rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, hN2] at this
    exact this
  have hlt : ∀ l : List Nat, P.allL l (fun i => Nat.blt i (Nat.add (lenA prog2) 2)) = true →
      ∀ i ∈ l, i < T.size := by
    intro l hl i hi
    rw [allL_eq, List.all_eq_true] at hl
    have := hl i hi
    rwa [Nat.blt_eq, hN2] at this
  have hnl : ∀ l : List Nat, P.allL l (fun i => Nat.blt i (Nat.add (lenA prog2) 2)) = true →
      nodesLt T.size l = true := by
    intro l hl
    have := hlt l hl
    simp only [nodesLt, List.all_eq_true, decide_eq_true_eq]
    exact this
  have htab : ∀ i < T.size, T[i]! = tabC n w (TF2 i) := fun i hi =>
    rep_unique (hrep i hi) (rep_tabC (rep_fields (hrep i hi)))
  have hmap : ∀ l : List Nat, (∀ i ∈ l, i < T.size) →
      l.map (fun i => T[i]!) = (mapW TF2 l).map (tabC n w) := by
    intro l hl
    rw [mapW_eq, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact htab i (hl i hi)
  have hvL : ∀ l : List Nat, (∀ i ∈ l, i < T.size) → ∀ q ∈ mapW TF2 l, VC n w q := by
    intro l hl q hq
    rw [mapW_eq, List.mem_map] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact hvc i (hl i hi)
  have l1 := hlt _ hl1
  have l3 := hlt _ hl3
  have fG : ∀ i < n, imgW w (TF2 gn) i < n := rep_fields (hrep gn hgn)
  have fGI : ∀ i < n, imgW w (TF2 gin) i < n := rep_fields (hrep gin hgin)
  have fH : ∀ i < n, imgW w (TF2 hn) i < n := rep_fields (hrep hn hhn)
  have fHI : ∀ i < n, imgW w (TF2 hin) i < n := rep_fields (hrep hin hhin)
  have hgr : Rep n w (TF3 0) T[gn]! := by
    rw [P.beq_iff.1 h30]
    exact hrep gn hgn
  have hhr : Rep n w (TF3 1) T[hn]! := by
    rw [P.beq_iff.1 h31]
    exact hrep hn hhn
  obtain ⟨hlen3, hrep3⟩ := nodes_rep wprog TF3 K' m' _ _ hgr hhr hwso hKm3 hn3
  have han' := P.blt_iff.1 han
  have hbn' := P.blt_iff.1 hbn
  rw [lenA_eq, Nat.add_eq] at han' hbn'
  have han'' : an < (slpTabsA T[gn]! T[hn]! wprog).size := by omega
  have hbn'' : bn < (slpTabsA T[gn]! T[hn]! wprog).size := by omega
  refine ⟨fun p hp => ⟨(hq1' p hp).1, (hq1' p hp).2, ?_⟩, ⟨hgn, hgin, hhn, hhin, han'', hbn''⟩,
    ⟨hnl _ hl1, hnl _ hl2, hnl _ hl3⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rep_inv (hrep p.1 (hq1' p hp).1) (hrep p.2 (hq1' p hp).2) hw
      (Nat.eq_of_beq_eq_true (by simpa using hq2 p hp))
  · rw [invPairOK, htab gn hgn, htab gin hgin, compArr_tabC fG fGI, compArr_tabC fGI fG, hg1,
      hg2, tabC_one hw]
    simp
  · rw [invPairOK, htab hn hhn, htab hin hhin, compArr_tabC fH fHI, compArr_tabC fHI fH, hh1,
      hh2, tabC_one hw]
    simp
  · rw [hmap _ l1, htab gn hgn, htab gin hgin, normOK_gen (hvL _ l1) fG fGI]
    exact hN1
  · rw [hmap _ l3, htab hn hhn, htab hin hhin, normOK_gen (hvL _ l3) fH fHI]
    exact hN3
  · rw [hmap _ l3, htab gn hgn, htab gin hgin, notNormOK_gen (hvL _ l3) fG fGI]
    exact hnN3
  · rw [hmap _ l1, htab hn hhn, htab hin hhin, notNormOK_gen (hvL _ l1) fH fHI]
    exact hnN1
  · have := hrep3 an han''
    rw [P.beq_iff.1 hTa] at this
    exact rep_unique this (rep_codeK hw hta)
  · have := hrep3 bn hbn''
    rw [P.beq_iff.1 hTb] at this
    exact rep_unique this (rep_codeK hw htb)

theorem zcl_sound {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
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
  exact Zcl.zcl_main hw B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 PG W BO IB
    PT CT K3 L3 prog2 TF2 K5 m5 nodes1 nodes2 nodes3 K6 L6 h hnd hs hb hcov h2 hn2 hz hzs

end CFSG.KC.LQT.XR

end
