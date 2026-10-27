module

public import Certificates.Data.Kernel.LocalQT.Fusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion

import CFSG.Certificates.Kernel.LocalQTBaseWProved
import CFSG.Certificates.Kernel.LocalQTLatKSound
import all CFSG.Certificates.Kernel.LocalQTBaseProved
import all CFSG.Certificates.Kernel.LocalQTFusionEnum

namespace CFSG.KC.LQT.FU

open CFSG.KC.Ord CFSG.KC.LQT.L CFSG.KC.LQT.BC CFSG.KC.LQT.BC.Pf
open CFSG.KC.LQT.BW.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2

variable {n : Nat}

section Idx

variable {N g gi : Nat} {par cl : Array Nat} {Gc : List Nat} {Lx : Nat → Nat}

theorem CayL.genIdx_spec (h : CayL n N g gi par cl Gc Lx) {i : Nat} (hi : i < N) (hi0 : 0 < i) :
    RankCert.genIdx g gi par cl i < g ∧
      Lx i = P.mul n (Gc.getD (RankCert.genIdx g gi par cl i) 0) (Lx par[i]!) ∧
      cl[par[i]! * (g + gi) + RankCert.genIdx g gi par cl i]! = i := by
  obtain ⟨hlt, j, hj, hij⟩ := h.parent i hi hi0
  obtain ⟨hcl1, hcl2⟩ := h.step par[i]! (hlt.trans hi) j hj
  have hcli : cl[par[i]! * (g + gi) + j]! = i := h.inj _ hcl1 i hi (by rw [hcl2, hij])
  have hex : ∃ j' ∈ List.range g, (cl[par[i]! * (g + gi) + j']! == i) = true :=
    ⟨j, List.mem_range.mpr hj, by simp [hcli]⟩
  have hfind : ((List.range g).find? fun j => cl[par[i]! * (g + gi) + j]! == i).isSome = true :=
    List.find?_isSome.mpr hex
  obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp hfind
  have hgi : RankCert.genIdx g gi par cl i = j' := by
    unfold RankCert.genIdx
    rw [hj']
    rfl
  have hmem := List.find?_some hj'
  have hj'g : j' < g := List.mem_range.mp (List.mem_of_find?_eq_some hj')
  have hcli' : cl[par[i]! * (g + gi) + j']! = i := by simpa using hmem
  refine ⟨by rw [hgi]; exact hj'g, ?_, by rw [hgi]; exact hcli'⟩
  obtain ⟨-, hcl2'⟩ := h.step par[i]! (hlt.trans hi) j' hj'g
  rw [hgi, ← hcl2', hcli']

theorem CayL.mulIdx_spec (hn : n ≤ 32) (h : CayL n N g gi par cl Gc Lx)
    (hgc : ∀ j < g, Can n (Gc.getD j 0)) :
    ∀ (f i k : Nat), i ≤ f → i < N → k < N →
      RankCert.mulIdx g gi par cl f i k < N ∧
      Lx (RankCert.mulIdx g gi par cl f i k) = P.mul n (Lx i) (Lx k) := by
  intro f
  induction f with
  | zero =>
    intro i k hif hi hk
    obtain rfl : i = 0 := by omega
    have e : RankCert.mulIdx g gi par cl 0 0 k = k := by simp [RankCert.mulIdx]
    rw [e]
    exact ⟨hk, by rw [h.zero, one_mul' hn (h.can k hk)]⟩
  | succ f ih =>
    intro i k hif hi hk
    by_cases hi0 : i = 0
    · subst hi0
      have e : RankCert.mulIdx g gi par cl (f + 1) 0 k = k := by simp [RankCert.mulIdx]
      rw [e]
      exact ⟨hk, by rw [h.zero, one_mul' hn (h.can k hk)]⟩
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      obtain ⟨hgi', hLi, -⟩ := h.genIdx_spec hi hpos
      obtain ⟨hlt, -⟩ := h.parent i hi hpos
      obtain ⟨h1, h2⟩ := ih par[i]! k (by omega) (hlt.trans hi) hk
      obtain ⟨h3, h4⟩ := h.step _ h1 _ hgi'
      simp only [RankCert.mulIdx, hi0, ite_false]
      refine ⟨h3, ?_⟩
      rw [h4, h2, hLi, mul_assoc' hn (hgc _ hgi') (h.can _ (hlt.trans hi)) (h.can k hk)]

theorem nodeRep_one (hn : n ≤ 32) : NodeRep n (P.one n) (Array.range n) := by
  refine ⟨by simp, can_one hn, fun i hi => ?_⟩
  rw [img_one hn hi]
  simp [img, hi]

theorem CayL.idxTab_spec (hn : n ≤ 32) (h : CayL n N g gi par cl Gc Lx)
    {Gt : List (Array Nat)} (hrep : ∀ j < g, NodeRep n (Gc.getD j 0) (Gt.getD j #[])) :
    ∀ (f i : Nat), i ≤ f → i < N →
      NodeRep n (Lx i) (FusionCert.idxTab n Gt g gi par cl f i) := by
  intro f
  induction f with
  | zero =>
    intro i hif hi
    obtain rfl : i = 0 := by omega
    rw [h.zero]
    simpa [FusionCert.idxTab] using nodeRep_one hn
  | succ f ih =>
    intro i hif hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [h.zero]
      simpa [FusionCert.idxTab] using nodeRep_one hn
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      obtain ⟨hgi', hLi, -⟩ := h.genIdx_spec hi hpos
      obtain ⟨hlt, -⟩ := h.parent i hi hpos
      simp only [FusionCert.idxTab, hi0, ite_false]
      rw [hLi]
      exact nodeRep_mul hn (hrep _ hgi') (ih par[i]! (by omega) (hlt.trans hi))

end Idx

theorem wordAB_rep (hn : n ≤ 32) {a b : Nat} {ta tb : Array Nat} (ha : NodeRep n a ta)
    (hb : NodeRep n b tb) :
    ∀ w : List Nat, NodeRep n (wordAB n a b w) (FusionCert.wordTab n ta tb w)
  | [] => nodeRep_one hn
  | x :: w => by
    have e1 : wordAB n a b (x :: w) =
        P.mul n (Bool.rec (motive := fun _ => Nat) b a (Nat.beq x 0)) (wordAB n a b w) := rfl
    have e2 : FusionCert.wordTab n ta tb (x :: w) =
        compArr (if x = 0 then ta else tb) (FusionCert.wordTab n ta tb w) := rfl
    rw [e1, e2]
    by_cases hx : x = 0
    · subst hx
      rw [if_pos rfl]
      exact nodeRep_mul hn ha (wordAB_rep hn ha hb w)
    · have hb0 : Nat.beq x 0 = false := Bool.eq_false_iff.2 fun e => hx (P.beq_iff.1 e)
      rw [if_neg hx, hb0]
      exact nodeRep_mul hn hb (wordAB_rep hn ha hb w)

theorem gwsK_spec {L cs : List Nat} :
    ∀ (Gc : List Nat) (gws : List (List Nat)), gwsK n L cs Gc gws = true →
      ∀ j < Gc.length, prodIdx n L cs (gws.getD j []) = Gc.getD j 0
  | [], _, _, j, hj => by simp at hj
  | g :: Gc, gws, h, j, hj => by
    cases gws with
    | nil =>
      change CFSG.KC.Ord.andB (Nat.beq (P.one n) g) (gwsK n L cs Gc []) = true at h
      rw [P.andB_iff, P.beq_iff] at h
      cases j with
      | zero => exact h.1
      | succ j =>
        have := gwsK_spec Gc [] h.2 j (by simpa using hj)
        simpa using this
    | cons w gws =>
      change CFSG.KC.Ord.andB (Nat.beq (prodIdx n L cs w) g) (gwsK n L cs Gc gws) = true at h
      rw [P.andB_iff, P.beq_iff] at h
      cases j with
      | zero => exact h.1
      | succ j =>
        have := gwsK_spec Gc gws h.2 j (by simpa using hj)
        simpa using this

theorem prodIdx_eq' {L cs : List Nat} :
    ∀ w : List Nat, prodIdx n L cs w =
      w.foldr (fun p acc => P.mul n (L.getD (cs.getD p 0) 0) acc) (P.one n)
  | [] => rfl
  | p :: w => by
    change P.mul n (CFSG.KC.LQT.S.getK L (CFSG.KC.LQT.S.getK cs p)) (prodIdx n L cs w) = _
    rw [getK_eq, getK_eq, prodIdx_eq' w]
    rfl

theorem evalIdx_spec (hn : n ≤ 32) {N g gi : Nat} {par cl : Array Nat} {Gc L cidx : List Nat}
    (h : CayL n N g gi par cl Gc (fun i => L.getD i 0)) (hgc : ∀ j < g, Can n (Gc.getD j 0))
    (hc : ∀ p ∈ cidx, p < N) :
    ∀ w : List Nat,
      FusionCert.evalIdxWord (RankCert.mulIdx g gi par cl N) cidx w < N ∧
      L.getD (FusionCert.evalIdxWord (RankCert.mulIdx g gi par cl N) cidx w) 0 =
        prodIdx n L cidx w
  | [] => ⟨h.pos, by rw [prodIdx_eq']; exact h.zero⟩
  | q :: w => by
    obtain ⟨h1, h2⟩ := evalIdx_spec hn h hgc hc w
    have hq : cidx.getD q 0 < N := by
      by_cases hql : q < cidx.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hql, Option.getD_some]
        exact hc _ (List.getElem_mem hql)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        exact h.pos
    obtain ⟨h3, h4⟩ := CayL.mulIdx_spec hn h hgc N (cidx.getD q 0) _ (le_of_lt hq) hq h1
    rw [FusionCert.evalIdxWord_cons]
    refine ⟨h3, ?_⟩
    rw [h4, prodIdx_eq', List.foldr_cons, ← prodIdx_eq', ← h2]

theorem conj_rep {zc gc gic : Nat} {zt gt git : Array Nat} (hz : NodeRep n zc zt)
    (hg' : NodeRep n gc gt) (hgi : NodeRep n gic git) {p : Nat} (hp : p < n) :
    conjImg zt gt git p = P.img (P.mul n gic (P.mul n zc gc)) p := by
  rw [conjImg, img_mul hp, img_mul hp, hg'.2.2 p hp, hz.2.2 _ (nodeRep_lt hg' p hp),
    hgi.2.2 _ (nodeRep_lt hz _ (nodeRep_lt hg' p hp))]

end CFSG.KC.LQT.FU

public section

namespace CFSG.KC.LQT.BC

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2 CFSG.KC.LQT.BC.Pf
open CFSG.KC.LQT.FU
open CFSG.KC.LQT.BW.Pf (andB_eq allA_eq allBs_cons allBs_nil lenA_eq getK_eq getD_mem)

theorem fusion_sound {n : Nat} (hn : n ≤ 24) (ta tb : List Nat) (prog : List (Nat × Nat))
    (qp : List (Nat × Nat)) (L : List Nat) (zi : Nat) (wits : List (List Nat × List Nat × Nat))
    (gws : List (List Nat)) (fuel : Nat)
    (h : fusionK n ta tb prog qp L zi wits gws fuel = true) :
    FusionCert.fusionCheck n (List.range n) ta.toArray tb.toArray
      (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2
      zi wits gws = true := by
  have h32 : n ≤ 32 := by omega
  rw [fusionK, andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hR⟩ := h
  obtain ⟨hlen, hrep⟩ := slpK_rep h32 hta htb hso
  have hra := nodeRep_codeL h32 hta
  have hrb := nodeRep_codeL h32 htb
  generalize slpTabsA ta.toArray tb.toArray prog = T at hlen hrep ⊢
  rw [P.letB_eq, P.letB_eq] at hR
  generalize slpK n (codeL ta) (codeL tb) prog = R at hlen hrep hR
  rw [fusionR, P.andB_iff] at hR
  obtain ⟨hqp, hQ⟩ := hR
  rw [fusionQ, P.andB_iff, P.andB_iff, P.andB_iff, P.letB_eq] at hQ
  simp only [LK.recMap] at hQ
  obtain ⟨hfu, hord, hzlt, hrest⟩ := hQ
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hrest
  obtain ⟨hz1, hz2, hz3, hz4, hz5, hz6⟩ := hrest
  rw [allA_eq, List.all_eq_true] at hqp
  have hq1 : ∀ p ∈ qp, p.1 < T.size := fun p hp => by
    have := hqp p hp
    rwa [P.blt_iff, hlen] at this
  generalize hzdef : S.getK L zi = z at hz1 hz2 hz3 hz4 hz5
  have hzL : L.getD zi 0 = z := by rw [← getK_eq]; exact hzdef
  let Gp : List (Nat × Array Nat) := qp.map fun p => (nodeK R p.1, T[p.1]!)
  have hGp1 : Gp.map Prod.fst = qp.map fun p => nodeK R p.1 := by
    simp only [Gp, List.map_map]; rfl
  have hGp2 : Gp.map Prod.snd = qp.map fun p => T[p.1]! := by
    simp only [Gp, List.map_map]; rfl
  have hGrep : ∀ p ∈ Gp, NodeRep n p.1 p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact hrep _ (hq1 q hq)
  have hG : ∀ s ∈ Gp.map Prod.snd, ∀ q < n, img s q < n := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
    exact nodeRep_lt (hGrep p hp)
  have hfuel : L.length ≤ fuel := by
    have := Nat.le_of_ble_eq_true hfu
    rwa [lenA_eq] at this
  obtain ⟨hsz, hTs, hcay⟩ := enum_cay (L := L) h32 hG
    (fun p hp => ⟨hGrep p hp, List.mem_map_of_mem hp⟩) (qp.map fun p => T[p.2]!) hfuel
    (by rw [hGp1]; exact hord)
  have hl1 : Gp.length = qp.length := List.length_map ..
  have hl2 : (qp.map fun p => T[p.2]!).length = qp.length := List.length_map ..
  rw [hGp2] at hsz hTs
  rw [hGp1, hGp2, hl1, hl2] at hcay
  generalize bfsEnumB n (List.range n) (qp.map fun p => T[p.1]!) (qp.map fun p => T[p.2]!) fuel
    = E at hsz hTs hcay ⊢
  obtain ⟨Ts, par, cl⟩ := E
  simp only at hsz hTs hcay ⊢
  have hgj : ∀ j < qp.length, NodeRep n ((qp.map fun p => nodeK R p.1).getD j 0)
      ((qp.map fun p => T[p.1]!).getD j #[]) := by
    intro j hj
    have := hrep _ (hq1 qp[j] (List.getElem_mem hj))
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
    simpa using this
  have hgc : ∀ j < qp.length, Can n ((qp.map fun p => nodeK R p.1).getD j 0) :=
    fun j hj => (hgj j hj).2.1
  have hmul := fun i k (hi : i < L.length) (hk : k < L.length) =>
    CayL.mulIdx_spec h32 hcay (by rw [hGp1] at *; exact hgc) L.length i k (le_of_lt hi) hi hk
  have hzero : L.getD 0 0 = P.one n := hcay.zero
  have hcan : ∀ i < L.length, Can n (L.getD i 0) := hcay.can
  have hinj : ∀ i < L.length, ∀ k < L.length, L.getD i 0 = L.getD k 0 → i = k := hcay.inj
  have hcl0 : ∀ j < qp.length, cl[j]! < L.length ∧
      L.getD cl[j]! 0 = (qp.map fun p => nodeK R p.1).getD j 0 := by
    intro j hj
    have := hcay.step 0 hcay.pos j hj
    simp only [Nat.zero_mul, Nat.zero_add] at this
    obtain ⟨h1, h2⟩ := this
    refine ⟨h1, ?_⟩
    have h2' : L.getD cl[j]! 0 =
        P.mul n ((qp.map fun p => nodeK R p.1).getD j 0) (L.getD 0 0) := h2
    rw [h2', hzero, mul_one' h32 (hgc j hj)]
  have hzN : zi < L.length := by
    have := P.blt_iff.1 hzlt
    rwa [lenA_eq] at this
  have hGcmem : ∀ j < qp.length, (qp.map fun p => nodeK R p.1).getD j 0 ∈
      qp.map fun p => nodeK R p.1 := fun j hj => getD_mem (by simpa using hj)
  have hG2 : ∀ s ∈ qp.map fun p => T[p.1]!, ∀ q < n, img s q < n := by
    rw [← hGp2]
    exact hG
  rw [allA_eq, List.all_eq_true] at hz5
  have hwlt : ∀ wit ∈ wits, wit.2.2 < L.length := by
    intro wit hwit
    have h5 := hz5 wit hwit
    rw [witK, P.letB_eq, P.letB_eq, P.andB_iff, P.andB_iff, P.blt_iff] at h5
    have := h5.1
    rwa [lenA_eq] at this
  simp only [FusionCert.fusionCheck, List.length_map, hsz, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨hzN, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rintro rfl
    have hz : z = P.one n := by rw [← hzL, hzero]
    rw [P.notB_iff, P.beq_iff] at hz1
    exact hz1 hz
  · obtain ⟨h1, h2⟩ := hmul zi zi hzN hzN
    apply hinj _ h1 0 hcay.pos
    rw [h2, hzL, hzero]
    exact P.beq_iff.1 hz2
  · intro j hj
    obtain ⟨hc1, hc2⟩ := hcl0 j hj
    obtain ⟨h1, h2⟩ := hmul cl[j]! zi hc1 hzN
    obtain ⟨h3, h4⟩ := hmul zi cl[j]! hzN hc1
    apply hinj _ h1 _ h3
    rw [h2, h4, hc2, hzL]
    exact P.beq_iff.1 ((P.allL_iff _ _).1 hz3 _ (hGcmem j hj))
  · intro i hi
    by_cases hall : ((List.range qp.length).all fun j =>
        RankCert.mulIdx qp.length qp.length par cl L.length cl[j]! i ==
          RankCert.mulIdx qp.length qp.length par cl L.length i cl[j]!) = true
    · have hcomm : ∀ y ∈ qp.map (fun p => nodeK R p.1),
          P.mul n y (L.getD i 0) = P.mul n (L.getD i 0) y := by
        intro y hy
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
        have hj' : j < qp.length := by simpa using hj
        have hgj' : (qp.map fun p => nodeK R p.1)[j] =
            (qp.map fun p => nodeK R p.1).getD j 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        rw [hgj']
        have := (List.all_eq_true.1 hall) j (List.mem_range.2 hj')
        rw [beq_iff_eq] at this
        obtain ⟨hc1, hc2⟩ := hcl0 j hj'
        obtain ⟨h1, h2⟩ := hmul cl[j]! i hc1 hi
        obtain ⟨h3, h4⟩ := hmul i cl[j]! hi hc1
        rw [← hc2, ← h2, ← h4, this]
      have h4 := (P.allL_iff _ _).1 hz4 (L.getD i 0) (getD_mem hi)
      have h5 := P.impB_iff.1 h4 ((P.allL_iff _ _).2 fun y hy => P.beq_iff.2 (hcomm y hy))
      rw [P.orB_iff, P.beq_iff, P.beq_iff] at h5
      rcases h5 with h5 | h5
      · exact Or.inl (Or.inr (hinj i hi 0 hcay.pos (by rw [hzero]; exact h5)))
      · exact Or.inr (hinj i hi zi hzN (by rw [hzL]; exact h5))
    · exact Or.inl (Or.inl (Bool.eq_false_iff.2 hall))
  · intro wit hwit
    have hc' := hwlt wit hwit
    have hwk := hz5 wit hwit
    rw [witK, P.letB_eq, P.letB_eq, P.andB_iff, P.andB_iff, P.blt_iff, P.beq_iff, P.beq_iff]
      at hwk
    obtain ⟨-, hinv, hconj⟩ := hwk
    have hzt : NodeRep n z
        (FusionCert.idxTab n (qp.map fun p => T[p.1]!) qp.length qp.length par cl L.length zi) :=
      hzL ▸ hcay.idxTab_spec h32 hgj L.length zi (le_of_lt hzN) hzN
    have hX := wordAB_rep h32 hra hrb wit.1
    have hY := wordAB_rep h32 hra hrb wit.2.1
    simp only [FusionCert.witOK, FusionCert.invTabs, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range, beq_iff_eq, hsz]
    refine ⟨⟨hc', fun q hq => inv_of_mul h32 hX hY hinv q hq⟩, ?_⟩
    rw [hTs _ hc', Tab]
    apply List.map_congr_left
    intro p hp
    rw [conj_rep hzt hX hY (ptsOf_lt hG2 p hp), hconj, getK_eq]
  · intro j hj
    have hcs : ∀ p ∈ wits.map (fun w => w.2.2), p < L.length := by
      intro p hp
      obtain ⟨wit, hwit, rfl⟩ := List.mem_map.1 hp
      exact hwlt wit hwit
    obtain ⟨h1, h2⟩ := evalIdx_spec h32 hcay hgc hcs (gws.getD j [])
    have h3 := gwsK_spec _ gws hz6 j (by simpa using hj)
    apply hinj _ h1 _ (hcl0 j hj).1
    rw [h2, h3, (hcl0 j hj).2]

end CFSG.KC.LQT.BC

end


