module

public import Certificates.Data.Kernel.E81K
public import CFSG.Certificates.Kernel.PGrpMul
import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

namespace CFSG.KC.E81K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.PGrp
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Monster.B.Co2 (permOfArr eqA_iff rep_compA allLt_iff)

structure Pin (n w : ℕ) (ps : List ℕ) where
  ng : ℕ
  N : ℕ
  G : ℕ → ℕ
  T : ℕ → ℕ
  E : ℕ → ℕ
  S : ℕ → ℕ
  SK : List ℕ
  ok : bfsK n w ng G N T E S = true
  keys : keysSK n w ps N T SK = true

section Cov

variable {n w : ℕ}

theorem eq_of_beq {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem cov_of {nh nd : ℕ} {H ND : ℕ → ℕ} {DT : ℕ → ℕ → ℕ} {Z Z2 : ℕ} {ZW : ℕ → ℕ}
    (hZ2 : pcomp n w (mask w) Z Z = Z2) (hzw : ∀ x < nh * nd, zwK n w nh H ND DT Z ZW x = true)
    {c s : ℕ} (h : covK n w nh nd H ND DT Z Z2 ZW c s = true) :
    (pcomp n w (mask w) s (pcomp n w (mask w) s s) ≠ pidn n w ∨ s = pidn n w ∨ s = Z ∨
        s = pcomp n w (mask w) Z Z) ∨
      ∃ i < nh, ∃ t < nd, ∃ j < ND t, ∃ j' < ND t,
        pcomp n w (mask w) (H i) s = pcomp n w (mask w) (DT t j) (H i) ∧
          pcomp n w (mask w) (H i) Z = pcomp n w (mask w) (DT t j') (H i) := by
  unfold covK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · left
    rcases h with ((h | h) | h) | h
    · left
      intro e
      rw [e, Nat.beq_refl] at h
      exact absurd h (by decide)
    · exact Or.inr (Or.inl (eq_of_beq h))
    · exact Or.inr (Or.inr (Or.inl (eq_of_beq h)))
    · rw [hZ2]
      exact Or.inr (Or.inr (Or.inr (eq_of_beq h)))
  · right
    unfold covW at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hx, hj⟩, hz⟩, he⟩ := h
    generalize (c - 1) % (nh * nd) = x at hx hj hz he
    generalize (c - 1) / (nh * nd) = j at hj he
    have hx' : x < nh * nd := Nat.blt_eq.mp hx
    have hnh : 0 < nh := Nat.pos_of_ne_zero fun e => by rw [e, Nat.zero_mul] at hx'; omega
    have hzx := hzw x hx'
    unfold zwK at hzx
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hzx
    have hz0 : 0 < ZW x := Nat.blt_eq.mp hz
    rcases hzx with hzx | ⟨hle, hzx⟩
    · rw [eq_of_beq hzx] at hz0
      exact absurd hz0 (by decide)
    refine ⟨x % nh, Nat.mod_lt _ hnh, x / nh, ?_, j, Nat.blt_eq.mp hj, ZW x - 1, ?_, eq_of_beq he,
      eq_of_beq hzx⟩
    · rw [Nat.div_lt_iff_lt_mul hnh, Nat.mul_comm]
      exact hx'
    · have := Nat.le_of_ble_eq_true hle
      omega

end Cov

section Glue

variable {n w : ℕ} (hw : szOK n w = true)
include hw

omit hw in
theorem getMap {α β : Type} [Inhabited α] [Inhabited β] (A : Array α) (f : α → β) {k : ℕ}
    (hk : k < A.size) : (A.map f)[k]! = f A[k]! := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, getElem!_pos A k hk]

omit hw in
theorem map_get {W : Array (List ℕ)} {f : List ℕ → ℕ} {G : ℕ → ℕ} {m : ℕ}
    (h : W.toList.map f = (List.range m).map G) : W.size = m ∧ ∀ k < m, f W[k]! = G k := by
  have hs : W.size = m := by simpa using congrArg List.length h
  refine ⟨hs, fun k hk => ?_⟩
  have hk' : k < (W.toList.map f).length := by simp [hs, hk]
  have e := List.getElem_of_eq h hk'
  rw [List.getElem_map, List.getElem_map, List.getElem_range, Array.getElem_toList] at e
  rw [getElem!_pos W k (by omega)]
  exact e

omit hw in
theorem letters_of_toList {W : Array (List ℕ)} {m : ℕ}
    (h : (W.toList.all fun w => w.all fun l => decide (l < m)) = true) :
    ∀ k < W.size, ∀ l ∈ W[k]!, l < m := by
  intro k hk l hl
  rw [List.all_eq_true] at h
  have h1 := h W[k]! (by rw [getElem!_pos W k hk]; exact Array.getElem_mem_toList hk)
  simpa using List.all_eq_true.1 h1 l hl

theorem words {gs : Array (Array ℕ)} {ng : ℕ} {G : ℕ → ℕ}
    (hg : ∀ l < ng, gs[l]! = unpack n w (G l)) (hp : ∀ l < ng, permB n w (G l) = true)
    {W : Array (List ℕ)} {m : ℕ} {F : ℕ → ℕ}
    (hW : W.toList.map (posWordK n w G) = (List.range m).map F)
    (hl : (W.toList.all fun wd => wd.all fun l => decide (l < ng)) = true) :
    (W.map (posWord n gs)).size = m ∧
      ∀ k < m, (W.map (posWord n gs))[k]! = unpack n w (F k) ∧ permB n w (F k) = true := by
  obtain ⟨hs, he⟩ := map_get hW
  refine ⟨by rw [Array.size_map, hs], fun k hk => ?_⟩
  have hk' : k < W.size := by rw [hs]; exact hk
  obtain ⟨e, p⟩ := posWord_unpack hw hg hp (letters_of_toList hl k hk')
  rw [he k hk] at e p
  rw [getMap W _ hk']
  exact ⟨e, p⟩

omit hw in
theorem pin_facts {gs : Array (Array ℕ)} {ps : List ℕ} (P : Pin n w ps) {fuel : ℕ}
    (hs : gs.size = P.ng)
    (hg : ∀ k < P.ng, gs[k]! = unpack n w (P.G k) ∧ permB n w (P.G k) = true)
    (hps : ∀ p ∈ ps, p < n) (hf : P.N ≤ fuel) :
    (enumBfs n gs ps fuel).pts = Array.ofFn (n := P.N) (fun i => unpack n w (P.T i.val)) ∧
      enumOK n gs ps (enumBfs n gs ps fuel) = true ∧
      ∀ i < P.N, (enumBfs n gs ps fuel).pts[i]! = unpack n w (P.T i) ∧
        permB n w (P.T i) = true := by
  have hpts := enumBfs_pts_base hs (fun k hk => (hg k hk).1) P.ok hps P.keys hf
  refine ⟨hpts, enumOK_of_bfsK_base hs (fun k hk => (hg k hk).1) (fun k hk => (hg k hk).2) P.ok
    hps P.keys hf, fun i hi => ⟨?_, permB_of_pp (PP_pts P.ok (fun k hk => (hg k hk).2) i hi)⟩⟩
  rw [hpts, getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

omit hw in
theorem mem_ofFn {α : Type} {N j : ℕ} (f : Fin N → α) (hj : j < N) :
    f ⟨j, hj⟩ ∈ (Array.ofFn f).toList := by
  have h := Array.getElem_mem_toList (xs := Array.ofFn f) (i := j) (by simpa using hj)
  rwa [Array.getElem_ofFn] at h

theorem conj_eq {p q d : ℕ} (hp : permB n w p = true) (hq : permB n w q = true)
    (hd : permB n w d = true) (e : pcomp n w (mask w) p q = pcomp n w (mask w) d p) :
    eqA n (conjA n (unpack n w p) (unpack n w q)) (unpack n w d) = true := by
  have vH := BfsPin.validA_unpack hp
  have vQ := BfsPin.validA_unpack hq
  have vD := BfsPin.validA_unpack hd
  have e3 : compA n (unpack n w p) (unpack n w q) = compA n (unpack n w d) (unpack n w p) := by
    rw [comp_unpack' hw hp hq, comp_unpack' hw hd hp, e]
  have r1 := rep_compA (rep_of_validA vH) (rep_of_validA vQ)
  have r2 := rep_compA (rep_of_validA vD) (rep_of_validA vH)
  rw [e3] at r1
  have e4 := r1.unique r2
  refine (eqA_iff (rep_conjA vH (rep_of_validA vQ)) (rep_of_validA vD)).2 ?_
  rw [e4, mul_inv_cancel_right]

omit hw in
theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem e81Check_of_pins (X : E81Data) (hn : X.n = n) {mp : ℕ} (PG : ℕ → ℕ)
    (hpg : X.pg.size = mp) (hpgE : ∀ j < mp, X.pg[j]! = unpack n w (PG j))
    (hpgP : ∀ j < mp, permB n w (PG j) = true)
    (hkeys : (X.qKeys ++ X.rKeys ++ X.dKeys).all (fun p => decide (p < n)) = true)
    (Q : Pin n w X.qKeys) (R : Pin n w X.rKeys) (D : ℕ → Pin n w X.dKeys) {nh : ℕ} (H : ℕ → ℕ)
    (Z : ℕ)
    (hlq : (X.qW.toList.all fun wd => wd.all fun l => decide (l < mp)) = true)
    (hlh : (X.hW.toList.all fun wd => wd.all fun l => decide (l < mp)) = true)
    (hlz : X.zW.all (fun l => decide (l < Q.ng)) = true)
    (hlr : (X.rW.toList.all fun wd => wd.all fun l => decide (l < Q.ng)) = true)
    (hld : (X.dW.toList.all fun ws => ws.toList.all fun wd => wd.all fun l => decide (l < Q.ng))
      = true)
    (hwQ : X.qW.toList.map (posWordK n w PG) = (List.range Q.ng).map Q.G)
    (hQN : X.qOrd = Q.N) (hQf : Q.N ≤ X.qFuel)
    (hZ : posWordK n w Q.G X.zW = Z) (hZ3 : pcomp n w (mask w) Z (pcomp n w (mask w) Z Z) = pidn n w)
    (hZ1 : Z ≠ pidn n w)
    (hZc : ∀ k < Q.ng, pcomp n w (mask w) Z (Q.G k) = pcomp n w (mask w) (Q.G k) Z)
    (hwR : X.rW.toList.map (posWordK n w Q.G) = (List.range R.ng).map R.G)
    (hRN : X.rOrd = R.N) (hRf : R.N ≤ X.rFuel) (hQR : X.qOrd ≤ 3 * X.rOrd)
    (hwD : ∀ t < X.dW.size,
      X.dW[t]!.toList.map (posWordK n w Q.G) = (List.range (D t).ng).map (D t).G)
    (hDN : ∀ t < X.dW.size, 81 ≤ (D t).N ∧ (D t).N ≤ X.dFuel)
    (hDe : ∀ t < X.dW.size, ∀ a < (D t).ng,
      pcomp n w (mask w) ((D t).G a) (pcomp n w (mask w) ((D t).G a) ((D t).G a)) = pidn n w ∧
        ∀ b < (D t).ng,
          pcomp n w (mask w) ((D t).G a) ((D t).G b) = pcomp n w (mask w) ((D t).G b) ((D t).G a))
    (hwH : X.hW.toList.map (posWordK n w PG) = (List.range nh).map H)
    (hcov : ∀ k < R.N,
      (pcomp n w (mask w) (R.T k) (pcomp n w (mask w) (R.T k) (R.T k)) ≠ pidn n w ∨
          R.T k = pidn n w ∨ R.T k = Z ∨ R.T k = pcomp n w (mask w) Z Z) ∨
        ∃ i < nh, ∃ t < X.dW.size, ∃ j < (D t).N, ∃ j' < (D t).N,
          pcomp n w (mask w) (H i) (R.T k) = pcomp n w (mask w) ((D t).T j) (H i) ∧
            pcomp n w (mask w) (H i) Z = pcomp n w (mask w) ((D t).T j') (H i)) :
    e81Check X = true := by
  have permId : permB n w (pidn n w) = true := permB_of_pp (PP.id hw)
  have hk' := hkeys
  simp only [List.all_eq_true, List.mem_append, decide_eq_true_eq] at hk'
  have psQ : ∀ p ∈ X.qKeys, p < n := fun p hp => hk' p (Or.inl (Or.inl hp))
  have psR : ∀ p ∈ X.rKeys, p < n := fun p hp => hk' p (Or.inl (Or.inr hp))
  have psD : ∀ p ∈ X.dKeys, p < n := fun p hp => hk' p (Or.inr hp)
  have hq := words hw hpgE hpgP hwQ hlq
  have hqE := pin_facts Q (fuel := X.qFuel) hq.1 hq.2 psQ hQf
  obtain ⟨hzE, hZp⟩ := posWord_unpack hw (gs := X.qW.map (posWord n X.pg)) (fun l hl => (hq.2 l hl).1)
    (fun l hl => (hq.2 l hl).2) (by simpa using hlz)
  rw [hZ] at hzE hZp
  have hr := words hw (fun l hl => (hq.2 l hl).1) (fun l hl => (hq.2 l hl).2) hwR hlr
  have hrE := pin_facts R (fuel := X.rFuel) hr.1 hr.2 psR hRf
  have hldt : ∀ t < X.dW.size,
      (X.dW[t]!.toList.all fun wd => wd.all fun l => decide (l < Q.ng)) = true := by
    intro t ht
    rw [List.all_eq_true] at hld
    exact hld _ (by rw [getElem!_pos X.dW t ht]; exact Array.getElem_mem_toList ht)
  have hd : ∀ t < X.dW.size,
      (X.dW[t]!.map (posWord n (X.qW.map (posWord n X.pg)))).size = (D t).ng ∧
        ∀ k < (D t).ng, (X.dW[t]!.map (posWord n (X.qW.map (posWord n X.pg))))[k]! =
          unpack n w ((D t).G k) ∧ permB n w ((D t).G k) = true := fun t ht =>
    words hw (gs := X.qW.map (posWord n X.pg)) (fun l hl => (hq.2 l hl).1)
      (fun l hl => (hq.2 l hl).2) (hwD t ht) (hldt t ht)
  have hh := words hw hpgE hpgP hwH hlh
  unfold e81Check e81Check' qCert zArr rCert dPairs hArrs
  unfold rGens
  unfold qGens
  rw [hn]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hqE.2.1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, hrE.2.1⟩, ?_⟩, decide_eq_true hQR⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allLt_iff, hpg]
    intro k hk
    rw [hpgE k hk]
    exact BfsPin.validA_unpack (hpgP k hk)
  · exact hkeys
  · rw [← Array.all_toList, hpg]
    exact hlq
  · rw [← Array.all_toList, hpg]
    exact hlh
  · rw [hq.1]
    exact hlz
  · rw [← Array.all_toList, hq.1]
    exact hlr
  · rw [hq.1]
    simpa only [Array.all_toList] using hld
  · rw [hqE.1, Array.size_ofFn, hQN]
    exact beq_self_eq_true _
  · rw [hzE]
    exact BfsPin.validA_unpack hZp
  · rw [hzE, comp_unpack' hw hZp hZp, comp_unpack' hw hZp (PGrp.permB_pcomp hw hZp hZp),
      idA_eq hw, eqA_unpack' hw (PGrp.permB_pcomp hw hZp (PGrp.permB_pcomp hw hZp hZp)) permId,
      hZ3]
    exact Nat.beq_refl _
  · rw [hzE, idA_eq hw, eqA_unpack' hw hZp permId, beq_false hZ1]
    rfl
  · rw [allLt_iff, hq.1]
    intro k hk
    obtain ⟨e, p⟩ := hq.2 k hk
    rw [hzE, e, comp_unpack' hw hZp p, comp_unpack' hw p hZp,
      eqA_unpack' hw (PGrp.permB_pcomp hw hZp p) (PGrp.permB_pcomp hw p hZp), hZc k hk]
    exact Nat.beq_refl _
  · rw [hrE.1, Array.size_ofFn, hRN]
    exact beq_self_eq_true _
  · rw [List.all_eq_true]
    intro p hp
    rw [Array.toList_map, List.mem_map] at hp
    obtain ⟨ws, hws, rfl⟩ := hp
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hws
    have ht' : t < X.dW.size := by simpa using ht
    have e : X.dW.toList[t] = X.dW[t]! := by rw [Array.getElem_toList, getElem!_pos X.dW t ht']
    rw [e]
    obtain ⟨hdp, hde, -⟩ := pin_facts (D t) (fuel := X.dFuel) (hd t ht').1 (hd t ht').2 psD
      (hDN t ht').2
    dsimp only
    simp only [Bool.and_eq_true]
    refine ⟨⟨hde, ?_⟩, ?_⟩
    · rw [hdp, Array.size_ofFn]
      exact decide_eq_true (hDN t ht').1
    · unfold elemAbOK
      rw [allLt_iff, (hd t ht').1]
      intro a ha
      obtain ⟨ea, pa⟩ := (hd t ht').2 a ha
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [ea, comp_unpack' hw pa pa, comp_unpack' hw pa (PGrp.permB_pcomp hw pa pa), idA_eq hw,
          eqA_unpack' hw (PGrp.permB_pcomp hw pa (PGrp.permB_pcomp hw pa pa)) permId,
          (hDe t ht' a ha).1]
        exact Nat.beq_refl _
      · rw [allLt_iff]
        intro b hb
        obtain ⟨eb, pb⟩ := (hd t ht').2 b hb
        rw [ea, eb, comp_unpack' hw pa pb, comp_unpack' hw pb pa,
          eqA_unpack' hw (PGrp.permB_pcomp hw pa pb) (PGrp.permB_pcomp hw pb pa),
          (hDe t ht' a ha).2 b hb]
        exact Nat.beq_refl _
  · rw [allLt_iff, hh.1]
    intro k hk
    rw [(hh.2 k hk).1]
    exact BfsPin.validA_unpack (hh.2 k hk).2
  · rw [allLt_iff, hrE.1, Array.size_ofFn]
    intro k hk
    have hk1 : k < (Array.ofFn (n := R.N) fun i => unpack n w (R.T i.val)).size := by
      rw [Array.size_ofFn]
      exact hk
    have pk := (hrE.2.2 k hk).2
    rw [getElem!_pos _ k hk1, Array.getElem_ofFn, hzE]
    dsimp only
    unfold coverOK
    rw [comp_unpack' hw pk pk, comp_unpack' hw pk (PGrp.permB_pcomp hw pk pk), idA_eq hw,
      eqA_unpack' hw (PGrp.permB_pcomp hw pk (PGrp.permB_pcomp hw pk pk)) permId,
      eqA_unpack' hw pk permId, eqA_unpack' hw pk hZp, comp_unpack' hw hZp hZp,
      eqA_unpack' hw pk (PGrp.permB_pcomp hw hZp hZp)]
    simp only [Bool.or_eq_true]
    rcases hcov k hk with (h | h | h | h) | h
    · rw [beq_false h]
      exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
    · rw [h]
      exact Or.inl (Or.inl (Or.inl (Or.inr (Nat.beq_refl _))))
    · rw [h]
      exact Or.inl (Or.inl (Or.inr (Nat.beq_refl _)))
    · rw [h]
      exact Or.inl (Or.inr (Nat.beq_refl _))
    · obtain ⟨i, hi, t, ht, j, hj, j', hj', e1, e2⟩ := h
      right
      rw [List.any_eq_true]
      have hi' : i < (X.hW.map (posWord n X.pg)).size := by rw [hh.1]; exact hi
      refine ⟨(X.hW.map (posWord n X.pg))[i]!, by
        rw [getElem!_pos _ i hi']; exact Array.getElem_mem_toList hi', ?_⟩
      obtain ⟨eh, ph⟩ := hh.2 i hi
      rw [eh]
      try dsimp only
      rw [List.any_eq_true]
      refine ⟨_, Array.getElem_mem_toList (by rw [Array.size_map]; exact ht), ?_⟩
      rw [Array.getElem_map, ← getElem!_pos X.dW t ht]
      try dsimp only
      obtain ⟨hdp, -, hdg⟩ := pin_facts (D t) (fuel := X.dFuel) (hd t ht).1 (hd t ht).2 psD
        (hDN t ht).2
      rw [hdp, Bool.and_eq_true, List.any_eq_true, List.any_eq_true]
      exact ⟨⟨_, mem_ofFn _ hj, conj_eq hw ph pk (hdg j hj).2 e1⟩,
        ⟨_, mem_ofFn _ hj', conj_eq hw ph hZp (hdg j' hj').2 e2⟩⟩

end Glue

end CFSG.KC.E81K

end
