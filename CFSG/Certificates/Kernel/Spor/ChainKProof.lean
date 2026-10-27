module

public import Certificates.Data.Kernel.Spor.ChainK
public import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Perm.Subperm
public import CFSG.Certificates.Kernel.Spor.PWord
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.CH

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.ONSchreier.Native

theorem strictB_v (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bIf_v (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem nIf_v (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem allBelowN_iff' {n : Nat} {p : Nat → Bool} : allBelowN n p = true ↔ ∀ i < n, p i = true := by
  unfold allBelowN
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i i.2

theorem fixesK_iff {F : Nat → Nat → Nat} {B : Nat → Nat} {i j : Nat} :
    fixesK F B i j = true ↔ ∀ k < i, F j (B k) = B k := by
  unfold fixesK
  constructor
  · intro h k hk
    exact Nat.eq_of_beq_eq_true (allN_spec h k hk)
  · intro h
    exact PackFld.allN_of_forall fun k hk => by rw [h k hk]; exact Nat.beq_refl _

theorem cntB_eq (s : Nat) (q : Nat → Bool) : cntB s q = ((List.range s).filter q).length := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change Nat.add (nIf(q s, nat_lit 1, nat_lit 0)) (cntB s q) = _
    rw [ih, List.range_succ, List.filter_append, List.length_append, nIf_v]
    cases h : q s <;> simp [h, Nat.add_comm]

theorem filter_eq_of {s len : Nat} {q : Nat → Bool} {IDX : Nat → Nat}
    (hlt : ∀ t < len, IDX t < s) (hq : ∀ t < len, q (IDX t) = true)
    (hinc : ∀ t, t + 1 < len → IDX t < IDX (t + 1)) (hc : ((List.range s).filter q).length = len) :
    (List.range s).filter q = (List.range len).map IDX := by
  have hmono : ∀ a b, a < b → b < len → IDX a < IDX b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_or_ge a b with h | h
      · exact Nat.lt_trans (ih h (by omega)) (hinc b hb)
      · have e : a = b := by omega
        subst e
        exact hinc a hb
  have hs1 : ((List.range len).map IDX).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem fun ha hb hab =>
      hmono _ _ hab (List.mem_range.1 hb)
  have hs2 : ((List.range s).filter q).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have hsub : (List.range len).map IDX ⊆ (List.range s).filter q := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    have ht' := List.mem_range.1 ht
    exact List.mem_filter.2 ⟨List.mem_range.2 (hlt t ht'), hq t ht'⟩
  have hp : ((List.range len).map IDX).Perm ((List.range s).filter q) :=
    List.Subperm.perm_of_length_le (List.Nodup.subperm (hs1.imp Nat.ne_of_lt) hsub) (by simp [hc])
  exact hp.symm.eq_of_pairwise' (r := (· ≤ ·)) (hs2.imp le_of_lt) (hs1.imp le_of_lt)

section

variable {n s : Nat} {S : Array (Array Nat)} {base : Array Nat} {F FI : Nat → Nat → Nat}
  {B : Nat → Nat} {IDX : Nat → Nat → Nat} {LEN : Nat → Nat}

theorem levIdx_eq (hS : S.size = s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hB : ∀ k < 3, base[k]! = B k ∧ B k < n) {i : Nat} (hi : i < 3)
    (hidx : idxOK F s B i (IDX i) (LEN i) = true) :
    levIdx S base i = (List.range (LEN i)).map (IDX i) ∧ ∀ t < LEN i, IDX i t < s := by
  unfold idxOK at hidx
  rw [bAnd_iff] at hidx
  obtain ⟨h1, h2⟩ := hidx
  have ht := fun t (htl : t < LEN i) => allN_spec h1 t htl
  have hq : ∀ j < s, pfixes base S[j]! i = fixesK F B i j := by
    intro j hj
    rw [Bool.eq_iff_iff, fixesK_iff]
    unfold pfixes
    rw [allBelowN_iff']
    constructor
    · intro h k hk
      have := h k hk
      rw [beq_iff_eq, (hB k (by omega)).1, (hF j hj _ (hB k (by omega)).2).1] at this
      exact this
    · intro h k hk
      rw [beq_iff_eq, (hB k (by omega)).1, (hF j hj _ (hB k (by omega)).2).1]
      exact h k hk
  have hlt : ∀ t < LEN i, IDX i t < s := fun t htl => by
    have := ht t htl
    simp only [bAnd_iff] at this
    exact Nat.blt_eq.mp this.1
  refine ⟨?_, hlt⟩
  unfold levIdx
  rw [hS]
  have hf : (List.range s).filter (fun j => pfixes base S[j]! i) =
      (List.range s).filter (fixesK F B i) :=
    List.filter_congr fun j hj => hq j (List.mem_range.1 hj)
  rw [hf]
  refine filter_eq_of hlt (fun t htl => ?_) (fun t htl => ?_) ?_
  · have := ht t (by omega)
    simp only [bAnd_iff] at this
    exact this.2.1
  · have := ht t (by omega)
    simp only [bAnd_iff] at this
    rw [bIf_v, ite_eq_left (Nat.blt_eq.mpr htl)] at this
    exact Nat.blt_eq.mp this.2.2
  · rw [← cntB_eq]
    exact Nat.eq_of_beq_eq_true h2

end

theorem cbPt_bounds {n m r k : Nat} {STEP : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    (h : cbPt n m r STEP PTS POS PAR LAB k = true) (hk : k ≠ 0) : PAR k < k ∧ LAB k < r := by
  unfold cbPt at h
  simp only [strictB_v, bAnd_iff] at h
  obtain ⟨-, -, h3, -⟩ := h
  have hb : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun e => hk (Nat.eq_of_beq_eq_true e)
  rw [hb] at h3
  dsimp only at h3
  simp only [bAnd_iff] at h3
  exact ⟨Nat.blt_eq.mp h3.1, Nat.blt_eq.mp h3.2.1⟩

theorem cbHead_facts {n m root : Nat} {PTS PAR LAB : Nat → Nat}
    (h : cbHead n m root PTS PAR LAB = true) : 0 < m ∧ m ≤ n ∧ PAR 0 = 0 ∧ LAB 0 = 0 := by
  unfold cbHead at h
  simp only [bAnd_iff, Nat.beq_eq] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.le_of_ble_eq_true h.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem trInvK_lt {n m r : Nat} {PAR LAB : Nat → Nat} {INV : Nat → Nat → Nat}
    (hm : ∀ k < m, PAR k < m ∧ LAB k < r) (hI : ∀ j < r, ∀ x < n, INV j x < n) :
    ∀ fuel k p, k < m → p < n → trInvK PAR LAB INV fuel k p < n
  | 0, _, _, _, hp => hp
  | f + 1, k, p, hk, hp => by
    change nIf(Nat.beq k 0, p, trInvK PAR LAB INV f (PAR k) (INV (LAB k) p)) < n
    rw [nIf_v]
    split
    · exact hp
    · exact trInvK_lt hm hI f _ _ (hm k hk).1 (hI _ (hm k hk).2 _ hp)

theorem psift_step {levels : Array CLevel} {invs : Array (Array (Array Nat))} {pts bidx : Array Nat}
    {full : Bool} {l : Nat} {img : Array Nat} (hl : l < levels.size) :
    psift levels invs pts bidx full l img =
      (decide (levels[l]!.pos[img[bidx[l]!]!]! < levels[l]!.pts.size) &&
        psift levels invs pts bidx full (l + 1) (img.map fun y =>
          trInvApp invs[l]! levels[l]! levels[l]!.pts.size levels[l]!.pos[img[bidx[l]!]!]! y)) := by
  rw [psift, dite_eq_left hl, ← getElem!_pos levels l hl]

theorem psift_end {levels : Array CLevel} {invs : Array (Array (Array Nat))} {pts bidx : Array Nat}
    {l : Nat} {img : Array Nat} (hl : ¬ l < levels.size) :
    psift levels invs pts bidx false l img = true := by
  rw [psift, dite_eq_right hl]
  rfl

theorem getD_ofFn {m : Nat} {f : Nat → Nat} {x : Nat} (hx : x < m) :
    (Array.ofFn (n := m) fun i => f i.val)[x]! = f x := by
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem memIn3_proved {n s : Nat} {S : Array (Array Nat)} {base g : Array Nat}
    {F FI : Nat → Nat → Nat} {B G LEN : Nat → Nat} {IDX : Nat → Nat → Nat} {Mr : Nat → Nat}
    {PTS POS PAR LAB : Nat → Nat → Nat}
    (hS : S.size = s) (hSz : ∀ j < s, S[j]!.size = n)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hb : base.size = 3) (hB : ∀ k < 3, base[k]! = B k ∧ B k < n) (hg : ∀ k < 3, g[B k]! = G k)
    (hG : ∀ k < 3, G k < n) (hlen : 0 < LEN 0 ∧ 0 < LEN 1)
    (hidx : ∀ i < 3, idxOK F s B i (IDX i) (LEN i) = true)
    (hh : ∀ i < 3, cbHead n (Mr i) (B i) (PTS i) (PAR i) (LAB i) = true)
    (hp : ∀ i < 3, ∀ k < Mr i, cbPt n (Mr i) (Nat.mul 2 (LEN i)) (stepX F FI (IDX i) (LEN i))
      (PTS i) (POS i) (PAR i) (LAB i) k = true)
    (hz : ∀ i < 3, ∀ z < n, cbPos n (Mr i) (PTS i) (POS i) z = true)
    (hsift : sift3 POS PAR LAB Mr (fun i => invX F FI (IDX i) (LEN i)) (G 0) (G 1) (G 2) = true) :
    memPoint (cLevels n base (allSteps S (pinvs n S) base)) (allInvSteps S (pinvs n S) base) base g =
      true := by
  have hSe : ∀ j < s, S[j]! = Array.ofFn (n := n) fun x => F j x.val :=
    fun j hj => CFSG.KS.PW.arr_ext (hSz j hj) fun x hx => (hF j hj x hx).1
  have hSi : ∀ j < s, ∀ x < n, ((pinvs n S)[j]!)[x]! = FI j x := by
    intro j hj x hx
    unfold pinvs
    rw [getElem!_pos _ j (by simp [hS]; exact hj), Array.getElem_map,
      ← getElem!_pos S j (by rw [hS]; exact hj), hSe j hj]
    have hsurj : ∀ y < n, ∃ x < n, F j x = y := by
      intro y hy
      obtain ⟨x, hx, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n)
        (t := Finset.range n) (fun x _ => F j x)
        (fun x hx => Finset.mem_range.2 (hF j hj x (Finset.mem_range.1 hx)).2.1)
        (fun a b ha hb hab => by
          rw [← (hF j hj a (Finset.mem_range.1 ha)).2.2.2, ← (hF j hj b (Finset.mem_range.1 hb)).2.2.2,
            hab])
        le_rfl y (Finset.mem_range.2 hy)
      exact ⟨x, Finset.mem_range.1 hx, e.symm⟩
    obtain ⟨x0, hx0, e0⟩ := hsurj x hx
    rw [← e0]
    rw [CFSG.KS.CB.pinvCand_get (fun y hy => (hF j hj y hy).2.1) (fun y hy => (hF j hj y hy).2.2.2)
      (by rw [e0]; exact hx), (hF j hj x0 hx0).2.2.2]
  have hst : ∀ i < 3, (allSteps S (pinvs n S) base)[i]!.size = Nat.mul 2 (LEN i) ∧
      ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
        (((allSteps S (pinvs n S) base)[i]!)[j]!)[x]! = stepX F FI (IDX i) (LEN i) j x := by
    intro i hi
    obtain ⟨hl, hlt⟩ := levIdx_eq hS hF hB hi (hidx i hi)
    unfold allSteps
    rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
    unfold levSteps
    rw [hl]
    refine ⟨by simp; omega, fun j hj x hx => ?_⟩
    simp only [Nat.mul_eq] at hj
    unfold stepX
    rw [nIf_v]
    by_cases hjl : j < LEN i
    · rw [ite_eq_left (Nat.blt_eq.mpr hjl), getElem!_pos _ j (by simp; omega),
        Array.getElem_append_left (by simp; exact hjl)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      exact (hF _ (hlt j hjl) x hx).1
    · rw [ite_eq_right (by simpa using hjl), getElem!_pos _ j (by simp; omega),
        Array.getElem_append_right (by simp; omega)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, List.size_toArray,
        List.length_map, List.length_range]
      exact hSi _ (hlt _ (by omega)) x hx
  have hinv : ∀ i < 3, ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
      (((allInvSteps S (pinvs n S) base)[i]!)[j]!)[x]! = invX F FI (IDX i) (LEN i) j x ∧
        invX F FI (IDX i) (LEN i) j x < n := by
    intro i hi j hj x hx
    simp only [Nat.mul_eq] at hj
    obtain ⟨hl, hlt⟩ := levIdx_eq hS hF hB hi (hidx i hi)
    unfold allInvSteps
    rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
    unfold levInvSteps invX
    rw [hl, nIf_v]
    by_cases hjl : j < LEN i
    · rw [ite_eq_left (Nat.blt_eq.mpr hjl), getElem!_pos _ j (by simp; omega),
        Array.getElem_append_left (by simp; exact hjl)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      rw [hSi _ (hlt j hjl) x hx]
      exact ⟨rfl, (hF _ (hlt j hjl) x hx).2.2.1⟩
    · rw [ite_eq_right (by simpa using hjl), getElem!_pos _ j (by simp; omega),
        Array.getElem_append_right (by simp; omega)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, List.size_toArray,
        List.length_map, List.length_range]
      have hjs : j - LEN i < LEN i := by omega
      exact ⟨(hF _ (hlt _ hjs) x hx).1, (hF _ (hlt _ hjs) x hx).2.1⟩
  have hlev : ∀ i < 3, (cLevels n base (allSteps S (pinvs n S) base))[i]! =
      ⟨Array.ofFn (n := Mr i) fun k => PTS i k.val, Array.ofFn (n := n) fun z => POS i z.val,
        Array.ofFn (n := Mr i) fun k => PAR i k.val, Array.ofFn (n := Mr i) fun k => LAB i k.val⟩ := by
    intro i hi
    unfold cLevels
    rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
    change cbfs n base[i]! (allSteps S (pinvs n S) base)[i]! = _
    rw [(hB i hi).1]
    exact cbfsK_sound (hst i hi) (hh i hi) (hp i hi) (hz i hi)
  have hcs : (cLevels n base (allSteps S (pinvs n S) base)).size = 3 := by simp [cLevels, hb]
  have hm : ∀ i < 2, ∀ k < Mr i, PAR i k < Mr i ∧ LAB i k < Nat.mul 2 (LEN i) := by
    intro i hi k hk
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨h1, -, h3, h4⟩ := cbHead_facts (hh i (by omega))
      rw [h3, h4]
      refine ⟨h1, ?_⟩
      have : 0 < LEN i := by interval_cases i <;> simp [hlen]
      simp only [Nat.mul_eq]
      omega
    · obtain ⟨a, b⟩ := cbPt_bounds (hp i (by omega) k hk) hk0
      exact ⟨by omega, b⟩
  have htr : ∀ i < 2, ∀ k < Mr i, ∀ p < n, ∀ fuel,
      trInvApp (allInvSteps S (pinvs n S) base)[i]! (cLevels n base (allSteps S (pinvs n S) base))[i]!
        fuel k p = trInvK (PAR i) (LAB i) (invX F FI (IDX i) (LEN i)) fuel k p := by
    intro i hi k hk p hpn fuel
    rw [hlev i (by omega)]
    exact trInvApp_eq (hm i hi) (fun j hj x hx => hinv i (by omega) j hj x hx) fuel k p hk hpn
  have hIlt : ∀ i < 3, ∀ j < Nat.mul 2 (LEN i), ∀ x < n, invX F FI (IDX i) (LEN i) j x < n :=
    fun i hi j hj x hx => (hinv i hi j hj x hx).2
  unfold sift3 at hsift
  simp only [strictB_v, bAnd_iff] at hsift
  obtain ⟨s0, s1, s2⟩ := hsift
  have k0lt : POS 0 (G 0) < Mr 0 := Nat.blt_eq.mp s0
  generalize hy1 : trInvK (PAR 0) (LAB 0) (invX F FI (IDX 0) (LEN 0)) (Mr 0) (POS 0 (G 0)) (G 1) = y1
    at s1 s2
  generalize hy2 : trInvK (PAR 0) (LAB 0) (invX F FI (IDX 0) (LEN 0)) (Mr 0) (POS 0 (G 0)) (G 2) = y2
    at s1 s2
  have k1lt : POS 1 y1 < Mr 1 := Nat.blt_eq.mp s1
  have y1lt : y1 < n := hy1 ▸ trInvK_lt (hm 0 (by norm_num)) (hIlt 0 (by norm_num)) _ _ _ k0lt (hG 1 (by norm_num))
  have y2lt : y2 < n := hy2 ▸ trInvK_lt (hm 0 (by norm_num)) (hIlt 0 (by norm_num)) _ _ _ k0lt (hG 2 (by norm_num))
  generalize hy3 : trInvK (PAR 1) (LAB 1) (invX F FI (IDX 1) (LEN 1)) (Mr 1) (POS 1 y1) y2 = y3 at s2
  have y3lt : y3 < n := hy3 ▸ trInvK_lt (hm 1 (by norm_num)) (hIlt 1 (by norm_num)) _ _ _ k1lt y2lt
  have k2lt : POS 2 y3 < Mr 2 := Nat.blt_eq.mp s2
  have L0 := hlev 0 (by norm_num)
  have L1 := hlev 1 (by norm_num)
  have L2 := hlev 2 (by norm_num)
  have bid : ∀ t < 3, (Array.ofFn (n := base.size) fun i => i.val)[t]! = t := fun t ht =>
    getD_ofFn (f := fun i => i) (by rw [hb]; exact ht)
  have img0 : ∀ t < 3, (base.map fun b => g[b]!)[t]! = G t := fun t ht => by
    rw [getElem!_pos _ t (by simp [hb]; exact ht), Array.getElem_map,
      ← getElem!_pos base t (by rw [hb]; exact ht), (hB t ht).1, hg t ht]
  unfold memPoint
  rw [psift_step (by rw [hcs]; norm_num), L0, bid 0 (by norm_num), img0 0 (by norm_num)]
  simp only [getD_ofFn (hG 0 (by norm_num)), Array.size_ofFn, decide_eq_true k0lt, Bool.true_and]
  generalize himg1 : (Array.map (fun y => trInvApp (allInvSteps S (pinvs n S) base)[0]!
    { pts := Array.ofFn fun k => PTS 0 ↑k, pos := Array.ofFn fun z => POS 0 ↑z,
      par := Array.ofFn fun k => PAR 0 ↑k, lab := Array.ofFn fun k => LAB 0 ↑k } (Mr 0) (POS 0 (G 0)) y)
    (base.map fun b => g[b]!)) = img1
  have img1v : ∀ t < 3, img1[t]! = trInvK (PAR 0) (LAB 0) (invX F FI (IDX 0) (LEN 0)) (Mr 0)
      (POS 0 (G 0)) (G t) := fun t ht => by
    rw [← himg1, getElem!_pos _ t (by simp [hb]; exact ht), Array.getElem_map,
      ← getElem!_pos _ t (by simp [hb]; exact ht), img0 t ht, ← L0]
    exact htr 0 (by norm_num) _ k0lt _ (hG t ht) _
  rw [psift_step (by rw [hcs]; norm_num), L1, bid 1 (by norm_num), img1v 1 (by norm_num), hy1]
  simp only [getD_ofFn y1lt, Array.size_ofFn, decide_eq_true k1lt, Bool.true_and]
  generalize himg2 : (Array.map (fun y => trInvApp (allInvSteps S (pinvs n S) base)[1]!
    { pts := Array.ofFn fun k => PTS 1 ↑k, pos := Array.ofFn fun z => POS 1 ↑z,
      par := Array.ofFn fun k => PAR 1 ↑k, lab := Array.ofFn fun k => LAB 1 ↑k } (Mr 1) (POS 1 y1) y)
    img1) = img2
  have img2v : img2[2]! = y3 := by
    have h1s : img1.size = 3 := by rw [← himg1]; simp [hb]
    rw [← himg2, getElem!_pos _ 2 (by simp [h1s]), Array.getElem_map,
      ← getElem!_pos img1 2 (by rw [h1s]; norm_num), img1v 2 (by norm_num), hy2, ← L1, ← hy3]
    exact htr 1 (by norm_num) _ k1lt _ y2lt _
  rw [psift_step (by rw [hcs]; norm_num), L2, bid 2 (by norm_num), img2v]
  simp only [getD_ofFn y3lt, Array.size_ofFn, decide_eq_true k2lt, Bool.true_and]
  exact psift_end (by rw [hcs]; norm_num)

end CFSG.KS.CH

end
