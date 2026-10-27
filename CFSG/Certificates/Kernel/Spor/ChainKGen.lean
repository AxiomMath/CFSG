module

public import CFSG.Certificates.Kernel.Spor.ChainKProof
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KS.CH

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.ONSchreier.Native

theorem foldl_setK_congr {n : Nat} {t u : Array Nat} (h : ∀ i < n, t[i]! = u[i]!) :
    ∀ (l : List Nat) (p : Array Nat), (∀ i ∈ l, i < n) →
      l.foldl (fun p i => p.set! t[i]! i) p = l.foldl (fun p i => p.set! u[i]! i) p
  | [], _, _ => rfl
  | a :: l, p, hl => by
    simp only [List.foldl_cons]
    rw [h a (hl a (by simp))]
    exact foldl_setK_congr h l _ fun i hi => hl i (by simp [hi])

theorem pinvCand_eq_of_agree {n : Nat} {t u : Array Nat} (h : ∀ i < n, t[i]! = u[i]!) :
    pinvCand n t = pinvCand n u := by
  have key : ∀ v : Array Nat, pinvCand n v =
      (List.range' 0 n).foldl (fun p i => p.set! v[i]! i) (Array.replicate n 0) := fun v => by
    unfold pinvCand
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  rw [key, key]
  exact foldl_setK_congr h _ _ fun i hi => by simpa using (List.mem_range'_1.1 hi).2

theorem pinvs_get {n s : Nat} {S : Array (Array Nat)} {F FI : Nat → Nat → Nat}
    (hS : S.size = s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x) :
    ∀ j < s, ∀ x < n, ((pinvs n S)[j]!)[x]! = FI j x := by
  intro j hj x hx
  unfold pinvs
  rw [getElem!_pos _ j (by simp [hS]; exact hj), Array.getElem_map,
    ← getElem!_pos S j (by rw [hS]; exact hj),
    pinvCand_eq_of_agree (u := Array.ofFn (n := n) fun i => F j i.val) fun i hi => by
      rw [getD_ofFn (f := F j) hi]
      exact (hF j hj i hi).1]
  exact CFSG.KS.CB.pinvCand_get (T := F j) (U := FI j) (fun y hy => (hF j hj y hy).2.1)
    (fun y hy => (hF j hj y hy).2.2.2) hx

theorem trInvK_lt_nz {n m r : Nat} {PAR LAB : Nat → Nat} {INV : Nat → Nat → Nat}
    (hm : ∀ k < m, k ≠ 0 → PAR k < m ∧ LAB k < r) (hI : ∀ j < r, ∀ x < n, INV j x < n) :
    ∀ fuel k p, k < m → p < n → trInvK PAR LAB INV fuel k p < n
  | 0, _, _, _, hp => hp
  | f + 1, k, p, hk, hp => by
    change nIf(Nat.beq k 0, p, trInvK PAR LAB INV f (PAR k) (INV (LAB k) p)) < n
    rw [nIf_v]
    split
    · exact hp
    · rename_i h
      have hk0 : k ≠ 0 := fun e => h (by rw [e]; rfl)
      exact trInvK_lt_nz hm hI f _ _ (hm k hk hk0).1 (hI _ (hm k hk hk0).2 _ hp)

theorem trInvApp_eq_nz {n m r : Nat} {PTS POS PAR LAB : Nat → Nat} {INV : Nat → Nat → Nat}
    {invs : Array (Array Nat)} (hm : ∀ k < m, k ≠ 0 → PAR k < m ∧ LAB k < r)
    (hinv : ∀ j < r, ∀ x < n, invs[j]![x]! = INV j x ∧ INV j x < n) :
    ∀ (fuel k p : Nat), k < m → p < n →
      trInvApp invs ⟨Array.ofFn (n := m) fun k => PTS k.val, Array.ofFn (n := n) fun z => POS z.val,
        Array.ofFn (n := m) fun k => PAR k.val, Array.ofFn (n := m) fun k => LAB k.val⟩ fuel k p =
      trInvK PAR LAB INV fuel k p
  | 0, _, _, _, _ => rfl
  | fuel + 1, k, p, hk, hp => by
    unfold trInvApp
    by_cases h0 : k = 0
    · subst h0
      rfl
    · have hbk : (k == 0) = false := by simpa using h0
      simp only [hbk, Bool.false_eq_true, ↓reduceIte]
      have e1 : (Array.ofFn (n := m) fun k => PAR k.val)[k]! = PAR k := by
        rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
      have e2 : (Array.ofFn (n := m) fun k => LAB k.val)[k]! = LAB k := by
        rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
      have hmk := hm k hk h0
      rw [e1, e2, (hinv (LAB k) hmk.2 p hp).1,
        trInvApp_eq_nz hm hinv fuel (PAR k) (INV (LAB k) p) hmk.1 (hinv (LAB k) hmk.2 p hp).2]
      change _ = nIf(Nat.beq k (nat_lit 0), p, trInvK PAR LAB INV fuel (PAR k) (INV (LAB k) p))
      have hb0 : Nat.beq k (nat_lit 0) = false := by
        cases k with
        | zero => exact absurd rfl h0
        | succ k => rfl
      rw [hb0]

theorem memIn3_gen {n s : Nat} {S : Array (Array Nat)} {base g : Array Nat}
    {F FI : Nat → Nat → Nat} {B G LEN : Nat → Nat} {IDX : Nat → Nat → Nat} {Mr : Nat → Nat}
    {PTS POS PAR LAB : Nat → Nat → Nat}
    (hS : S.size = s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hb : base.size = 3) (hB : ∀ k < 3, base[k]! = B k ∧ B k < n) (hg : ∀ k < 3, g[B k]! = G k)
    (hG : ∀ k < 3, G k < n)
    (hidx : ∀ i < 3, idxOK F s B i (IDX i) (LEN i) = true)
    (hh : ∀ i < 3, cbHead n (Mr i) (B i) (PTS i) (PAR i) (LAB i) = true)
    (hp : ∀ i < 3, ∀ k < Mr i, cbPt n (Mr i) (Nat.mul 2 (LEN i)) (stepX F FI (IDX i) (LEN i))
      (PTS i) (POS i) (PAR i) (LAB i) k = true)
    (hz : ∀ i < 3, ∀ z < n, cbPos n (Mr i) (PTS i) (POS i) z = true)
    (hsift : sift3 POS PAR LAB Mr (fun i => invX F FI (IDX i) (LEN i)) (G 0) (G 1) (G 2) = true) :
    memPoint (cLevels n base (allSteps S (pinvs n S) base)) (allInvSteps S (pinvs n S) base) base g =
      true := by
  have hSi := pinvs_get hS hF
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
  have hm : ∀ i < 3, ∀ k < Mr i, k ≠ 0 → PAR i k < Mr i ∧ LAB i k < Nat.mul 2 (LEN i) := by
    intro i hi k hk hk0
    obtain ⟨a, b⟩ := cbPt_bounds (hp i hi k hk) hk0
    exact ⟨by omega, b⟩
  have htr : ∀ i < 2, ∀ k < Mr i, ∀ p < n, ∀ fuel,
      trInvApp (allInvSteps S (pinvs n S) base)[i]! (cLevels n base (allSteps S (pinvs n S) base))[i]!
        fuel k p = trInvK (PAR i) (LAB i) (invX F FI (IDX i) (LEN i)) fuel k p := by
    intro i hi k hk p hpn fuel
    rw [hlev i (by omega)]
    exact trInvApp_eq_nz (hm i (by omega)) (fun j hj x hx => hinv i (by omega) j hj x hx) fuel k p hk hpn
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
  have y1lt : y1 < n := hy1 ▸ trInvK_lt_nz (hm 0 (by norm_num)) (hIlt 0 (by norm_num)) _ _ _ k0lt (hG 1 (by norm_num))
  have y2lt : y2 < n := hy2 ▸ trInvK_lt_nz (hm 0 (by norm_num)) (hIlt 0 (by norm_num)) _ _ _ k0lt (hG 2 (by norm_num))
  generalize hy3 : trInvK (PAR 1) (LAB 1) (invX F FI (IDX 1) (LEN 1)) (Mr 1) (POS 1 y1) y2 = y3 at s2
  have y3lt : y3 < n := hy3 ▸ trInvK_lt_nz (hm 1 (by norm_num)) (hIlt 1 (by norm_num)) _ _ _ k1lt y2lt
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
