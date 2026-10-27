module

public import Certificates.Data.Kernel.Spor.ChainSK
public import CFSG.Certificates.Kernel.Spor.ChainKGen
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KS.CH.SKB

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.ONSchreier.Native

variable {n s : Nat} {S : Array (Array Nat)} {base : Array Nat} {F FI : Nat → Nat → Nat}
  {B LEN : Nat → Nat} {IDX : Nat → Nat → Nat}

theorem pisInv_of (hS : S.size = s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x) :
    ∀ j < S.size, pisInv n S[j]! (pinvs n S)[j]! = true := by
  intro j hj
  rw [hS] at hj
  unfold pisInv
  rw [allBelowN_iff']
  intro x hx
  rw [(hF j hj x hx).1, pinvs_get hS hF j hj _ (hF j hj x hx).2.1, (hF j hj x hx).2.2.2]
  simp [(hF j hj x hx).2.1]

theorem plettersOK_of {j : Nat} {w : List Int} (hl : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ j) :
    plettersOK j w = true := by
  unfold plettersOK
  rw [List.all_eq_true]
  intro l hl'
  obtain ⟨h1, h2⟩ := hl l hl'
  simp [h1, h2]

theorem peq_pword_of (hS : S.size = s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    {j : Nat} (hj : j < s) {w : List Int} (hl : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ j)
    (hf : ∀ x < n, F j x = w.foldr (CFSG.KS.TW.GZ F FI) x) :
    peq n S[j]! (pword n S (pinvs n S) w) = true := by
  have hL : CFSG.KS.PW.LettersOK n j S (pinvs n S) F FI := fun j' hj' x hx =>
    ⟨(hF j' (by omega) x hx).1, pinvs_get hS hF j' (by omega) x hx, (hF j' (by omega) x hx).2.1,
      (hF j' (by omega) x hx).2.2.1⟩
  unfold peq
  rw [allBelowN_iff']
  intro x hx
  rw [(hF j hj x hx).1, (CFSG.KS.PW.pword_get hL w hl x hx).1, ← hf x hx]
  exact beq_self_eq_true _

theorem pointChainOK_of_levels {m nb chunks : Nat} {W : Array (List Int)}
    (hS : S.size = s) (hWs : W.size = s) (hm : m ≤ s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hW : ∀ j, m ≤ j → j < s → (∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      ∀ x < n, F j x = W[j]!.foldr (CFSG.KS.TW.GZ F FI) x)
    (hb : base.size = nb) (hB : ∀ k < nb, base[k]! = B k ∧ B k < n)
    (hlev : ∀ i < nb, clevelOK n base[i]! (allSteps S (pinvs n S) base)[i]!
      (cLevels n base (allSteps S (pinvs n S) base))[i]! = true)
    (hsch : ∀ i < nb, cschreierOK (cLevels n base (allSteps S (pinvs n S) base))
      (allSteps S (pinvs n S) base) (allInvSteps S (pinvs n S) base) base
      (Array.ofFn (n := base.size) fun i => i.val) false i chunks = true) :
    pointChainOK n m S base W chunks = true := by
  have hbn : ∀ i < base.size, base[i]! < n := fun i hi => by
    rw [hb] at hi
    rw [(hB i hi).1]
    exact (hB i hi).2
  have bid : ∀ t < base.size, (Array.ofFn (n := base.size) fun i => i.val)[t]! = t :=
    fun t ht => getD_ofFn (f := fun i => i) ht
  unfold pointChainOK chainOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by omega, by rw [hWs, hS]⟩, allBelowN_iff'.2 (pisInv_of hS hF)⟩,
    allBelowN_iff'.2 fun j hj => ?_⟩, allBelowN_iff'.2 fun i hi => decide_eq_true (hbn i hi)⟩,
    Array.size_ofFn⟩, allBelowN_iff'.2 fun i hi => ?_⟩,
    allBelowN_iff'.2 fun i hi => decide_eq_true (hbn i hi)⟩, rfl⟩,
    allBelowN_iff'.2 fun i hi => hlev i (by omega)⟩, allBelowN_iff'.2 fun i hi => hsch i (by omega)⟩
  · rw [hS] at hj
    by_cases hjm : j < m
    · simp [hjm]
    · obtain ⟨hl, hf⟩ := hW j (by omega) hj
      rw [plettersOK_of hl, peq_pword_of hS hF hj hl hf]
      simp
  · rw [bid i hi]
    simp [hi]

theorem cOrbitSizes_eq {nb : Nat} {M : Nat → Nat} (hb : base.size = nb)
    (h : ∀ i < nb, (cLevels n base (allSteps S (pinvs n S) base))[i]!.pts.size = M i) :
    cOrbitSizes n S base = (List.range nb).map M := by
  have hcs : (cLevels n base (allSteps S (pinvs n S) base)).size = nb := by simp [cLevels, hb]
  unfold cOrbitSizes
  apply List.ext_getElem
  · simp [hcs]
  · intro i h1 h2
    have hi : i < nb := by simpa using h2
    simp only [List.getElem_map, Array.getElem_toList, List.getElem_range]
    rw [← getElem!_pos (cLevels n base (allSteps S (pinvs n S) base)) i (by rw [hcs]; exact hi),
      h i hi]

theorem steps3_get (hS : S.size = s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hb : base.size = 3) (hB : ∀ k < 3, base[k]! = B k ∧ B k < n) {i : Nat} (hi : i < 3)
    (hidx : idxOK F s B i (IDX i) (LEN i) = true) :
    (allSteps S (pinvs n S) base)[i]!.size = Nat.mul 2 (LEN i) ∧
      ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
        (((allSteps S (pinvs n S) base)[i]!)[j]!)[x]! = stepX F FI (IDX i) (LEN i) j x ∧
          stepX F FI (IDX i) (LEN i) j x < n := by
  obtain ⟨hl, hlt⟩ := levIdx_eq hS hF hB hi hidx
  unfold allSteps
  rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
  unfold levSteps
  rw [hl]
  refine ⟨by simp; omega, fun j hj x hx => ?_⟩
  simp only [Nat.mul_eq] at hj
  unfold stepX
  rw [nIf_v]
  by_cases hjl : j < LEN i
  · rw [if_pos (Nat.blt_eq.mpr hjl), getElem!_pos _ j (by simp; omega),
      Array.getElem_append_left (by simp; exact hjl)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
    exact ⟨(hF _ (hlt j hjl) x hx).1, (hF _ (hlt j hjl) x hx).2.1⟩
  · rw [if_neg (by simpa using hjl), getElem!_pos _ j (by simp; omega),
      Array.getElem_append_right (by simp; omega)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, List.size_toArray,
      List.length_map, List.length_range]
    have hjs : j - LEN i < LEN i := by omega
    exact ⟨pinvs_get hS hF _ (hlt _ hjs) x hx, (hF _ (hlt _ hjs) x hx).2.2.1⟩

theorem invSteps3_get (hS : S.size = s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hb : base.size = 3) (hB : ∀ k < 3, base[k]! = B k ∧ B k < n) {i : Nat} (hi : i < 3)
    (hidx : idxOK F s B i (IDX i) (LEN i) = true) :
    ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
      (((allInvSteps S (pinvs n S) base)[i]!)[j]!)[x]! = invX F FI (IDX i) (LEN i) j x ∧
        invX F FI (IDX i) (LEN i) j x < n := by
  intro j hj x hx
  simp only [Nat.mul_eq] at hj
  obtain ⟨hl, hlt⟩ := levIdx_eq hS hF hB hi hidx
  unfold allInvSteps
  rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
  unfold levInvSteps invX
  rw [hl, nIf_v]
  by_cases hjl : j < LEN i
  · rw [if_pos (Nat.blt_eq.mpr hjl), getElem!_pos _ j (by simp; omega),
      Array.getElem_append_left (by simp; exact hjl)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
    rw [pinvs_get hS hF _ (hlt j hjl) x hx]
    exact ⟨rfl, (hF _ (hlt j hjl) x hx).2.2.1⟩
  · rw [if_neg (by simpa using hjl), getElem!_pos _ j (by simp; omega),
      Array.getElem_append_right (by simp; omega)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, List.size_toArray,
      List.length_map, List.length_range]
    have hjs : j - LEN i < LEN i := by omega
    exact ⟨(hF _ (hlt _ hjs) x hx).1, (hF _ (hlt _ hjs) x hx).2.1⟩

theorem trK_lt_nz {m r : Nat} {PAR LAB : Nat → Nat} {STEP : Nat → Nat → Nat}
    (hm : ∀ k < m, k ≠ 0 → PAR k < m ∧ LAB k < r) (hs : ∀ j < r, ∀ x < n, STEP j x < n) :
    ∀ (fuel k p : Nat), k < m → p < n → trK STEP PAR LAB fuel k p < n
  | 0, _, _, _, hp => hp
  | fuel + 1, k, p, hk, hp => by
    cases k with
    | zero => exact hp
    | succ k =>
      have hk0 := hm _ hk (Nat.succ_ne_zero k)
      exact hs _ hk0.2 _ (trK_lt_nz hm hs fuel (PAR (k + 1)) p hk0.1 hp)

theorem trApp_eq_nz {m r : Nat} {PTS POS PAR LAB : Nat → Nat} {STEP : Nat → Nat → Nat}
    {st : Array (Array Nat)} (hm : ∀ k < m, k ≠ 0 → PAR k < m ∧ LAB k < r)
    (hs : ∀ j < r, ∀ x < n, (st[j]!)[x]! = STEP j x ∧ STEP j x < n) :
    ∀ (fuel k p : Nat), k < m → p < n →
      trApp st ⟨Array.ofFn (n := m) fun k => PTS k.val, Array.ofFn (n := n) fun z => POS z.val,
        Array.ofFn (n := m) fun k => PAR k.val, Array.ofFn (n := m) fun k => LAB k.val⟩ fuel k p =
      trK STEP PAR LAB fuel k p
  | 0, _, _, _, _ => rfl
  | fuel + 1, k, p, hk, hp => by
    unfold trApp
    cases k with
    | zero => rfl
    | succ k =>
      have hk0 := hm _ hk (Nat.succ_ne_zero k)
      simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
      have e1 : (Array.ofFn (n := m) fun k => PAR k.val)[k + 1]! = PAR (k + 1) := by
        rw [getElem!_pos _ (k + 1) (by simpa using hk), Array.getElem_ofFn]
      have e2 : (Array.ofFn (n := m) fun k => LAB k.val)[k + 1]! = LAB (k + 1) := by
        rw [getElem!_pos _ (k + 1) (by simpa using hk), Array.getElem_ofFn]
      rw [e1, e2, trApp_eq_nz hm hs fuel _ p hk0.1 hp,
        (hs _ hk0.2 _ (trK_lt_nz hm (fun j hj x hx => (hs j hj x hx).2) fuel _ p hk0.1 hp)).1]
      rfl

theorem schImg_lt {r : Nat} {STEP INV : Nat → Nat → Nat → Nat} {PAR LAB : Nat → Nat → Nat}
    {Mr : Nat → Nat} {i h j k p : Nat}
    (hm : ∀ k < Mr i, k ≠ 0 → PAR i k < Mr i ∧ LAB i k < r)
    (hs : ∀ j < r, ∀ x < n, STEP i j x < n) (hI : ∀ j < r, ∀ x < n, INV i j x < n)
    (hh : h < Mr i) (hj : j < r) (hk : k < Mr i) (hp : p < n) :
    schImg STEP INV PAR LAB Mr i h j k p < n :=
  trInvK_lt_nz hm hI _ _ _ hk (hs j hj _ (trK_lt_nz hm hs _ _ _ hh hp))

theorem schreierImgs_eq {nb r : Nat} {steps invs : Array (Array Nat)}
    {STEP INV : Nat → Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat → Nat} {Mr : Nat → Nat}
    {i h j k : Nat} (hb : base.size = nb) (hB : ∀ t < nb, base[t]! = B t ∧ B t < n)
    (hm : ∀ k < Mr i, k ≠ 0 → PAR i k < Mr i ∧ LAB i k < r)
    (hs : ∀ j < r, ∀ x < n, (steps[j]!)[x]! = STEP i j x ∧ STEP i j x < n)
    (hinv : ∀ j < r, ∀ x < n, (invs[j]!)[x]! = INV i j x ∧ INV i j x < n)
    (hh : h < Mr i) (hj : j < r) (hk : k < Mr i) :
    schreierImgs steps invs ⟨Array.ofFn (n := Mr i) fun k => PTS i k.val,
        Array.ofFn (n := n) fun z => POS i z.val, Array.ofFn (n := Mr i) fun k => PAR i k.val,
        Array.ofFn (n := Mr i) fun k => LAB i k.val⟩ base h j k =
      Array.ofFn (n := nb) fun t => schImg STEP INV PAR LAB Mr i h j k (B t.val) := by
  unfold schreierImgs
  apply Array.ext
  · simp [hb]
  · intro t h1 _
    have ht : t < nb := by simpa [hb] using h1
    have hBt : base[t] = B t := by
      rw [← getElem!_pos base t (by rw [hb]; exact ht)]
      exact (hB t ht).1
    have htk := trK_lt_nz hm (fun j hj x hx => (hs j hj x hx).2) (Mr i) h (B t) hh (hB t ht).2
    rw [Array.getElem_map, Array.getElem_ofFn]
    simp only [Array.size_ofFn]
    rw [hBt, trApp_eq_nz hm hs (Mr i) h (B t) hh (hB t ht).2, (hs j hj _ htk).1,
      trInvApp_eq_nz hm hinv (Mr i) k _ hk (hs j hj _ htk).2]
    rfl

theorem psift_ofFn_step {m r l nb : Nat} {LV : Array CLevel} {IV : Array (Array (Array Nat))}
    {pts bidx : Array Nat} {full : Bool} {PTS POS PAR LAB : Nat → Nat} {INV : Nat → Nat → Nat}
    {ψ : Nat → Nat} (hl : l < LV.size) (hln : l < nb) (hbid : bidx[l]! = l)
    (hlev : LV[l]! = ⟨Array.ofFn (n := m) fun k => PTS k.val,
      Array.ofFn (n := n) fun z => POS z.val, Array.ofFn (n := m) fun k => PAR k.val,
      Array.ofFn (n := m) fun k => LAB k.val⟩)
    (hm : ∀ k < m, k ≠ 0 → PAR k < m ∧ LAB k < r)
    (hinv : ∀ j < r, ∀ x < n, ((IV[l]!)[j]!)[x]! = INV j x ∧ INV j x < n)
    (hψ : ∀ t < nb, ψ t < n) :
    psift LV IV pts bidx full l (Array.ofFn (n := nb) fun t => ψ t.val) =
      (decide (POS (ψ l) < m) && psift LV IV pts bidx full (l + 1)
        (Array.ofFn (n := nb) fun t => trInvK PAR LAB INV m (POS (ψ l)) (ψ t.val))) := by
  rw [psift_step hl, hbid, getD_ofFn hln, hlev]
  simp only [getD_ofFn (hψ l hln), Array.size_ofFn]
  by_cases hk : POS (ψ l) < m
  · have e : (Array.ofFn (n := nb) fun t => ψ t.val).map (fun y => trInvApp IV[l]!
        ⟨Array.ofFn (n := m) fun k => PTS k.val, Array.ofFn (n := n) fun z => POS z.val,
          Array.ofFn (n := m) fun k => PAR k.val, Array.ofFn (n := m) fun k => LAB k.val⟩ m
          (POS (ψ l)) y) =
        Array.ofFn (n := nb) fun t => trInvK PAR LAB INV m (POS (ψ l)) (ψ t.val) := by
      rw [Array.map_ofFn]
      congr 1
      funext t
      exact trInvApp_eq_nz hm hinv m _ _ hk (hψ t t.isLt)
    rw [e]
  · simp [hk]

end CFSG.KS.CH.SKB

end
