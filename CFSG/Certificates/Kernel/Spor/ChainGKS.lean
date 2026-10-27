module

public import Certificates.Data.Kernel.Spor.ChainGK
public import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Spor.ChainKGen
import CFSG.Certificates.Kernel.Spor.ChainFKProof
import CFSG.Certificates.Kernel.Spor.CbfsFacts

public section

namespace CFSG.KS.CH.GKS

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.KS.PC CFSG.KS.CH CFSG.ONSchreier.Native

private theorem mapK_eqG (f : Nat → Nat) (q : List Nat) : mapK f q = q.map f := by
  induction q with
  | nil => rfl
  | cons x q ih =>
    change f x :: mapK f q = _
    rw [ih]
    rfl

private theorem listEqK_eqG : ∀ (a b : List Nat), listEqK a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | x :: a, y :: b, h => by
    change Bool.rec (motive := fun _ => Bool) false (listEqK a b) (Nat.beq x y) = true at h
    rw [bAnd_iff] at h
    rw [Nat.eq_of_beq_eq_true h.1, listEqK_eqG a b h.2]

private theorem map_selfG {l : List Nat} {f : Nat → Nat} (h : l.map f = l) :
    ∀ x ∈ l, f x = x := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.map_cons, List.cons.injEq] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx

private theorem parBelow_ofG {m chunks : Nat} {p : Nat → Bool} (h : ∀ i < m, p i = true) :
    parBelow m chunks p = true := by
  unfold parBelow
  rw [List.all_eq_true]
  intro t ht
  simp only [List.mem_map, List.mem_range] at ht
  obtain ⟨c, -, rfl⟩ := ht
  change allBelowN (m / chunks + 1)
    (fun k => !(decide (c * (m / chunks + 1) + k < m)) || p (c * (m / chunks + 1) + k)) = true
  rw [allBelowN_iff']
  intro k _
  by_cases hk : c * (m / chunks + 1) + k < m
  · simp [hk, h _ hk]
  · simp [hk]

private theorem siftG_zeroG (n : Nat) (POS PAR LAB : Nat → Nat → Nat) (Mr B : Nat → Nat)
    (INV : Nat → Nat → Nat → Nat) (i : Nat) (img : List Nat) :
    siftG n POS PAR LAB Mr B INV 0 i img = listEqK img (List.range n) := rfl

private theorem siftG_succG (n : Nat) (POS PAR LAB : Nat → Nat → Nat) (Mr B : Nat → Nat)
    (INV : Nat → Nat → Nat → Nat) (f i : Nat) (img : List Nat) :
    siftG n POS PAR LAB Mr B INV (f + 1) i img =
      Bool.rec (motive := fun _ => Bool) false
        (siftG n POS PAR LAB Mr B INV f (i + 1)
          (mapK (trInvK (PAR i) (LAB i) (INV i) (Mr i) (POS i (List.getD img (B i) 0))) img))
        (Nat.blt (POS i (List.getD img (B i) 0)) (Mr i)) :=
  strictB_v (POS i (List.getD img (B i) 0)) fun k => Bool.rec (motive := fun _ => Bool) false
    (siftG n POS PAR LAB Mr B INV f (i + 1) (mapK (trInvK (PAR i) (LAB i) (INV i) (Mr i) k) img))
    (Nat.blt k (Mr i))

private theorem schG_eqG {n nb : Nat} {F FI : Nat → Nat → Nat} {IDX : Nat → Nat → Nat}
    {LEN : Nat → Nat} {PTS POS PAR LAB : Nat → Nat → Nat} {Mr B : Nat → Nat} {i h j : Nat} :
    schG n nb (fun i => stepX F FI (IDX i) (LEN i)) (fun i => invX F FI (IDX i) (LEN i)) PTS POS
        PAR LAB Mr B i h j =
      Bool.rec (motive := fun _ => Bool) false
        (siftG n POS PAR LAB Mr B (fun i => invX F FI (IDX i) (LEN i)) (nb - (i + 1)) (i + 1)
          ((List.range n).map (schImg (fun i => stepX F FI (IDX i) (LEN i))
            (fun i => invX F FI (IDX i) (LEN i)) PAR LAB Mr i h j
            (POS i (stepX F FI (IDX i) (LEN i) j (PTS i h))))))
        (Nat.blt (POS i (stepX F FI (IDX i) (LEN i) j (PTS i h))) (Mr i)) := by
  unfold schG
  exact strictB_v _ _

private theorem cbPt_ptG {n m r k : Nat} {STEP : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    (h : cbPt n m r STEP PTS POS PAR LAB k = true) : PTS k < n ∧ POS (PTS k) = k := by
  unfold cbPt at h
  simp only [strictB_v, bAnd_iff] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2.1⟩

private theorem trK_lt_nzG {n m r : Nat} {PAR LAB : Nat → Nat} {STEP : Nat → Nat → Nat}
    (hm : ∀ k < m, k ≠ 0 → PAR k < m ∧ LAB k < r) (hs : ∀ j < r, ∀ x < n, STEP j x < n) :
    ∀ (fuel k p : Nat), k < m → p < n → trK STEP PAR LAB fuel k p < n
  | 0, _, _, _, hp => hp
  | fuel + 1, k, p, hk, hp => by
    cases k with
    | zero => exact hp
    | succ k =>
      have hk0 := hm _ hk (Nat.succ_ne_zero k)
      exact hs _ hk0.2 _ (trK_lt_nzG hm hs fuel (PAR (k + 1)) p hk0.1 hp)

private theorem trApp_eqG {n m r : Nat} {PTS POS PAR LAB : Nat → Nat} {STEP : Nat → Nat → Nat}
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
      rw [e1, e2, trApp_eqG hm hs fuel _ p hk0.1 hp,
        (hs _ hk0.2 _ (trK_lt_nzG hm (fun j hj x hx => (hs j hj x hx).2) fuel _ p hk0.1 hp)).1]
      rfl

private theorem pfixes_eqG {n s nb : Nat} {S : Array (Array Nat)} {base : Array Nat}
    {F FI : Nat → Nat → Nat} {B : Nat → Nat}
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hB : ∀ k < nb, base[k]! = B k ∧ B k < n) {i : Nat} (hi : i ≤ nb) {j : Nat} (hj : j < s) :
    pfixes base S[j]! i = fixesK F B i j := by
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

private theorem levIdx_eqG {n s nb : Nat} {S : Array (Array Nat)} {base : Array Nat}
    {F FI : Nat → Nat → Nat} {B : Nat → Nat} {IDX : Nat → Nat → Nat} {LEN : Nat → Nat}
    (hS : S.size = s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hB : ∀ k < nb, base[k]! = B k ∧ B k < n) {i : Nat} (hi : i < nb)
    (hidx : idxOK F s B i (IDX i) (LEN i) = true) :
    levIdx S base i = (List.range (LEN i)).map (IDX i) ∧ ∀ t < LEN i, IDX i t < s := by
  unfold idxOK at hidx
  rw [bAnd_iff] at hidx
  obtain ⟨h1, h2⟩ := hidx
  have ht := fun t (htl : t < LEN i) => allN_spec h1 t htl
  have hlt : ∀ t < LEN i, IDX i t < s := fun t htl => by
    have := ht t htl
    simp only [bAnd_iff] at this
    exact Nat.blt_eq.mp this.1
  refine ⟨?_, hlt⟩
  unfold levIdx
  rw [hS]
  have hf : (List.range s).filter (fun j => pfixes base S[j]! i) =
      (List.range s).filter (fixesK F B i) :=
    List.filter_congr fun j hj => pfixes_eqG hF hB hi.le (List.mem_range.1 hj)
  rw [hf]
  refine filter_eq_of hlt (fun t htl => ?_) (fun t htl => ?_) ?_
  · have := ht t (by omega)
    simp only [bAnd_iff] at this
    exact this.2.1
  · have := ht t (by omega)
    simp only [bAnd_iff] at this
    rw [bIf_v, if_pos (Nat.blt_eq.mpr htl)] at this
    exact Nat.blt_eq.mp this.2.2
  · rw [← cntB_eq]
    exact Nat.eq_of_beq_eq_true h2

theorem fullChainG_of_checks {n m s nb chunks : Nat} {S : Array (Array Nat)} {base : Array Nat}
    {W : Array (List Int)} {F FI : Nat → Nat → Nat} {B LEN : Nat → Nat} {IDX : Nat → Nat → Nat}
    {Mr : Nat → Nat} {PTS POS PAR LAB : Nat → Nat → Nat}
    (hS : S.size = s) (hWs : W.size = s) (hm : m ≤ s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hW : ∀ j, m ≤ j → j < s → (∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      ∀ x < n, F j x = W[j]!.foldr (CFSG.KS.TW.GZ F FI) x)
    (hb : base.size = nb) (hB : ∀ k < nb, base[k]! = B k ∧ B k < n)
    (hidx : ∀ i < nb, idxOK F s B i (IDX i) (LEN i) = true)
    (hh : ∀ i < nb, cbHead n (Mr i) (B i) (PTS i) (PAR i) (LAB i) = true)
    (hp : ∀ i < nb, ∀ k < Mr i, cbPt n (Mr i) (Nat.mul 2 (LEN i)) (stepX F FI (IDX i) (LEN i))
      (PTS i) (POS i) (PAR i) (LAB i) k = true)
    (hz : ∀ i < nb, ∀ z < n, cbPos n (Mr i) (PTS i) (POS i) z = true)
    (hsch : ∀ i < nb, ∀ h < Mr i, ∀ j < Nat.mul 2 (LEN i),
      schG n nb (fun i => stepX F FI (IDX i) (LEN i)) (fun i => invX F FI (IDX i) (LEN i)) PTS POS
        PAR LAB Mr B i h j = true)
    (hterm : termG n s nb F B = true) :
    fullChainOK n m S base W chunks = true ∧ cOrbitSizes n S base = (List.range nb).map Mr := by
  have hSi := pinvs_get hS hF
  have hSlt : ∀ i < nb, ∀ j < Nat.mul 2 (LEN i), ∀ x < n, stepX F FI (IDX i) (LEN i) j x < n := by
    intro i hi j hj x hx
    obtain ⟨-, hlt⟩ := levIdx_eqG hS hF hB hi (hidx i hi)
    simp only [Nat.mul_eq] at hj
    unfold stepX
    rw [nIf_v]
    by_cases hjl : j < LEN i
    · rw [if_pos (Nat.blt_eq.mpr hjl)]
      exact (hF _ (hlt j hjl) x hx).2.1
    · rw [if_neg (by simpa using hjl)]
      have hjs : j - LEN i < LEN i := by omega
      exact (hF _ (hlt _ hjs) x hx).2.2.1
  have hst : ∀ i < nb, (allSteps S (pinvs n S) base)[i]!.size = Nat.mul 2 (LEN i) ∧
      ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
        (((allSteps S (pinvs n S) base)[i]!)[j]!)[x]! = stepX F FI (IDX i) (LEN i) j x := by
    intro i hi
    obtain ⟨hl, hlt⟩ := levIdx_eqG hS hF hB hi (hidx i hi)
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
      exact (hF _ (hlt j hjl) x hx).1
    · rw [if_neg (by simpa using hjl), getElem!_pos _ j (by simp; omega),
        Array.getElem_append_right (by simp; omega)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, List.size_toArray,
        List.length_map, List.length_range]
      exact hSi _ (hlt _ (by omega)) x hx
  have hinv : ∀ i < nb, ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
      (((allInvSteps S (pinvs n S) base)[i]!)[j]!)[x]! = invX F FI (IDX i) (LEN i) j x ∧
        invX F FI (IDX i) (LEN i) j x < n := by
    intro i hi j hj x hx
    simp only [Nat.mul_eq] at hj
    obtain ⟨hl, hlt⟩ := levIdx_eqG hS hF hB hi (hidx i hi)
    unfold allInvSteps
    rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
    unfold levInvSteps invX
    rw [hl, nIf_v]
    by_cases hjl : j < LEN i
    · rw [if_pos (Nat.blt_eq.mpr hjl), getElem!_pos _ j (by simp; omega),
        Array.getElem_append_left (by simp; exact hjl)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      rw [hSi _ (hlt j hjl) x hx]
      exact ⟨rfl, (hF _ (hlt j hjl) x hx).2.2.1⟩
    · rw [if_neg (by simpa using hjl), getElem!_pos _ j (by simp; omega),
        Array.getElem_append_right (by simp; omega)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, List.size_toArray,
        List.length_map, List.length_range]
      have hjs : j - LEN i < LEN i := by omega
      exact ⟨(hF _ (hlt _ hjs) x hx).1, (hF _ (hlt _ hjs) x hx).2.1⟩
  have hIlt : ∀ i < nb, ∀ j < Nat.mul 2 (LEN i), ∀ x < n, invX F FI (IDX i) (LEN i) j x < n :=
    fun i hi j hj x hx => (hinv i hi j hj x hx).2
  have hlev : ∀ i < nb, (cLevels n base (allSteps S (pinvs n S) base))[i]! =
      ⟨Array.ofFn (n := Mr i) fun k => PTS i k.val, Array.ofFn (n := n) fun z => POS i z.val,
        Array.ofFn (n := Mr i) fun k => PAR i k.val,
        Array.ofFn (n := Mr i) fun k => LAB i k.val⟩ := by
    intro i hi
    unfold cLevels
    rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
    change cbfs n base[i]! (allSteps S (pinvs n S) base)[i]! = _
    rw [(hB i hi).1]
    exact cbfsK_sound (hst i hi) (hh i hi) (hp i hi) (hz i hi)
  have hcl : ∀ i < nb, clevelOK n base[i]! (allSteps S (pinvs n S) base)[i]!
      (cLevels n base (allSteps S (pinvs n S) base))[i]! = true := by
    intro i hi
    have e : (cLevels n base (allSteps S (pinvs n S) base))[i]! =
        cbfs n base[i]! (allSteps S (pinvs n S) base)[i]! := by
      unfold cLevels
      rw [getElem!_pos _ i (by simp [hb]; exact hi), Array.getElem_ofFn]
    rw [e]
    refine CFSG.KS.CBF.clevelOK_cbfs (by rw [(hB i hi).1]; exact (hB i hi).2) fun j hj x hx => ?_
    rw [(hst i hi).1] at hj
    rw [(hst i hi).2 j hj x hx]
    exact hSlt i hi j hj x hx
  have hcs : (cLevels n base (allSteps S (pinvs n S) base)).size = nb := by simp [cLevels, hb]
  have hmb : ∀ i < nb, ∀ k < Mr i, k ≠ 0 → PAR i k < Mr i ∧ LAB i k < Nat.mul 2 (LEN i) := by
    intro i hi k hk hk0
    obtain ⟨a, b⟩ := cbPt_bounds (hp i hi k hk) hk0
    exact ⟨by omega, b⟩
  have horb : cOrbitSizes n S base = (List.range nb).map Mr := by
    unfold cOrbitSizes
    apply List.ext_getElem
    · simp [hcs]
    · intro i h1 h2
      have hi : i < nb := by simpa using h2
      simp only [List.getElem_map, Array.getElem_toList, List.getElem_range]
      rw [← getElem!_pos (cLevels n base (allSteps S (pinvs n S) base)) i (by rw [hcs]; exact hi),
        hlev i hi, Array.size_ofFn]
  refine ⟨?_, horb⟩
  unfold fullChainOK chainOK
  dsimp only
  generalize cLevels n base (allSteps S (pinvs n S) base) = LV at hlev hcs hcl ⊢
  generalize allSteps S (pinvs n S) base = SV at hst hcl ⊢
  generalize allInvSteps S (pinvs n S) base = IV at hinv ⊢
  have hpos : ∀ i < nb, ∀ x < n, LV[i]!.pos[x]! = POS i x := fun i hi x hx => by
    rw [hlev i hi]
    exact getD_ofFn hx
  have hsz : ∀ i < nb, LV[i]!.pts.size = Mr i := fun i hi => by
    rw [hlev i hi, Array.size_ofFn]
  have hptsv : ∀ i < nb, ∀ k < Mr i, LV[i]!.pts[k]! = PTS i k := fun i hi k hk => by
    rw [hlev i hi]
    exact getD_ofFn hk
  have tlt : ∀ l < nb, ∀ k < Mr l, ∀ p < n,
      trInvK (PAR l) (LAB l) (invX F FI (IDX l) (LEN l)) (Mr l) k p < n :=
    fun l hl k hk p hpn => trInvK_lt_nz (hmb l hl) (hIlt l hl) _ _ _ hk hpn
  have hpidv : ∀ t < n, (pid n)[t]! = t := fun t ht => getD_ofFn (f := fun i => i) ht
  have hpids : (pid n).size = n := by simp [pid]
  have sift : ∀ f l, l + f = nb → ∀ (img : Array Nat) (ψ : Nat → Nat), img.size = n →
      (∀ y < n, img[y]! = ψ y) → (∀ y < n, ψ y < n) →
      siftG n POS PAR LAB Mr B (fun i => invX F FI (IDX i) (LEN i)) f l
        ((List.range n).map ψ) = true →
      psift LV IV (pid n) base true l img = true := by
    intro f
    induction f with
    | zero =>
      intro l hl img ψ hs hv hψ h
      rw [siftG_zeroG] at h
      have e := listEqK_eqG _ _ h
      rw [psift_end_full (by rw [hcs]; omega), allBelowN_iff']
      intro t ht
      rw [hpids] at ht
      rw [hv t ht, map_selfG e t (List.mem_range.2 ht), hpidv t ht]
      exact beq_self_eq_true t
    | succ f ih =>
      intro l hl img ψ hs hv hψ h
      have hln : l < nb := by omega
      have hBl := hB l hln
      rw [siftG_succG, bAnd_iff] at h
      have e0 : List.getD ((List.range n).map ψ) (B l) 0 = ψ (B l) := by
        rw [List.getD_eq_getElem _ _ (by simpa using hBl.2)]
        simp
      rw [e0] at h
      obtain ⟨hk, h⟩ := h
      have hk' : POS l (ψ (B l)) < Mr l := Nat.blt_eq.mp hk
      rw [psift_step (by rw [hcs]; exact hln), hBl.1, hv _ hBl.2,
        hpos l hln _ (hψ _ hBl.2), hsz l hln, decide_eq_true hk', Bool.true_and]
      refine ih (l + 1) (by omega) _ (fun y => trInvK (PAR l) (LAB l)
        (invX F FI (IDX l) (LEN l)) (Mr l) (POS l (ψ (B l))) (ψ y))
        (by rw [Array.size_map, hs]) (fun y hy => ?_) (fun y hy => tlt l hln _ hk' _ (hψ y hy)) ?_
      · rw [getElem!_pos _ y (by rw [Array.size_map, hs]; exact hy), Array.getElem_map,
          ← getElem!_pos img y (by rw [hs]; exact hy), hv y hy, hlev l hln]
        exact trInvApp_eq_nz (hmb l hln) (fun j hj x hx => hinv l hln j hj x hx) (Mr l) _ (ψ y)
          hk' (hψ y hy)
      · rw [mapK_eqG, List.map_map] at h
        exact h
  have hschr : ∀ i < nb, cschreierOK LV SV IV (pid n) base true i chunks = true := by
    intro i hi
    unfold cschreierOK
    dsimp only
    rw [hsz i hi, (hst i hi).1]
    refine parBelow_ofG fun h hh => allBelowN_iff'.2 fun j hj => ?_
    have hpt := cbPt_ptG (hp i hi h hh)
    rw [hptsv i hi h hh, (hst i hi).2 j hj _ hpt.1, hpos i hi _ (hSlt i hi j hj _ hpt.1)]
    have hs0 := hsch i hi h hh j hj
    rw [schG_eqG, bAnd_iff] at hs0
    generalize POS i (stepX F FI (IDX i) (LEN i) j (PTS i h)) = K at hs0 ⊢
    obtain ⟨hk, hs0⟩ := hs0
    have hk' : K < Mr i := Nat.blt_eq.mp hk
    rw [decide_eq_true hk', Bool.true_and]
    have hstv : ∀ j < Nat.mul 2 (LEN i), ∀ x < n,
        ((SV[i]!)[j]!)[x]! = stepX F FI (IDX i) (LEN i) j x ∧ stepX F FI (IDX i) (LEN i) j x < n :=
      fun j hj x hx => ⟨(hst i hi).2 j hj x hx, hSlt i hi j hj x hx⟩
    refine sift (nb - (i + 1)) (i + 1) (by omega) _ (schImg (fun i => stepX F FI (IDX i) (LEN i))
      (fun i => invX F FI (IDX i) (LEN i)) PAR LAB Mr i h j K) ?_ (fun y hy => ?_) (fun y hy => ?_)
      hs0
    · unfold schreierImgs
      rw [Array.size_map, hpids]
    · have htk := trK_lt_nzG (hmb i hi) (hSlt i hi) (Mr i) h y hh hy
      unfold schreierImgs
      rw [getElem!_pos _ y (by rw [Array.size_map, hpids]; exact hy), Array.getElem_map,
        ← getElem!_pos (pid n) y (by rw [hpids]; exact hy), hpidv y hy, hsz i hi, hlev i hi,
        trApp_eqG (hmb i hi) hstv (Mr i) h y hh hy, (hst i hi).2 j hj _ htk,
        trInvApp_eq_nz (hmb i hi) (hinv i hi) (Mr i) K _ hk' (hSlt i hi j hj _ htk)]
      rfl
    · exact trInvK_lt_nz (hmb i hi) (hIlt i hi) _ _ _ hk'
        (hSlt i hi j hj _ (trK_lt_nzG (hmb i hi) (hSlt i hi) (Mr i) h y hh hy))
  have c1 : decide (m ≤ S.size) = true := decide_eq_true (by omega)
  have c2 : (W.size == S.size) = true := by
    rw [hWs, hS]
    exact beq_self_eq_true s
  have c3 : allBelowN S.size (fun j => pisInv n S[j]! (pinvs n S)[j]!) = true := by
    rw [allBelowN_iff']
    intro j hj
    rw [hS] at hj
    unfold pisInv
    rw [allBelowN_iff']
    intro x hx
    rw [(hF j hj x hx).1, hSi j hj _ (hF j hj x hx).2.1, (hF j hj x hx).2.2.2]
    simp [(hF j hj x hx).2.1]
  have c4 : allBelowN S.size (fun j => decide (j < m) ||
      (plettersOK j W[j]! && peq n S[j]! (pword n S (pinvs n S) W[j]!))) = true := by
    rw [allBelowN_iff']
    intro j hj
    rw [hS] at hj
    by_cases hjm : j < m
    · simp [hjm]
    · obtain ⟨hl, hf⟩ := hW j (by omega) hj
      have hL : CFSG.KS.PW.LettersOK n j S (pinvs n S) F FI := fun j' hj' x hx =>
        ⟨(hF j' (by omega) x hx).1, hSi j' (by omega) x hx, (hF j' (by omega) x hx).2.1,
          (hF j' (by omega) x hx).2.2.1⟩
      have hpl : plettersOK j W[j]! = true := by
        unfold plettersOK
        rw [List.all_eq_true]
        intro l hl'
        obtain ⟨h1, h2⟩ := hl l hl'
        simp [h1, h2]
      have hpe : peq n S[j]! (pword n S (pinvs n S) W[j]!) = true := by
        unfold peq
        rw [allBelowN_iff']
        intro x hx
        rw [(hF j hj x hx).1, (CFSG.KS.PW.pword_get hL W[j]! hl x hx).1, ← hf x hx]
        exact beq_self_eq_true _
      rw [hpl, hpe]
      simp
  have c5 : allBelowN base.size (fun i => decide (base[i]! < n)) = true := by
    rw [allBelowN_iff']
    intro i hi
    rw [hb] at hi
    rw [(hB i hi).1]
    exact decide_eq_true (hB i hi).2
  have c6 : (base.size == base.size) = true := beq_self_eq_true _
  have c7 : allBelowN base.size (fun i => decide (base[i]! < (pid n).size) &&
      (pid n)[base[i]!]! == base[i]!) = true := by
    rw [allBelowN_iff']
    intro i hi
    rw [hb] at hi
    rw [(hB i hi).1, hpids, hpidv _ (hB i hi).2]
    simp [(hB i hi).2]
  have c8 : allBelowN (pid n).size (fun t => decide ((pid n)[t]! < n)) = true := by
    rw [allBelowN_iff']
    intro t ht
    rw [hpids] at ht
    rw [hpidv t ht]
    exact decide_eq_true ht
  have c9 : (!true || allBelowN S.size fun j => !(pfixes base S[j]! base.size) ||
      peq n S[j]! (pid n)) = true := by
    rw [Bool.not_true, Bool.false_or, allBelowN_iff']
    intro j hj
    rw [hS] at hj
    rw [hb, pfixes_eqG hF hB (Nat.le_refl nb) hj]
    have ht := allN_spec hterm j hj
    rw [bIf_v] at ht
    by_cases hfx : fixesK F B nb j = true
    · rw [if_pos hfx] at ht
      rw [hfx, Bool.not_true, Bool.false_or]
      unfold peq
      rw [allBelowN_iff']
      intro x hx
      rw [(hF j hj x hx).1, hpidv x hx, Nat.eq_of_beq_eq_true (allN_spec ht x hx)]
      exact beq_self_eq_true _
    · rw [Bool.eq_false_iff.2 hfx]
      rfl
  have c10 : allBelowN base.size (fun i => clevelOK n base[i]! SV[i]! LV[i]!) = true := by
    rw [allBelowN_iff']
    intro i hi
    rw [hb] at hi
    exact hcl i hi
  have c11 : allBelowN base.size (fun i => cschreierOK LV SV IV (pid n) base true i chunks) =
      true := by
    rw [allBelowN_iff']
    intro i hi
    rw [hb] at hi
    exact hschr i hi
  rw [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11]
  rfl

end CFSG.KS.CH.GKS

end
