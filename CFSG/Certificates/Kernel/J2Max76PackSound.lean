module

public import Certificates.Data.Kernel.J2Max76Pack

public section

namespace CFSG.KC.J2Max76

open Certificates.K76J2Max Certificates.G2ThreeMax CFSG.Monster.B.TwoA.Census CFSG.KC.Bfs

theorem pin1_lane (W : ℕ) (L : List ℕ) (PK : ℕ) (h : pin1 W L PK = true) (j : ℕ) :
    lane PK W j = L.getD j 0 := by
  induction L generalizing PK j with
  | nil =>
    have h0 : PK = 0 := Nat.eq_of_beq_eq_true h
    subst h0
    change (0 >>> (W * j)) &&& _ = 0
    rw [Nat.zero_shiftRight, Nat.zero_and]
  | cons a l ih =>
    change Bool.rec (motive := fun _ => Bool) false (pin1 W l (Nat.shiftRight PK W))
      (Nat.beq (Nat.land PK (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))) a) = true at h
    cases ha : Nat.beq (Nat.land PK (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))) a
    · rw [ha] at h
      exact absurd h Bool.false_ne_true
    · rw [ha] at h
      cases j with
      | zero =>
        change Nat.land (PK >>> (W * 0)) _ = a
        rw [Nat.mul_zero, Nat.shiftRight_zero]
        exact Nat.eq_of_beq_eq_true ha
      | succ j =>
        have e := ih (Nat.shiftRight PK W) h j
        change Nat.land (PK >>> (W * (j + 1))) _ = l.getD j 0
        rw [Nat.mul_succ, Nat.add_comm, Nat.shiftRight_add]
        exact e

theorem flatten_getD (m : ℕ) (rows : List (List ℕ)) (hl : ∀ r ∈ rows, r.length = m) (i k : ℕ)
    (hk : k < m) : rows.flatten.getD (m * i + k) 0 = (rows.getD i []).getD k 0 := by
  induction rows generalizing i with
  | nil => simp
  | cons r rs ih =>
    have hr : r.length = m := hl r (List.mem_cons_self ..)
    rw [List.flatten_cons]
    cases i with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero, List.getD_append _ _ _ _ (by omega)]
    | succ i =>
      rw [List.getD_cons_succ, List.getD_append_right _ _ _ _ (by rw [hr]; nlinarith),
        ← ih (fun r' h' => hl r' (List.mem_cons_of_mem _ h')) i, hr]
      congr 1
      rw [Nat.mul_succ]
      omega

theorem pinT_rdT (PK W m : ℕ) (rows : List (List ℕ)) (h : pinT PK W m rows = true) (i k : ℕ) :
    rdT PK W m i k = (rows.getD i []).getD k 0 := by
  unfold pinT at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hl : ∀ r ∈ rows, r.length = m := fun r hr => beq_iff_eq.mp (h.1 r hr)
  unfold rdT
  by_cases hk : k < m
  · have hb : Nat.blt k m = true := Nat.blt_eq.mpr hk
    rw [hb]
    change lane PK W (m * i + k) = _
    rw [pin1_lane W _ PK h.2, flatten_getD m rows hl i k hk]
  · have hb : Nat.blt k m = false := Bool.eq_false_iff.mpr fun e => hk (Nat.blt_eq.mp e)
    rw [hb]
    symm
    apply List.getD_eq_default
    by_cases hi : i < rows.length
    · rw [List.getD_eq_getElem _ _ hi, hl _ (List.getElem_mem hi)]
      omega
    · rw [List.getD_eq_default _ _ (by omega)]
      simp

theorem arr_getD {α : Type} [Inhabited α] (a : Array α) (i : ℕ) :
    a[i]! = a.toList.getD i default := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases a[i]? <;> rfl

theorem arr2_getD (a : Array (Array ℕ)) (i k : ℕ) :
    (a[i]!)[k]! = ((a.toList.map Array.toList).getD i []).getD k 0 := by
  rw [arr_getD a i, arr_getD]
  change _ = ((List.map Array.toList a.toList).getD i (Array.toList default)).getD k 0
  rw [List.getD_map]
  rfl

theorem pinT_arr (PK W m : ℕ) (a : Array (Array ℕ)) (h : pinT PK W m (a.toList.map Array.toList) = true)
    (i k : ℕ) : (a[i]!)[k]! = rdT PK W m i k := by
  rw [arr2_getD, pinT_rdT PK W m _ h]

theorem pinT_size (PK W m n : ℕ) (a : Array (Array ℕ)) (hn : a.size = n)
    (h : pinT PK W m (a.toList.map Array.toList) = true) (i : ℕ) : (a[i]!).size = rszR n m i := by
  unfold pinT at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  unfold rszR
  rw [arr_getD]
  by_cases hi : i < n
  · rw [Nat.blt_eq.mpr hi]
    have hi' : i < a.toList.length := by simpa [hn] using hi
    rw [List.getD_eq_getElem _ _ hi', ← Array.length_toList]
    exact beq_iff_eq.mp (h.1 _ (List.mem_map.mpr ⟨_, List.getElem_mem hi', rfl⟩))
  · have hb : Nat.blt i n = false := Bool.eq_false_iff.mpr fun e => hi (Nat.blt_eq.mp e)
    rw [hb, List.getD_eq_default _ _ (by simp [hn]; omega)]
    rfl

theorem natCertOK_eq_R (act : ℕ → ℕ → ℕ) (ngen : ℕ) (valid : ℕ → Bool) (root : ℕ)
    (c : NatCert) :
    natCertOK act ngen valid root c = natCertR act ngen valid root c.pts.size (fun i => c.pts[i]!)
      (fun i k => (c.edges[i]!)[k]!) (fun i => (c.edges[i]!).size) (fun i => c.par[i]!)
      (fun i => c.lab[i]!) c.pts.toList := by
  unfold natCertOK natCertR natPointOK natPointR
  rw [List.mergeSort_eq_insertionSort (r := (· ≤ ·))]

theorem natCertOK_eq_P (act : ℕ → ℕ → ℕ) (ngen : ℕ) (valid : ℕ → Bool) (root : ℕ)
    (c : NatCert) (n W PKp PKe PKpar PKlab : ℕ)
    (h : certPin c n W ngen PKp PKe PKpar PKlab = true) :
    natCertOK act ngen valid root c = natCertP act ngen valid root n W ngen PKp PKe PKpar PKlab
      c.pts.toList := by
  unfold certPin at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hn, hen⟩, hp⟩, he⟩, hpar⟩, hlab⟩ := h
  rw [natCertOK_eq_R, hn]
  unfold natCertP
  have eP : (fun i => c.pts[i]!) = lane PKp W := funext fun i => by
    rw [pin1_lane W _ PKp hp, arr_getD]
    rfl
  have eE : (fun i k => (c.edges[i]!)[k]!) = rdT PKe 9 ngen :=
    funext fun i => funext fun k => pinT_arr PKe 9 ngen c.edges he i k
  have eR : (fun i => (c.edges[i]!).size) = rszR n ngen :=
    funext fun i => pinT_size PKe 9 ngen n c.edges hen he i
  have ePar : (fun i => c.par[i]!) = lane PKpar 9 := funext fun i => by
    rw [pin1_lane 9 _ PKpar hpar, arr_getD]
    rfl
  have eLab : (fun i => c.lab[i]!) = lane PKlab 9 := funext fun i => by
    rw [pin1_lane 9 _ PKlab hlab, arr_getD]
    rfl
  rw [eP, eE, eR, ePar, eLab]

theorem hAct_eq_R (hp : Array (Array ℕ)) (PKh : ℕ)
    (h : pinT PKh 9 280 (hp.toList.map Array.toList) = true) : hAct hp = hR PKh :=
  funext fun s => funext fun i => pinT_arr PKh 9 280 hp h s i

theorem repAct_eq_R (hp : Array (Array ℕ)) (rp : Array ℕ) (PKh PKrp : ℕ) (hs : hp.size = 3)
    (h : pinT PKh 9 280 (hp.toList.map Array.toList) = true) (hr : pin1 9 rp.toList PKrp = true) :
    repAct hp rp = repR PKh PKrp := by
  funext s i
  unfold repAct repR
  rw [hs]
  by_cases h3 : s < 3
  · rw [if_pos h3, Nat.blt_eq.mpr h3]
    exact pinT_arr PKh 9 280 hp h s i
  · have hb : Nat.blt s 3 = false := Bool.eq_false_iff.mpr fun e => h3 (Nat.blt_eq.mp e)
    rw [if_neg h3, hb]
    change rp[i]! = lane PKrp 9 i
    rw [pin1_lane 9 _ PKrp hr, arr_getD]
    rfl

theorem tabOf_eq_R (c : NatCert) (PKe : ℕ)
    (h : pinT PKe 9 5 (c.edges.toList.map Array.toList) = true) : tabOf c = tabR PKe :=
  funext fun k => funext fun i => pinT_arr PKe 9 5 c.edges h i k

theorem permArr_toList (c : NatCert) (w : List ℕ) :
    (permArr c w).toList = permL (tabOf c) c.pts.size w := by
  unfold permArr permL applyW
  rw [Array.toList_map, Array.toList_range]

theorem nTabs_toList (c : NatCert) :
    (nTabs c).toList.map Array.toList = [permL (tabOf c) c.pts.size [2],
      permL (tabOf c) c.pts.size [3], permL (tabOf c) c.pts.size [4]] := by
  unfold nTabs
  rw [← permArr_toList, ← permArr_toList, ← permArr_toList]
  rfl

theorem certPin_size (c : NatCert) (n W m PKp PKe PKpar PKlab : ℕ)
    (h : certPin c n W m PKp PKe PKpar PKlab = true) : c.pts.size = n := by
  unfold certPin at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1

theorem certPin_edges (c : NatCert) (n W m PKp PKe PKpar PKlab : ℕ)
    (h : certPin c n W m PKp PKe PKpar PKlab = true) :
    pinT PKe 9 m (c.edges.toList.map Array.toList) = true := by
  unfold certPin at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem okOrbs_of(hp : Array (Array ℕ)) (N : ℕ) (orbs : List (ℕ × NatCert))
    (h1 : ∀ t ∈ orbs, natCertOK (hAct hp) hp.size (fun u => decide (u < N)) t.1 t.2 = true)
    (h2 : ((orbs.flatMap fun t => t.2.pts.toList).insertionSort (· ≤ ·) == List.range N) = true) :
    okOrbs hp N orbs = true := by
  unfold okOrbs
  rw [List.mergeSort_eq_insertionSort (r := (· ≤ ·)), h2, Bool.and_true, List.all_eq_true]
  exact h1

theorem repLitOK_of_P (c : NatCert) (hp : Array (Array ℕ)) (r : ℕ) (w : List ℕ) (rp : Array ℕ)
    (c₃ : NatCert) (PKh PKrp PKp PKe PKpar PKlab : ℕ) (hs : hp.size = 3)
    (hh : pinT PKh 9 280 (hp.toList.map Array.toList) = true) (hr : pin1 9 rp.toList PKrp = true)
    (hc : certPin c₃ 280 9 4 PKp PKe PKpar PKlab = true)
    (h : repLitP c PKh r w PKrp PKp PKe PKpar PKlab c₃.pts.toList = true) :
    repLitOK c hp r w rp c₃ = true := by
  unfold repLitOK
  rw [natCertOK_eq_P _ _ _ _ c₃ 280 9 PKp PKe PKpar PKlab hc, repAct_eq_R hp rp PKh PKrp hs hh hr,
    List.mergeSort_eq_insertionSort (r := (· ≤ ·))]
  exact h

end CFSG.KC.J2Max76
