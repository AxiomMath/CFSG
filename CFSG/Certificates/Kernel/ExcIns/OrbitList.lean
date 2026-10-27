module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideImg
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcInsideTransport

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6} {T : Chk.Tabs}

private theorem rtR_val (hT : Chk.tabsOK m T = true) (u t : Root m) :
    (rtR hT u t).val = (T.rt[u.val]!)[t.val]! := rfl

theorem rt_rt (hT : Chk.tabsOK m T = true) (u t : Root m) :
    (T.rt[u.val]!)[(T.rt[u.val]!)[t.val]!]! = t.val := by
  obtain ⟨ε, hε, h1, -⟩ := rtR_spec hT u (rtR hT u t)
  obtain ⟨δ, hδ, h2, -⟩ := rtR_spec hT u t
  have hεδ : ε * δ = 1 ∨ ε * δ = -1 := by
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> norm_num
  have heq : rtR hT u (rtR hT u t) = t := by
    refine eq_of_root_eq_sign hεδ fun v => ?_
    have hrr : reflection m u (reflection m u v) = v :=
      Module.involutive_reflection (root_coroot m u) v
    rw [h1, h2, hrr, Int.cast_mul, mul_assoc]
  exact congrArg Fin.val heq

private theorem adj_bit_iff (hT : Chk.tabsOK m T = true) (i j : Root m) :
    (T.adj[i.val]!).testBit j.val = true ↔ Adj m i j :=
  ⟨fun h => by
    obtain ⟨_, ha⟩ := (tabsOK_adj hT i j.val).mp h
    exact ha, fun h => (tabsOK_adj hT i j.val).mpr ⟨j.isLt, h⟩⟩

theorem adj_rt (hT : Chk.tabsOK m T = true) (u i j : Root m) :
    (T.adj[(T.rt[u.val]!)[i.val]!]!).testBit ((T.rt[u.val]!)[j.val]!) =
      (T.adj[i.val]!).testBit j.val := by
  rw [Bool.eq_iff_iff, ← rtR_val hT u i, ← rtR_val hT u j, adj_bit_iff hT, adj_bit_iff hT,
    adj_rtR_iff]

private theorem ofMask_or (a b : ℕ) :
    ofMask m (a ||| b) = ofMask m a ∪ ofMask m b := by
  ext t
  simp [ofMask, Nat.testBit_or]

private theorem ofMask_one (i : Root m) :
    ofMask m (1 <<< i.val) = {i} := by
  ext t
  rw [mem_ofMask, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq,
    Finset.mem_singleton, Fin.ext_iff]
  exact eq_comm

private theorem one_lt (i : Root m) : 1 <<< i.val < 2 ^ nroots m := by
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by norm_num) i.isLt

private theorem eq_of_ofMask_eq {a b : ℕ} (ha : a < 2 ^ nroots m) (hb : b < 2 ^ nroots m)
    (h : ∀ t : Root m, t ∈ ofMask m a ↔ t ∈ ofMask m b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < nroots m
  · rw [Bool.eq_iff_iff, ← mem_ofMask (t := ⟨t, ht⟩), ← mem_ofMask (t := ⟨t, ht⟩)]
    exact h ⟨t, ht⟩
  · have hpow : 2 ^ nroots m ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt ht)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hpow)]

private theorem imgN_or (hT : Chk.tabsOK m T = true) (u : Root m) (a b : ℕ) :
    Chk.imgN T (nroots m) u (a ||| b) =
      Chk.imgN T (nroots m) u a ||| Chk.imgN T (nroots m) u b := by
  refine eq_of_ofMask_eq (imgN_lt hT u _) (Nat.or_lt_two_pow (imgN_lt hT u a) (imgN_lt hT u b))
    fun t => ?_
  simp only [ofMask_or, Finset.mem_union, mem_ofMask_imgN]
  exact ⟨fun ⟨s, hs, hst⟩ => hs.elim (fun h => Or.inl ⟨s, h, hst⟩)
      (fun h => Or.inr ⟨s, h, hst⟩),
    fun h => h.elim (fun ⟨s, hs, hst⟩ => ⟨s, Or.inl hs, hst⟩)
      (fun ⟨s, hs, hst⟩ => ⟨s, Or.inr hs, hst⟩)⟩

private theorem imgN_one (hT : Chk.tabsOK m T = true) (u j : Root m) :
    Chk.imgN T (nroots m) u (1 <<< j.val) = 1 <<< (rtR hT u j).val := by
  refine eq_of_ofMask_eq (imgN_lt hT u _) (one_lt _) fun t => ?_
  rw [mem_ofMask_imgN, ofMask_one, ofMask_one, Finset.mem_singleton]
  constructor
  · rintro ⟨s, hs, hst⟩
    rw [Finset.mem_singleton] at hs
    subst hs
    exact Fin.ext hst.symm
  · intro h
    exact ⟨j, Finset.mem_singleton_self j, by rw [h]; rfl⟩

theorem imgW_cons (u : Root m) (w : List (Root m)) (c : ℕ) :
    imgW T m (u :: w) c = Chk.imgN T (nroots m) u (imgW T m w c) := rfl

theorem imgW_lt (hT : Chk.tabsOK m T = true) (w : List (Root m)) {c : ℕ}
    (hc : c < 2 ^ nroots m) : imgW T m w c < 2 ^ nroots m := by
  cases w with
  | nil => exact hc
  | cons u w => exact imgN_lt hT u _

theorem imgW_induction {G : Root m → Prop} (P : ℕ → Prop)
    (hP : ∀ u, G u → ∀ n, P n → P (Chk.imgN T (nroots m) u n)) {w : List (Root m)}
    (hw : ∀ u ∈ w, G u) {c : ℕ} (hc : P c) : P (imgW T m w c) := by
  induction w with
  | nil => exact hc
  | cons u w ih =>
    rw [imgW_cons]
    exact hP u (hw u List.mem_cons_self) _ (ih fun v hv => hw v (List.mem_cons_of_mem u hv))

theorem exists_growC_imgW (hT : Chk.tabsOK m T = true) {G : Root m → Prop} {ι : Type*}
    {R : ι → ℕ} (hR : ∀ x, R x < 2 ^ nroots m)
    (hGrow : ∀ x, ∀ j : Root m, (R x).testBit j.val = false → T.adj[j.val]! &&& R x ≠ 0 →
      ∃ y w, (∀ u ∈ w, G u) ∧
        Chk.growC T (dim m) (nroots m) (R x ||| 1 <<< j.val) = imgW T m w (R y))
    (w : List (Root m)) (hw : ∀ u ∈ w, G u) (x : ι) (j : Root m)
    (hj : j ∉ ofMask m (imgW T m w (R x))) (hadj : T.adj[j.val]! &&& imgW T m w (R x) ≠ 0) :
    ∃ y w', (∀ u ∈ w', G u) ∧
      Chk.growC T (dim m) (nroots m) (imgW T m w (R x) ||| 1 <<< j.val) = imgW T m w' (R y) := by
  induction w generalizing j with
  | nil =>
    refine hGrow x j ?_ hadj
    by_contra hb
    exact hj (mem_ofMask.mpr (Bool.not_eq_false _ ▸ hb))
  | cons u w ih =>
    have hwu : G u := hw u List.mem_cons_self
    have hww : ∀ v ∈ w, G v := fun v hv => hw v (List.mem_cons_of_mem u hv)
    set n₀ := imgW T m w (R x) with hn₀
    have hn : imgW T m (u :: w) (R x) = Chk.imgN T (nroots m) u n₀ := imgW_cons u w (R x)
    rw [hn] at hj hadj ⊢
    let j' : Root m := rtR hT u j
    have hinvj : (T.rt[u.val]!)[j'.val]! = j.val := rt_rt hT u j
    have hj'not : j' ∉ ofMask m n₀ := by
      intro hj'
      exact hj ((mem_ofMask_imgN u n₀ j).mpr ⟨j', hj', hinvj⟩)
    have hjadj' : T.adj[j'.val]! &&& n₀ ≠ 0 := by
      obtain ⟨s, hs⟩ := Nat.exists_testBit_of_ne_zero hadj
      rw [Nat.testBit_and, Bool.and_eq_true] at hs
      obtain ⟨hsr, -⟩ := (tabsOK_adj hT j s).mp hs.1
      have hmem : (⟨s, hsr⟩ : Root m) ∈ ofMask m (Chk.imgN T (nroots m) u n₀) :=
        mem_ofMask.mpr hs.2
      obtain ⟨t, htmem, hrt⟩ := (mem_ofMask_imgN u n₀ _).mp hmem
      have hAt : (T.adj[j'.val]!).testBit t.val = true := by
        have h := adj_rt hT u j' t
        rw [hinvj, hrt] at h
        rw [← h]
        exact hs.1
      intro hzero
      have hb : (T.adj[j'.val]! &&& n₀).testBit t.val = true := by
        rw [Nat.testBit_and, Bool.and_eq_true]
        exact ⟨hAt, mem_ofMask.mp htmem⟩
      rw [hzero] at hb
      exact absurd hb (by simp)
    obtain ⟨y, w₁, hw₁, hgr⟩ := ih hww j' hj'not hjadj'
    have hcand : n₀ ||| 1 <<< j'.val < 2 ^ nroots m :=
      Nat.or_lt_two_pow (imgW_lt hT w (hR x)) (one_lt j')
    refine ⟨y, u :: w₁, fun v hv => ?_, ?_⟩
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact hwu
      · exact hw₁ v hv
    · have himg : Chk.imgN T (nroots m) u (n₀ ||| 1 <<< j'.val) =
          Chk.imgN T (nroots m) u n₀ ||| 1 <<< j.val := by
        rw [imgN_or hT u, imgN_one hT u j']
        congr 2
      rw [← himg, growC_imgN hT (rt_rt hT u) (adj_rt hT u) hcand, hgr, imgW_cons]

private theorem le_cent_of_vanish {U : Submodule (ZMod 3) (V m)} {Y : Finset (Root m)}
    (h : ∀ i ∈ Y, Vanish m U i) : U ≤ cent m Y := by
  intro u hu
  simp only [cent, Submodule.mem_iInf, LinearMap.mem_ker]
  exact fun i hi => h i hi u hu

theorem exists_imgW_of_occurs (hT : Chk.tabsOK m T = true) {G : Root m → Prop} {ι : Type*}
    {R : ι → ℕ} (hR : ∀ x, R x < 2 ^ nroots m)
    (hSeed : ∀ i : Root m, ∃ x w, (∀ u ∈ w, G u) ∧
      Chk.growC T (dim m) (nroots m) (1 <<< i.val) = imgW T m w (R x))
    (hGrow : ∀ x, ∀ j : Root m, (R x).testBit j.val = false → T.adj[j.val]! &&& R x ≠ 0 →
      ∃ y w, (∀ u ∈ w, G u) ∧
        Chk.growC T (dim m) (nroots m) (R x ||| 1 <<< j.val) = imgW T m w (R y))
    {U : Submodule (ZMod 3) (V m)} {c : Finset (Root m)} (hc : occurs m U c) :
    ∃ x w, (∀ u ∈ w, G u) ∧ ofMask m (imgW T m w (R x)) = c := by
  have hc' := hc
  simp only [occurs, IsComp] at hc'
  obtain ⟨hne, hvan, hclosed, hmin⟩ := hc'
  obtain ⟨i₀, hi₀⟩ := hne
  have hUle : U ≤ cent m (ofMask m (1 <<< i₀.val)) := by
    refine le_cent_of_vanish ?_
    intro t ht
    rw [ofMask_one] at ht
    obtain rfl := Finset.mem_singleton.mp ht
    exact hvan t hi₀
  have hcM₀ : ofMask m (Chk.growC T (dim m) (nroots m) (1 <<< i₀.val)) ⊆ c := by
    refine growC_subset (C := c) hT (one_lt i₀) ?_ ?_
    · rw [ofMask_one]
      exact Finset.singleton_subset_iff.mpr hi₀
    · intro i hi j hv hadj
      exact hclosed i hi j (fun u hu => hv u (hUle hu)) hadj
  have hi₀M₀ : i₀ ∈ ofMask m (Chk.growC T (dim m) (nroots m) (1 <<< i₀.val)) :=
    subset_growC (1 <<< i₀.val) (by rw [ofMask_one]; exact Finset.mem_singleton_self i₀)
  have key : ∀ k : ℕ, ∀ M : ℕ, (c \ ofMask m M).card = k →
      (∃ x w, (∀ u ∈ w, G u) ∧ imgW T m w (R x) = M) → ofMask m M ⊆ c →
      i₀ ∈ ofMask m M → ∃ x w, (∀ u ∈ w, G u) ∧ ofMask m (imgW T m w (R x)) = c := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro M hk hM hMc hi₀M
      obtain ⟨x, w, hw, hxM⟩ := hM
      by_cases hEq : ofMask m M = c
      · exact ⟨x, w, hw, by rw [hxM, hEq]⟩
      · have hSne : (ofMask m M).Nonempty := ⟨i₀, hi₀M⟩
        have hnotclosed : ¬ (∀ i ∈ ofMask m M, ∀ j ∈ c, Adj m i j → j ∈ ofMask m M) := by
          intro hcl
          exact hEq (hmin (ofMask m M) hMc hSne hcl)
        have hex : ∃ i ∈ ofMask m M, ∃ j ∈ c, Adj m i j ∧ j ∉ ofMask m M := by
          by_contra h
          exact hnotclosed fun i hi j hj hadj => by
            by_contra hjS
            exact h ⟨i, hi, j, hj, hadj, hjS⟩
        obtain ⟨i, hiS, j, hjc, hadj, hjS⟩ := hex
        have hadj' : Adj m j i := by
          simpa only [Adj, or_comm] using hadj
        have hbit : (T.adj[j.val]!).testBit i.val = true := (adj_bit_iff hT j i).mpr hadj'
        have hiM : M.testBit i.val = true := (mem_ofMask (t := i)).mp hiS
        have hne : T.adj[j.val]! &&& M ≠ 0 := by
          intro hzero
          have hb : (T.adj[j.val]! &&& M).testBit i.val = true := by
            rw [Nat.testBit_and, Bool.and_eq_true]
            exact ⟨hbit, hiM⟩
          rw [hzero] at hb
          exact absurd hb (by simp)
        have hjS' : j ∉ ofMask m (imgW T m w (R x)) := by rwa [hxM]
        have hne' : T.adj[j.val]! &&& imgW T m w (R x) ≠ 0 := by rwa [hxM]
        obtain ⟨y, w', hw', hyM⟩ :=
          exists_growC_imgW hT hR hGrow w hw x j hjS' hne'
        rw [hxM] at hyM
        let M' : ℕ := Chk.growC T (dim m) (nroots m) (M ||| 1 <<< j.val)
        have hM' : ∃ y w, (∀ u ∈ w, G u) ∧ imgW T m w (R y) = M' := ⟨y, w', hw', hyM.symm⟩
        have hMlt : M < 2 ^ nroots m := by
          rw [← hxM]
          exact imgW_lt hT w (hR x)
        have hbitlt : M ||| 1 <<< j.val < 2 ^ nroots m := Nat.or_lt_two_pow hMlt (one_lt j)
        have hMcUnion : ofMask m (M ||| 1 <<< j.val) ⊆ c := by
          rw [ofMask_or, ofMask_one]
          exact Finset.union_subset hMc (Finset.singleton_subset_iff.mpr hjc)
        have hUle' : U ≤ cent m (ofMask m (M ||| 1 <<< j.val)) := by
          refine le_cent_of_vanish ?_
          intro t ht
          exact hvan t (hMcUnion ht)
        have hMc' : ofMask m M' ⊆ c := by
          refine growC_subset (C := c) hT hbitlt hMcUnion ?_
          intro i hi jj hv hadjj
          exact hclosed i hi jj (fun u hu => hv u (hUle' hu)) hadjj
        have hsub : ofMask m (M ||| 1 <<< j.val) ⊆ ofMask m M' :=
          subset_growC (M ||| 1 <<< j.val)
        have hsubM : ofMask m M ⊆ ofMask m M' := fun t ht =>
          hsub (by rw [ofMask_or]; exact Finset.mem_union_left _ ht)
        have hi₀M' : i₀ ∈ ofMask m M' := hsubM hi₀M
        have hjM' : j ∈ ofMask m M' := hsub (by
          rw [ofMask_or, Finset.mem_union, ofMask_one]
          exact Or.inr (Finset.mem_singleton_self j))
        have hlt : (c \ ofMask m M').card < k := by
          rw [← hk]
          refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.mpr
            ⟨j, ?_, ?_⟩)
          · intro t ht
            rw [Finset.mem_sdiff] at ht ⊢
            exact ⟨ht.1, fun ht' => ht.2 (hsubM ht')⟩
          · rw [Finset.mem_sdiff]
            exact ⟨hjc, hjS⟩
          · intro h
            exact (Finset.mem_sdiff.mp h).2 hjM'
        exact ih _ hlt M' rfl hM' hMc' hi₀M'
  obtain ⟨x₀, w₀, hw₀, h₀⟩ := hSeed i₀
  exact key _ _ rfl ⟨x₀, w₀, hw₀, h₀.symm⟩ hcM₀ hi₀M₀

theorem exists_of_occurs (hT : Chk.tabsOK m T = true) {G : Root m → Prop} {ι : Type*}
    {R : ι → ℕ} (hR : ∀ x, R x < 2 ^ nroots m)
    (hSeed : ∀ i : Root m, ∃ x w, (∀ u ∈ w, G u) ∧
      Chk.growC T (dim m) (nroots m) (1 <<< i.val) = imgW T m w (R x))
    (hGrow : ∀ x, ∀ j : Root m, (R x).testBit j.val = false → T.adj[j.val]! &&& R x ≠ 0 →
      ∃ y w, (∀ u ∈ w, G u) ∧
        Chk.growC T (dim m) (nroots m) (R x ||| 1 <<< j.val) = imgW T m w (R y))
    (P : ℕ → Prop) (hP : ∀ u, G u → ∀ n, P n → P (Chk.imgN T (nroots m) u n))
    (hPR : ∀ x, P (R x)) {U : Submodule (ZMod 3) (V m)} {c : Finset (Root m)}
    (hc : occurs m U c) : ∃ n, P n ∧ ofMask m n = c := by
  obtain ⟨x, w, hw, hxc⟩ := exists_imgW_of_occurs hT hR hSeed hGrow hc
  exact ⟨_, imgW_induction P hP hw (hPR x), hxc⟩

theorem insideCensus_of_orbits (hT : Chk.tabsOK m T = true) {G : Root m → Prop} {ι : Type*}
    {R : ι → ℕ} (hG : ∀ u, G u → PairSigned m (rtR hT u)) (hR : ∀ x, R x < 2 ^ nroots m)
    (hSeed : ∀ i : Root m, ∃ x w, (∀ u ∈ w, G u) ∧
      Chk.growC T (dim m) (nroots m) (1 <<< i.val) = imgW T m w (R x))
    (hGrow : ∀ x, ∀ j : Root m, (R x).testBit j.val = false → T.adj[j.val]! &&& R x ≠ 0 →
      ∃ y w, (∀ u ∈ w, G u) ∧
        Chk.growC T (dim m) (nroots m) (R x ||| 1 <<< j.val) = imgW T m w (R y))
    (A : ℕ → Prop) (hA : ∀ u, G u → ∀ n, A n → A (Chk.imgN T (nroots m) u n))
    (hAflag : ∀ n, A n → InsideFlag m (ofMask m n))
    (hrep : ∀ x, InsideT m (ofMask m (R x)) ∨ A (R x)) : InsideCensus m := by
  intro U c hc
  obtain ⟨n, hn, rfl⟩ := exists_of_occurs hT hR hSeed hGrow
    (fun n => InsideT m (ofMask m n) ∨ A n)
    (fun u hu n h => h.elim (fun h' => Or.inl (insideT_imgN hT (hG u hu) h'))
      (fun h' => Or.inr (hA u hu n h'))) hrep hc
  rcases hn with h | h
  · exact h.census
  · exact Or.inr (hAflag n h)

end CFSG.StandardType.GGQ2Frame.ExcRaw
