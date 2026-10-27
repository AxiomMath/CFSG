module

public import CFSG.Certificates.Kernel.SporSch.HNT0Inv

public section

namespace CFSG.KS.HNT0

open CFSG.KC.Enum CFSG.KS CFSG.KS.EnumBase CFSG.KS.PEnum CFSG.KS.BaseEq CFSG.KC.LL
  CFSG.KC.LL.HNX CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5
  CFSG.Sporadic.Co2Rank

theorem strictN_eq₀ (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Enum.strictN y k = k y := by cases y <;> rfl

theorem strictB_eq₀ (y : ℕ) (k : ℕ → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem nIf_eq (c : Bool) (t e : ℕ) : nIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

theorem tb_land (a b i : ℕ) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i

theorem tb_lor (a b i : ℕ) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i

theorem tb_shr (a b i : ℕ) : (Nat.shiftRight a b).testBit i = a.testBit (b + i) :=
  Nat.testBit_shiftRight a

theorem tb_one_shl (c i : ℕ) : (Nat.shiftLeft 1 c).testBit i = decide (c = i) := by
  rw [PF.shl_eq, Nat.one_mul, Nat.testBit_two_pow]

theorem tb_low (n i : ℕ) : (Nat.sub (Nat.shiftLeft 1 n) 1).testBit i = decide (i < n) := by
  rw [PF.shl_eq, Nat.one_mul]
  exact Nat.testBit_two_pow_sub_one n i

theorem tb_clr (X lo c : ℕ) :
    (Nat.sub X (Nat.land X (Nat.sub (Nat.shiftLeft 1 lo) 1))).testBit c =
      (X.testBit c && decide (lo ≤ c)) := by
  have e1 : Nat.land X (Nat.sub (Nat.shiftLeft 1 lo) 1) = X % 2 ^ lo := by
    rw [PF.shl_eq, Nat.one_mul]
    exact Nat.and_two_pow_sub_one_eq_mod X lo
  have e2 : Nat.sub X (X % 2 ^ lo) = X / 2 ^ lo * 2 ^ lo := by
    have := Nat.div_add_mod X (2 ^ lo)
    change X - X % 2 ^ lo = _
    rw [Nat.mul_comm]
    omega
  rw [e1, e2, Nat.testBit_mul_two_pow]
  by_cases h : lo ≤ c
  · have e3 : X.testBit c = (X / 2 ^ lo).testBit (c - lo) := by
      have := Nat.testBit_add X (c - lo) lo
      rwa [Nat.sub_add_cancel h] at this
    rw [e3]
    simp [h]
  · simp [h]

theorem tb_sub_pow {K c : ℕ} (hK : K.testBit c = true) (j : ℕ) :
    (Nat.sub K (Nat.shiftLeft 1 c)).testBit j = (K.testBit j && decide (j ≠ c)) := by
  rw [PF.shl_eq, Nat.one_mul]
  have hge := Nat.ge_two_pow_of_testBit hK
  obtain ⟨K', rfl⟩ : ∃ K', K = 2 ^ c + K' := ⟨K - 2 ^ c, by omega⟩
  have e : Nat.sub (2 ^ c + K') (2 ^ c) = K' := by
    change 2 ^ c + K' - 2 ^ c = K'
    omega
  rw [e]
  have hK' : K'.testBit c = false := by
    rw [Nat.testBit_two_pow_add_eq] at hK
    simpa using hK
  rcases Nat.lt_trichotomy j c with hj | rfl | hj
  · rw [Nat.testBit_two_pow_add_gt hj]
    simp [Nat.ne_of_lt hj]
  · simp [hK']
  · have hmod : K' % 2 ^ (c + 1) < 2 ^ c := by
      refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
      rw [Nat.testBit_mod_two_pow]
      rcases Nat.eq_or_lt_of_le hi with rfl | hi'
      · simp [hK']
      · simp [show ¬ i < c + 1 by omega]
    have hdiv : (2 ^ c + K') / 2 ^ (c + 1) = K' / 2 ^ (c + 1) := by
      have e1 := Nat.div_add_mod K' (2 ^ (c + 1))
      have e2 : 2 ^ c + K' = (2 ^ c + K' % 2 ^ (c + 1)) + 2 ^ (c + 1) * (K' / 2 ^ (c + 1)) := by
        omega
      rw [e2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt, Nat.zero_add]
      have hp : 2 ^ (c + 1) = 2 ^ c * 2 := pow_succ 2 c
      omega
    have ej : j = (j - (c + 1)) + (c + 1) := by omega
    rw [ej, Nat.testBit_add, Nat.testBit_add, hdiv]
    simp [show j - (c + 1) + (c + 1) ≠ c by omega]

theorem testBit_of_land_pos {K c : ℕ} (h : 0 < Nat.land K (Nat.shiftLeft 1 c)) :
    K.testBit c = true := by
  by_contra hc
  have e : Nat.land K (Nat.shiftLeft 1 c) = 0 := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [tb_land, tb_one_shl, Nat.zero_testBit]
    by_cases hi : c = i
    · subst hi
      simpa using hc
    · simp [hi]
  omega

theorem mask10 : mask 10 = 1023 := by decide

theorem fld10_of {X i : ℕ} {g : ℕ → ℕ} (hX : PF.Fld 10 X g) (hg : g i < 2 ^ 10) :
    fld(X, Nat.mul 10 i, 1023) = g i := by
  have h := PF.pg_of_fld hX hg
  rw [mask10] at h
  exact h

theorem getD_lt {l : List ℕ} {b : ℕ} (hl : ∀ s ∈ l, s < b) (hb : 0 < b) (i : ℕ) :
    l.getD i 0 < b := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < l.length
  · rw [List.getElem?_eq_getElem hi, Option.getD_some]
    exact hl _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none (by omega), Option.getD_none]
    exact hb

theorem getD_ge {l : List ℕ} {i : ℕ} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem getD_append_lt {l l' : List ℕ} {i : ℕ} (h : i < l.length) :
    (l ++ l').getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_ge {l l' : List ℕ} {i : ℕ} (h : l.length ≤ i) :
    (l ++ l').getD i 0 = l'.getD (i - l.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_map0 {f : ℕ → ℕ} {l : List ℕ} {i : ℕ} :
    (l.map f).getD i 0 = if i < l.length then f (l.getD i 0) else 0 := by
  by_cases h : i < l.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h,
      Option.map_some, Option.getD_some, h, ↓reduceIte]
  · have e : l[i]? = none := List.getElem?_eq_none (by omega)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, e, Option.map_none,
      Option.getD_none, h, ↓reduceIte]

theorem getD_mem {l : List ℕ} {i : ℕ} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem exists_getD {l : List ℕ} {x : ℕ} (hx : x ∈ l) : ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem extK_fld (Pc S : ℕ) : ∀ k, PF.Fld 10 (extK Pc S k)
    (fun j => if j < k then fld(Pc, Nat.mul 10 fld(S, Nat.mul 10 j, 1023), 1023) else 0)
  | 0 => PF.fld_congr (PF.fld_zero 10) fun i => by simp
  | k + 1 => by
    have hv : fld(Pc, Nat.mul 10 fld(S, Nat.mul 10 k, 1023), 1023) < 2 ^ 10 :=
      Nat.and_lt_two_pow _ (by norm_num)
    have h := PF.fld_or (extK_fld Pc S k) (PF.fld_shl k (PF.fld_one hv))
    have e : extK Pc S (k + 1) = extK Pc S k |||
        fld(Pc, Nat.mul 10 fld(S, Nat.mul 10 k, 1023), 1023) <<< (10 * k) := rfl
    rw [e]
    refine PF.fld_congr h fun i => ?_
    rcases Nat.lt_trichotomy i k with hi | rfl | hi
    · simp [hi, Nat.lt_succ_of_lt hi, show ¬ k ≤ i by omega]
    · simp
    · simp [show ¬ i < k by omega, show ¬ i < k + 1 by omega, show k ≤ i by omega,
        show i - k ≠ 0 by omega]

theorem pack_fld {Sl : List ℕ} {S k c Pc : ℕ} (hS : PF.Fld 10 S (fun i => Sl.getD i 0))
    (hk : Sl.length = k) (hc : c < 1024) (hSl : ∀ s ∈ Sl, s < 1024) :
    PF.Fld 10 (Nat.lor c (Nat.lor (Nat.shiftLeft S 10)
        (Nat.shiftLeft (extK Pc S k) (10 * (k + 1)))))
      (fun i => (c :: (Sl ++ Sl.map fun s => fld(Pc, Nat.mul 10 s, 1023))).getD i 0) := by
  have h0 := PF.fld_one (w := 10) (v := c) (by norm_num; omega)
  have h1 := PF.fld_shl 1 hS
  have h2 := PF.fld_shl (k + 1) (extK_fld Pc S k)
  refine PF.fld_congr (PF.fld_or h0 (PF.fld_or h1 h2)) fun i => ?_
  rcases i with _ | j
  · simp
  · rw [List.getD_cons_succ]
    have a1 : ¬ (j + 1 = 0) := by omega
    have a2 : 1 ≤ j + 1 := by omega
    have e1 : j + 1 - 1 = j := by omega
    by_cases hj : j < k
    · have a3 : ¬ (k + 1 ≤ j + 1) := by omega
      rw [getD_append_lt (by omega)]
      simp only [a1, a2, a3, e1, ↓reduceIte, Nat.zero_or, Nat.or_zero]
    · obtain ⟨t, rfl⟩ : ∃ t, j = k + t := ⟨j - k, by omega⟩
      have a3 : k + 1 ≤ k + t + 1 := by omega
      have e2 : k + t + 1 - (k + 1) = t := by omega
      have hSl0 : Sl.getD (k + t) 0 = 0 := getD_ge (by omega)
      rw [getD_append_ge (by omega), hk, Nat.add_sub_cancel_left, getD_map0, hk]
      simp only [a1, a2, a3, e1, e2, hSl0, ↓reduceIte, Nat.zero_or]
      by_cases ht : t < k
      · simp only [ht, ↓reduceIte]
        rw [fld10_of hS (getD_lt hSl (by norm_num) t)]
      · simp only [ht, ↓reduceIte]

variable {AL PR DF DFO : ℕ → ℕ} {m : ℕ}

structure GraphFacts (AL PR : ℕ → ℕ) (m : ℕ) : Prop where
  le : m ≤ 1024
  symm : ∀ i j, adjT AL m i j = true → adjT AL m j i = true
  pr : ∀ i j, adjT AL m i j = true → prT PR i j < m ∧ prT PR i j = prT PR j i
  high : ∀ a < m, ∀ b < m,
    fld(AL a, Nat.add 1024 b, 1) = if adjT AL m a b = true ∧ b < prT PR a b then 1 else 0
  low : ∀ a < m, ∀ b, m ≤ b → b < 1024 → (AL a).testBit b = false

theorem adjT_iff {i j : ℕ} :
    adjT AL m i j = true ↔ i < m ∧ j < m ∧ (AL i).testBit j = true := by
  unfold adjT
  rw [bit_eq]
  by_cases h : (AL i).testBit j = true <;> simp [h, beq_eq]

theorem adjK_low {na : ℕ} {ps : List ℕ} {IL : ℕ → ℕ} {KB a : ℕ}
    (h : adjK na 8 255 ps 24 IL AL PR KB a = true) :
    ∀ b, na ≤ b → b < 1024 → (AL a).testBit b = false := by
  intro b hb hb'
  unfold adjK at h
  simp only [strictB_eq₀, bAnd_eq, Bool.and_eq_true, beq_eq, decide_eq_true_eq] at h
  obtain ⟨-, h2, -⟩ := h
  have e : AL a / 2 ^ na % 2 ^ (1024 - na) = 0 := by
    rw [← fldW_eq']
    exact h2
  have h3 := Nat.testBit_add (AL a) (b - na) na
  rw [Nat.sub_add_cancel hb] at h3
  rw [h3]
  have h4 := Nat.testBit_mod_two_pow (AL a / 2 ^ na) (1024 - na) (b - na)
  rw [e, Nat.zero_testBit] at h4
  simpa [show b - na < 1024 - na by omega] using h4.symm

theorem GraphFacts.of_setting {G : Type*} [Group G] {v : ℕ → G}
    (hs : Setting m v (adjT AL m) (prT PR)) (hm : m ≤ 1024)
    (hhigh : ∀ a < m, ∀ b < m,
      fld(AL a, Nat.add 1024 b, 1) = if adjT AL m a b = true ∧ b < prT PR a b then 1 else 0)
    (hlow : ∀ a < m, ∀ b, m ≤ b → b < 1024 → (AL a).testBit b = false) :
    GraphFacts AL PR m := by
  refine ⟨hm, fun i j h => hs.adj_symm h, fun i j h => ?_, hhigh, hlow⟩
  obtain ⟨h1, h2⟩ := hs.pr_spec i j h
  obtain ⟨h3, h4⟩ := hs.pr_spec j i (hs.adj_symm h)
  refine ⟨h1, hs.inj _ _ h1 h3 ?_⟩
  rw [h2, h4, comm_of_adj hs h]

structure NodeInv (AL : ℕ → ℕ) (m : ℕ) (Sl : List ℕ) (S k M : ℕ) (cand : List ℕ) : Prop where
  pack : PF.Fld 10 S (fun i => Sl.getD i 0)
  len : Sl.length = k
  lt : ∀ s ∈ Sl, s < m
  cand : ∀ c ∈ cand, c < m ∧ ∀ s ∈ Sl, adjT AL m s c = true
  mand : ∀ i, (∀ s ∈ Sl, (AL s).testBit i = true) → M.testBit i = true

theorem kidsK_testBit (M lo c : ℕ) : (kidsK M lo).testBit c =
    (M.testBit c && decide (c < 1024) && M.testBit (1024 + c) && decide (lo ≤ c)) := by
  unfold kidsK
  rw [strictN_eq₀, tb_clr, tb_land, tb_land, tb_low, tb_shr]

theorem kids_bit (hG : GraphFacts AL PR m) {Sl cand : List ℕ} {S k M lo : ℕ}
    (hI : NodeInv AL m Sl S k M cand) {c : ℕ} (hc : c ∈ kids (prT PR) Sl cand lo) :
    (kidsK M lo).testBit c = true := by
  simp only [kids, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨hcc, hlo, hpr⟩ := hc
  obtain ⟨hcm, hadj⟩ := hI.cand c hcc
  have h1 : M.testBit c = true := hI.mand c fun s hs => (adjT_iff.1 (hadj s hs)).2.2
  have h2 : M.testBit (1024 + c) = true := hI.mand _ fun s hs => by
    have hsc := hadj s hs
    have e := hG.high s (hI.lt s hs) c hcm
    rw [(hG.pr s c hsc).2, if_pos ⟨hsc, hpr s hs⟩, bit_eq] at e
    split_ifs at e with hb
    exact hb
  have h3 : c < 1024 := by
    have := hG.le
    omega
  rw [kidsK_testBit]
  simp [h1, h2, h3, hlo]

theorem childK_eq (S k M c : ℕ) (f : ℕ → ℕ → ℕ → ℕ) :
    childK AL PR S k M c f = f (Nat.lor c (Nat.lor (Nat.shiftLeft S 10)
      (Nat.shiftLeft (extK (PR c) S k) (10 * (k + 1))))) (2 * k + 1)
      (andK AL (extK (PR c) S k) k (Nat.land M (AL c))) := by
  unfold childK
  simp only [strictN_eq₀]
  rfl

theorem andK_testBit (X : ℕ) : ∀ (k M0 i : ℕ), (andK AL X k M0).testBit i = true ↔
    M0.testBit i = true ∧ ∀ j < k, (AL fld(X, Nat.mul 10 j, 1023)).testBit i = true
  | 0, M0, i => by
    have e : andK AL X 0 M0 = M0 := rfl
    simp [e]
  | k + 1, M0, i => by
    have e : andK AL X (k + 1) M0 =
        Nat.land (andK AL X k M0) (AL fld(X, Nat.mul 10 k, 1023)) := rfl
    rw [e, tb_land, Bool.and_eq_true, andK_testBit X k M0 i]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h2 j hj
      · exact h3
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun j hj => h2 j (Nat.lt_succ_of_lt hj)⟩, h2 k (Nat.lt_succ_self k)⟩

theorem mem_childS {pr : ℕ → ℕ → ℕ} {Sl : List ℕ} {c x : ℕ} :
    x ∈ childS pr Sl c ↔ x = c ∨ x ∈ Sl ∨ ∃ s ∈ Sl, pr c s = x := by
  simp only [childS, List.mem_cons, List.mem_append, List.mem_map]

theorem length_childS (pr : ℕ → ℕ → ℕ) (Sl : List ℕ) (c : ℕ) :
    (childS pr Sl c).length = 2 * Sl.length + 1 := by
  have := card_childS pr Sl c
  omega

theorem pack_child {Sl : List ℕ} {S k c : ℕ} (hm : m ≤ 1024)
    (hS : PF.Fld 10 S (fun i => Sl.getD i 0)) (hk : Sl.length = k) (hc : c < m)
    (hSl : ∀ s ∈ Sl, s < m) :
    PF.Fld 10 (Nat.lor c (Nat.lor (Nat.shiftLeft S 10)
        (Nat.shiftLeft (extK (PR c) S k) (10 * (k + 1)))))
      (fun i => (childS (prT PR) Sl c).getD i 0) :=
  pack_fld hS hk (by omega) fun s hs => by have := hSl s hs; omega

theorem lt_child (hG : GraphFacts AL PR m) {Sl : List ℕ} {c : ℕ} (hc : c < m)
    (hSl : ∀ s ∈ Sl, s < m) (hadj : ∀ s ∈ Sl, adjT AL m s c = true) :
    ∀ x ∈ childS (prT PR) Sl c, x < m := by
  intro x hx
  rcases mem_childS.1 hx with rfl | hx | ⟨s, hs, rfl⟩
  · exact hc
  · exact hSl x hx
  · exact (hG.pr c s (hG.symm s c (hadj s hs))).1

theorem child_inv (hG : GraphFacts AL PR m) {Sl cand : List ℕ} {S k M lo : ℕ}
    (hI : NodeInv AL m Sl S k M cand) {c : ℕ} (hc : c ∈ kids (prT PR) Sl cand lo) :
    NodeInv AL m (childS (prT PR) Sl c) (Nat.lor c (Nat.lor (Nat.shiftLeft S 10)
        (Nat.shiftLeft (extK (PR c) S k) (10 * (k + 1))))) (2 * k + 1)
      (andK AL (extK (PR c) S k) k (Nat.land M (AL c)))
      (childCand (adjT AL m) (prT PR) Sl cand c) := by
  have hcc : c ∈ cand := (List.mem_filter.1 hc).1
  obtain ⟨hcm, hadj⟩ := hI.cand c hcc
  have hX := extK_fld (PR c) S k
  refine ⟨pack_child hG.le hI.pack hI.len hcm hI.lt, by rw [length_childS, hI.len],
    lt_child hG hcm hI.lt hadj, fun d hd => ?_, fun i hi => ?_⟩
  · simp only [childCand, List.mem_filter, Bool.and_eq_true, List.all_eq_true] at hd
    obtain ⟨hdc, hcd, hpd⟩ := hd
    obtain ⟨hdm, hsd⟩ := hI.cand d hdc
    refine ⟨hdm, fun x hx => ?_⟩
    rcases mem_childS.1 hx with rfl | hx | ⟨s, hs, rfl⟩
    · exact hcd
    · exact hsd x hx
    · exact hpd s hs
  · rw [andK_testBit, tb_land, Bool.and_eq_true]
    refine ⟨⟨hI.mand i fun s hs => hi s (mem_childS.2 (Or.inr (Or.inl hs))),
      hi c (mem_childS.2 (Or.inl rfl))⟩, fun j hj => ?_⟩
    have hj' : j < Sl.length := by rw [hI.len]; exact hj
    have hg : (if j < k then fld(PR c, Nat.mul 10 fld(S, Nat.mul 10 j, 1023), 1023) else 0) <
        2 ^ 10 := by
      rw [if_pos hj]
      exact Nat.and_lt_two_pow _ (by norm_num)
    have e := fld10_of hX hg
    rw [if_pos hj, fld10_of hI.pack (getD_lt (fun s hs => by
      have := hI.lt s hs; have := hG.le; omega) (by norm_num) j)] at e
    rw [e]
    exact hi _ (mem_childS.2 (Or.inr (Or.inr ⟨_, getD_mem hj', rfl⟩)))

@[expose] noncomputable def loopW (DF : ℕ → ℕ) (base : ℕ) (ch : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun K p => nIf(Nat.beq K (nat_lit 0), p, failK))
    (fun _ loop K p => nIf(Nat.beq K (nat_lit 0), p,
      strictN (dfE DF p) fun e => strictN (Nat.sub e base) fun c =>
      strictN (Nat.shiftLeft (nat_lit 1) c) fun b =>
      nIf(bAnd(Nat.ble base e, bAnd(Nat.blt (nat_lit 0) (Nat.land K b),
          Nat.beq (Nat.land K (Nat.sub b (nat_lit 1))) (nat_lit 0))),
        strictN (ch c p) fun p' => loop (Nat.sub K b) p',
        failK)))

theorem walkK_zero (S k M lo p : ℕ) :
    walkK AL PR DF 0 S k M lo p = nIf(Nat.beq (kidsK M lo) 0, p, failK) := rfl

set_option maxRecDepth 100000 in
theorem walkK_succ (d S k M lo p : ℕ) : walkK AL PR DF (d + 1) S k M lo p =
    loopW DF (Nat.mul (nat_lit 1024) (Nat.sub (nat_lit 5) d))
      (fun c p => childK AL PR S k M c fun S' k' M' =>
        walkK AL PR DF d S' k' M' (Nat.succ c) (Nat.succ p)) (nat_lit 1024) (kidsK M lo) p := by
  have e : walkK AL PR DF (Nat.succ d) S k M lo p =
      strictN (Nat.mul (nat_lit 1024) (Nat.sub (nat_lit 5) d)) fun base =>
      loopW DF base (fun c p => childK AL PR S k M c fun S' k' M' =>
        walkK AL PR DF d S' k' M' (Nat.succ c) (Nat.succ p)) (nat_lit 1024) (kidsK M lo) p := rfl
  rw [e, strictN_eq₀]

theorem loopW_zero {base : ℕ} {ch : ℕ → ℕ → ℕ} (K p : ℕ) :
    loopW DF base ch 0 K p = nIf(Nat.beq K 0, p, failK) := rfl

theorem loopW_succ {base : ℕ} {ch : ℕ → ℕ → ℕ} (n K p : ℕ) : loopW DF base ch (n + 1) K p =
    if K = 0 then p else
      if bAnd(Nat.ble base (dfE DF p), bAnd(Nat.blt 0
          (Nat.land K (Nat.shiftLeft 1 (Nat.sub (dfE DF p) base))),
          Nat.beq (Nat.land K (Nat.sub (Nat.shiftLeft 1 (Nat.sub (dfE DF p) base)) 1)) 0)) = true
      then loopW DF base ch n (Nat.sub K (Nat.shiftLeft 1 (Nat.sub (dfE DF p) base)))
        (ch (Nat.sub (dfE DF p) base) p)
      else failK := by
  have e : loopW DF base ch (n + 1) K p = nIf(Nat.beq K (nat_lit 0), p,
      strictN (dfE DF p) fun e => strictN (Nat.sub e base) fun c =>
      strictN (Nat.shiftLeft (nat_lit 1) c) fun b =>
      nIf(bAnd(Nat.ble base e, bAnd(Nat.blt (nat_lit 0) (Nat.land K b),
          Nat.beq (Nat.land K (Nat.sub b (nat_lit 1))) (nat_lit 0))),
        strictN (ch c p) fun p' => loopW DF base ch n (Nat.sub K b) p',
        failK)) := rfl
  rw [e]
  simp only [strictN_eq₀, nIf_eq, beq_eq, decide_eq_true_eq]

theorem loopW_sound {base : ℕ} {ch : ℕ → ℕ → ℕ} {G : ℕ → Prop}
    (hch : ∀ c p, ch c p < failK → p + 1 ≤ ch c p ∧ G c) :
    ∀ n K p, loopW DF base ch n K p < failK →
      p ≤ loopW DF base ch n K p ∧ ∀ c, K.testBit c = true → G c := by
  intro n
  induction n with
  | zero =>
    intro K p h
    rw [loopW_zero, nIf_eq] at h ⊢
    split_ifs at h ⊢ with hK
    · rw [beq_eq, decide_eq_true_eq] at hK
      subst hK
      exact ⟨le_refl _, fun c hc => by simp at hc⟩
    · exact absurd h (lt_irrefl _)
  | succ n ih =>
    intro K p h
    rw [loopW_succ] at h ⊢
    split_ifs at h ⊢ with hK hc
    · subst hK
      exact ⟨le_refl _, fun c hc => by simp at hc⟩
    · obtain ⟨h1, h2⟩ := ih _ _ h
      have h3 := hch _ _ (lt_of_le_of_lt h1 h)
      simp only [bAnd_eq, Bool.and_eq_true, blt_eq, decide_eq_true_eq] at hc
      have hb := testBit_of_land_pos hc.2.1
      refine ⟨by omega, fun c' hc' => ?_⟩
      by_cases e : c' = Nat.sub (dfE DF p) base
      · rw [e]
        exact h3.2
      · refine h2 c' ?_
        rw [tb_sub_pow hb, hc', Bool.true_and, decide_eq_true_eq]
        exact e
    · exact absurd h (lt_irrefl _)

theorem walk_mono : ∀ d S k M lo p, walkK AL PR DF d S k M lo p < failK →
    p ≤ walkK AL PR DF d S k M lo p := by
  intro d
  induction d with
  | zero =>
    intro S k M lo p h
    rw [walkK_zero, nIf_eq] at h ⊢
    split_ifs at h ⊢
    · exact le_refl _
    · exact absurd h (lt_irrefl _)
  | succ d ih =>
    intro S k M lo p h
    rw [walkK_succ] at h ⊢
    refine (loopW_sound (G := fun _ => True) (fun c q hq => ⟨?_, trivial⟩) _ _ _ h).1
    rw [childK_eq] at hq ⊢
    exact ih _ _ _ _ _ hq

theorem dfs_succ_of {adj : ℕ → ℕ → Bool} {pr : ℕ → ℕ → ℕ} {d : ℕ} {S cand : List ℕ} {lo : ℕ}
    (h : ∀ c ∈ kids pr S cand lo,
      dfs adj pr d (childS pr S c) (childCand adj pr S cand c) (c + 1) = true) :
    dfs adj pr (d + 1) S cand lo = true := by
  simp only [dfs, List.all_eq_true]
  exact h

theorem walk_sound (hG : GraphFacts AL PR m) : ∀ d (Sl : List ℕ) (S k M lo : ℕ)
    (cand : List ℕ) (p : ℕ), NodeInv AL m Sl S k M cand →
    walkK AL PR DF d S k M lo p < failK → dfs (adjT AL m) (prT PR) d Sl cand lo = true := by
  intro d
  induction d with
  | zero =>
    intro Sl S k M lo cand p hI h
    rw [walkK_zero, nIf_eq] at h
    split_ifs at h with hK
    · rw [beq_eq, decide_eq_true_eq] at hK
      simp only [dfs, List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
      intro c hc
      have := kids_bit hG hI hc
      rw [hK] at this
      simp at this
    · exact absurd h (lt_irrefl _)
  | succ d ih =>
    intro Sl S k M lo cand p hI h
    rw [walkK_succ] at h
    have hl := (loopW_sound (G := fun c => c ∈ kids (prT PR) Sl cand lo →
        dfs (adjT AL m) (prT PR) d (childS (prT PR) Sl c)
          (childCand (adjT AL m) (prT PR) Sl cand c) (c + 1) = true)
      (fun c q hq => ⟨by
        rw [childK_eq] at hq ⊢
        exact walk_mono _ _ _ _ _ _ hq, fun hc => by
        rw [childK_eq] at hq
        exact ih _ _ _ _ _ _ _ (child_inv hG hI hc) hq⟩) _ _ _ h).2
    exact dfs_succ_of fun c hc => hl c (kids_bit hG hI hc) hc

@[expose] noncomputable def rootR (DF DFO : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun j acc => strictN (dfE DF (DFO j)) fun e =>
    Nat.lor acc (nIf(bAnd(Nat.ble (nat_lit 1024) e, Nat.blt e (nat_lit 2048)),
      Nat.shiftLeft (nat_lit 1) (Nat.sub e (nat_lit 1024)),
      Nat.shiftLeft (nat_lit 1) (nat_lit 2048)))) n

theorem rootK_eq (z n : ℕ) :
    rootK AL DF DFO z n = Nat.beq (kidsK (AL z) 0) (rootR DF DFO n) := rfl

theorem rootR_bit {c : ℕ} (hc : c < 1024) : ∀ n, (rootR DF DFO n).testBit c = true →
    ∃ j < n, dfE DF (DFO j) = c + 1024
  | 0, h => by
    have e : rootR DF DFO 0 = 0 := rfl
    simp [e] at h
  | n + 1, h => by
    have e : rootR DF DFO (n + 1) = strictN (dfE DF (DFO n)) fun e =>
        Nat.lor (rootR DF DFO n) (nIf(bAnd(Nat.ble 1024 e, Nat.blt e 2048),
          Nat.shiftLeft 1 (Nat.sub e 1024), Nat.shiftLeft 1 2048)) := rfl
    rw [e, strictN_eq₀, tb_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨j, hj, hje⟩ := rootR_bit hc n h
      exact ⟨j, Nat.lt_succ_of_lt hj, hje⟩
    · rw [nIf_eq] at h
      split_ifs at h with hb
      · rw [tb_one_shl, decide_eq_true_eq] at h
        simp only [bAnd_eq, Bool.and_eq_true, ble_eq, blt_eq, decide_eq_true_eq] at hb
        refine ⟨n, Nat.lt_succ_self n, ?_⟩
        change dfE DF (DFO n) - 1024 = c at h
        omega
      · rw [tb_one_shl, decide_eq_true_eq] at h
        omega

theorem subK_lt {z j : ℕ} (h : subK AL PR DF DFO z j = true) :
    childK AL PR z 1 (AL z) (dfE DF (DFO j) - 1024) (fun S k M =>
      walkK AL PR DF 4 S k M (dfE DF (DFO j) - 1024 + 1) (DFO j + 1)) < failK := by
  unfold subK at h
  simp only [strictB_eq₀, bAnd_eq, Bool.and_eq_true, blt_eq, beq_eq, decide_eq_true_eq] at h
  obtain ⟨hq, he⟩ := h
  rw [← he] at hq
  exact hq

theorem root_inv (hG : GraphFacts AL PR m) {z : ℕ} (hz : z < m) :
    NodeInv AL m [z] z 1 (AL z) ((List.range m).filter fun c => adjT AL m c z) := by
  have hz' : z < 2 ^ 10 := by
    have := hG.le
    norm_num
    omega
  refine ⟨PF.fld_congr (PF.fld_one hz') fun i => ?_, rfl, by simpa using hz, fun c hc => ?_,
    fun i hi => hi z (List.mem_singleton_self z)⟩
  · rcases i with _ | i <;> simp
  · simp only [List.mem_filter, List.mem_range] at hc
    refine ⟨hc.1, fun s hs => ?_⟩
    rw [List.mem_singleton] at hs
    subst hs
    exact hG.symm _ _ hc.2

theorem dfs_of_replay (hG : GraphFacts AL PR m) {z n0 : ℕ} (hz : z < m)
    (hroot : rootK AL DF DFO z n0 = true) (hsub : ∀ j < n0, subK AL PR DF DFO z j = true) :
    dfs (adjT AL m) (prT PR) 5 [z] ((List.range m).filter fun c => adjT AL m c z) 0 = true := by
  have hI := root_inv hG hz
  rw [rootK_eq, beq_eq, decide_eq_true_eq] at hroot
  refine dfs_succ_of (d := 4) fun c hc => ?_
  have hbit := kids_bit hG hI hc
  have hcm : c < m := (hI.cand c (List.mem_filter.1 hc).1).1
  have hc' : c < 1024 := by
    have := hG.le
    omega
  rw [hroot] at hbit
  obtain ⟨j, hj, hje⟩ := rootR_bit hc' n0 hbit
  have hs := subK_lt (hsub j hj)
  rw [hje, Nat.add_sub_cancel, childK_eq] at hs
  exact walk_sound hG 4 _ _ _ _ _ _ _ (child_inv hG hI hc) hs

@[expose] def ExtOK (adj : ℕ → ℕ → Bool) (pr : ℕ → ℕ → ℕ) : List ℕ → List ℕ → Prop
  | _, [] => True
  | S, c :: cs => c ∉ S ∧ (∀ s ∈ S, adj c s = true) ∧ ExtOK adj pr (childS pr S c) cs

structure BInv (AL : ℕ → ℕ) (m : ℕ) (Sl : List ℕ) (S k SB AA : ℕ) : Prop where
  pack : PF.Fld 10 S (fun i => Sl.getD i 0)
  len : Sl.length = k
  lt : ∀ s ∈ Sl, s < m
  ne : Sl ≠ []
  sb : ∀ x ∈ Sl, SB.testBit x = true
  aa : ∀ c, AA.testBit c = true → c < 1024 ∧ ∀ s ∈ Sl, (AL s).testBit c = true

theorem bitsK_testBit (S : ℕ) : ∀ (k x : ℕ), (∃ i < k, fld(S, Nat.mul 10 i, 1023) = x) →
    (bitsK S k).testBit x = true
  | 0, x, ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)
  | k + 1, x, ⟨i, hi, hix⟩ => by
    have e : bitsK S (k + 1) =
        Nat.lor (bitsK S k) (Nat.shiftLeft 1 fld(S, Nat.mul 10 k, 1023)) := rfl
    rw [e, tb_lor, Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact Or.inl (bitsK_testBit S k x ⟨i, hi, hix⟩)
    · right
      rw [tb_one_shl, decide_eq_true_eq]
      exact hix

theorem fld_span {Sl : List ℕ} {S : ℕ} (hm : m ≤ 1024) (hS : PF.Fld 10 S (fun i => Sl.getD i 0))
    (hSl : ∀ s ∈ Sl, s < m) (i : ℕ) : fld(S, Nat.mul 10 i, 1023) = Sl.getD i 0 :=
  fld10_of hS (getD_lt (fun s hs => by have := hSl s hs; omega) (by norm_num) i)

theorem basisK_sound (hG : GraphFacts AL PR m) : ∀ (bs Sl : List ℕ) (S k SB AA : ℕ)
    (f : ℕ → ℕ → Bool), BInv AL m Sl S k SB AA → basisK AL PR bs S k SB AA f = true →
    ExtOK (adjT AL m) (prT PR) Sl bs ∧ ∃ S2 k2, PF.Fld 10 S2
      (fun i => (bs.foldl (childS (prT PR)) Sl).getD i 0) ∧
      (bs.foldl (childS (prT PR)) Sl).length = k2 ∧
      (∀ s ∈ bs.foldl (childS (prT PR)) Sl, s < m) ∧ f S2 k2 = true
  | [], Sl, S, k, SB, AA, f, hI, h => ⟨trivial, S, k, hI.pack, hI.len, hI.lt, h⟩
  | c :: bs, Sl, S, k, SB, AA, f, hI, h => by
    have e : basisK AL PR (c :: bs) S k SB AA f = bAnd(Nat.beq fld(SB, c, 1) 0,
        bAnd(Nat.beq fld(AA, c, 1) 1,
        strictB (PR c) fun Pc => strictB (extK Pc S k) fun X =>
        strictB (Nat.lor c (Nat.lor (Nat.shiftLeft S 10)
          (Nat.shiftLeft X (Nat.mul 10 (Nat.succ k))))) fun S' =>
        strictB (Nat.succ (Nat.mul 2 k)) fun k' =>
        strictB (bitsK S' k') fun SB' =>
        strictB (andK AL S' k' (Nat.sub (Nat.shiftLeft 1 1024) 1))
          fun AA' => basisK AL PR bs S' k' SB' AA' f)) := rfl
    rw [e] at h
    simp only [strictB_eq₀, bAnd_eq, Bool.and_eq_true, beq_eq, decide_eq_true_eq] at h
    obtain ⟨hsb, haa, hrest⟩ := h
    have hcS : c ∉ Sl := fun hc => by
      rw [bit_eq, if_pos (hI.sb c hc)] at hsb
      exact absurd hsb (by decide)
    have hAA : AA.testBit c = true := by
      rw [bit_eq] at haa
      by_contra hne
      rw [if_neg hne] at haa
      exact absurd haa (by decide)
    obtain ⟨hc1024, hrow⟩ := hI.aa c hAA
    obtain ⟨s0, hs0⟩ := List.exists_mem_of_ne_nil Sl hI.ne
    have hcm : c < m := by
      by_contra hcm
      have := hG.low s0 (hI.lt s0 hs0) c (by omega) hc1024
      rw [hrow s0 hs0] at this
      exact absurd this (by decide)
    have hadj : ∀ s ∈ Sl, adjT AL m s c = true := fun s hs =>
      adjT_iff.2 ⟨hI.lt s hs, hcm, hrow s hs⟩
    set S' := Nat.lor c (Nat.lor (Nat.shiftLeft S 10)
      (Nat.shiftLeft (extK (PR c) S k) (10 * (k + 1)))) with hS'
    have hpack : PF.Fld 10 S' (fun i => (childS (prT PR) Sl c).getD i 0) :=
      pack_child hG.le hI.pack hI.len hcm hI.lt
    have hlt' := lt_child hG hcm hI.lt hadj
    have hlen : (childS (prT PR) Sl c).length = 2 * k + 1 := by rw [length_childS, hI.len]
    have hI' : BInv AL m (childS (prT PR) Sl c) S' (2 * k + 1) (bitsK S' (2 * k + 1))
        (andK AL S' (2 * k + 1) (Nat.sub (Nat.shiftLeft 1 1024) 1)) := by
      refine ⟨hpack, hlen, hlt', by simp [childS], fun x hx => ?_, fun c' hc' => ?_⟩
      · obtain ⟨i, hi, rfl⟩ := exists_getD hx
        exact bitsK_testBit S' _ _ ⟨i, by omega, fld_span hG.le hpack hlt' i⟩
      · rw [andK_testBit, tb_low, decide_eq_true_eq] at hc'
        refine ⟨hc'.1, fun s hs => ?_⟩
        obtain ⟨i, hi, rfl⟩ := exists_getD hs
        have := hc'.2 i (by omega)
        rwa [fld_span hG.le hpack hlt' i] at this
    obtain ⟨h1, h2⟩ := basisK_sound hG bs _ S' (2 * k + 1) _ _ f hI' hrest
    exact ⟨⟨hcS, fun s hs => hG.symm _ _ (hadj s hs), h1⟩, h2⟩

theorem wmK_testBit (S W w : ℕ) : ∀ k, W.testBit w = true →
    (∀ i < k, (AL fld(S, Nat.mul 10 i, 1023)).testBit w = true ∨
      fld(S, Nat.mul 10 i, 1023) = w) → (wmK AL S k W).testBit w = true
  | 0, hW, _ => hW
  | k + 1, hW, h => by
    have e : wmK AL S (k + 1) W = Nat.land (wmK AL S k W)
        (Nat.lor (AL fld(S, Nat.mul 10 k, 1023)) (Nat.shiftLeft 1 fld(S, Nat.mul 10 k, 1023))) := by
      have e' : wmK AL S (k + 1) W = strictN fld(S, Nat.mul 10 k, 1023) fun s =>
          Nat.land (wmK AL S k W) (Nat.lor (AL s) (Nat.shiftLeft 1 s)) := rfl
      rw [e', strictN_eq₀]
    rw [e, tb_land, tb_lor, tb_one_shl, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨wmK_testBit S W w k hW fun i hi => h i (Nat.lt_succ_of_lt hi), h k (Nat.lt_succ_self k)⟩

@[expose] noncomputable def ebR (AL PR : ℕ → ℕ) (z zm : ℕ) : List (List ℕ) → ℕ → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun W => Nat.beq (Nat.land W zm) W)
    (fun bs _ ih W => bAnd(Nat.beq (lenK bs) (nat_lit 5),
      basisK AL PR bs z (nat_lit 1) (Nat.shiftLeft (nat_lit 1) z)
        (Nat.land (AL z) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1024)) (nat_lit 1)))
        fun S k => strictB (wmK AL S k W) ih))

theorem ebK_eq (z : ℕ) (EB : List (List ℕ)) (ZW : List ℕ) : ebK AL PR m z EB ZW =
    bAnd(Nat.beq (lenK EB) 3, bAnd(Nat.beq (lenK ZW) 3,
      strictB (maskL ZW) fun zm => ebR AL PR z zm EB (Nat.sub (Nat.shiftLeft 1 m) 1))) := rfl

theorem root_binv (hG : GraphFacts AL PR m) {z : ℕ} (hz : z < m) :
    BInv AL m [z] z 1 (Nat.shiftLeft 1 z)
      (Nat.land (AL z) (Nat.sub (Nat.shiftLeft 1 1024) 1)) := by
  have hz' : z < 2 ^ 10 := by
    have := hG.le
    norm_num
    omega
  refine ⟨PF.fld_congr (PF.fld_one hz') fun i => ?_, rfl, by simpa using hz, by simp,
    fun x hx => ?_, fun c hc => ?_⟩
  · rcases i with _ | i <;> simp
  · rw [List.mem_singleton] at hx
    subst hx
    rw [tb_one_shl, decide_eq_true_eq]
  · rw [tb_land, tb_low, Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨hc.2, fun s hs => ?_⟩
    rw [List.mem_singleton] at hs
    subst hs
    exact hc.1

theorem ebR_sound (hG : GraphFacts AL PR m) {z zm : ℕ} (hz : z < m) :
    ∀ (EB : List (List ℕ)) (W : ℕ), ebR AL PR z zm EB W = true →
      (∀ bs ∈ EB, bs.length = 5 ∧ ExtOK (adjT AL m) (prT PR) [z] bs) ∧
      ∀ w, W.testBit w = true → (∀ bs ∈ EB, ∀ s ∈ bs.foldl (childS (prT PR)) [z],
        adjT AL m w s = true ∨ w = s) → zm.testBit w = true
  | [], W, h => by
    have e : ebR AL PR z zm [] W = Nat.beq (Nat.land W zm) W := rfl
    rw [e, beq_eq, decide_eq_true_eq] at h
    refine ⟨fun bs hbs => absurd hbs List.not_mem_nil, fun w hw _ => ?_⟩
    rw [← h, tb_land, Bool.and_eq_true] at hw
    exact hw.2
  | bs :: EB, W, h => by
    have e : ebR AL PR z zm (bs :: EB) W = bAnd(Nat.beq (lenK bs) 5,
        basisK AL PR bs z 1 (Nat.shiftLeft 1 z)
          (Nat.land (AL z) (Nat.sub (Nat.shiftLeft 1 1024) 1))
          fun S k => strictB (wmK AL S k W) (ebR AL PR z zm EB)) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true, beq_eq, decide_eq_true_eq, lenK_eq] at h
    obtain ⟨hlen, hb⟩ := h
    obtain ⟨hext, S2, k2, hpack, hk2, hlt, hf⟩ := basisK_sound hG bs [z] z 1 _ _ _ (root_binv hG hz) hb
    rw [strictB_eq₀] at hf
    obtain ⟨ih1, ih2⟩ := ebR_sound hG hz EB _ hf
    refine ⟨fun bs' hbs' => ?_, fun w hw hall => ?_⟩
    · rcases List.mem_cons.1 hbs' with rfl | hbs'
      · exact ⟨hlen, hext⟩
      · exact ih1 bs' hbs'
    · refine ih2 w (wmK_testBit S2 W w k2 hw fun i hi => ?_)
        fun bs' hbs' => hall bs' (List.mem_cons_of_mem _ hbs')
      rw [fld_span hG.le hpack hlt i]
      have hi' : i < (bs.foldl (childS (prT PR)) [z]).length := by omega
      rcases hall bs List.mem_cons_self _ (getD_mem hi') with ha | ha
      · exact Or.inl (adjT_iff.1 (hG.symm _ _ ha)).2.2
      · exact Or.inr ha.symm

theorem ebK_sound (hG : GraphFacts AL PR m) {z : ℕ} (hz : z < m) {EB : List (List ℕ)}
    {ZW : List ℕ} (h : ebK AL PR m z EB ZW = true) :
    EB.length = 3 ∧ ZW.length = 3 ∧
      (∀ bs ∈ EB, bs.length = 5 ∧ ExtOK (adjT AL m) (prT PR) [z] bs) ∧
      ∀ w < m, (∀ bs ∈ EB, ∀ s ∈ bs.foldl (childS (prT PR)) [z],
        adjT AL m w s = true ∨ w = s) → w ∈ ZW := by
  rw [ebK_eq, bAnd_eq, bAnd_eq, strictB_eq₀] at h
  simp only [Bool.and_eq_true, beq_eq, decide_eq_true_eq, lenK_eq] at h
  obtain ⟨h1, h2⟩ := ebR_sound hG hz EB _ h.2.2
  refine ⟨h.1, h.2.1, h1, fun w hw hall => ?_⟩
  have := h2 w (by rw [tb_low, decide_eq_true_eq]; exact hw) hall
  rw [maskL_testBit, decide_eq_true_eq] at this
  exact this

end CFSG.KS.HNT0

end
