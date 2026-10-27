module

public import CFSG.Monster.B.TwoA.Sp8.P0UCoord
public import CFSG.Monster.B.TwoA.Sp8.P0RankInputs

set_option linter.unusedSectionVars false

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.P0Col

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Sp8.WordRel
open MonsterB.P0Rank

theorem colsAct_prod {G : Type*} [Group G] (F : ℕ → G) (hF : ∀ a b, F (a ^^^ b) = F a * F b)
    (cs : List ℕ) (x : ℕ) :
    F (colsAct cs x) =
      ((List.range cs.length).map fun j => if x.testBit j then F (cs.getD j 0) else 1).prod := by
  have h0 : F 0 = 1 := by
    have h := hF 0 0
    rw [Nat.zero_xor] at h
    exact mul_left_cancel (a := F 0) (by rw [mul_one]; exact h.symm)
  induction cs generalizing x with
  | nil => simp [colsAct.eq_1, h0]
  | cons c cs ih =>
    rw [colsAct.eq_2, hF, ih, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.prod_cons, List.map_map]
    congr 1
    · rw [Nat.testBit_zero]
      by_cases hx : x % 2 = 1 <;> simp [hx, h0]
    · congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply, Nat.testBit_succ, List.getD_cons_succ]

@[expose] def cIn (s j : ℕ) (l : List ℕ) (a : ℕ) : ℕ :=
  l.foldl (fun acc i => if j < i && s.testBit i then acc ^^^ (lCommN.getD i []).getD j 0
    else acc) a

theorem cIn_acc (s j : ℕ) (l : List ℕ) (a : ℕ) : cIn s j l a = a ^^^ cIn s j l 0 := by
  induction l generalizing a with
  | nil => simp [cIn]
  | cons i l ih =>
    simp only [cIn, List.foldl_cons] at ih ⊢
    rw [ih, ih (if (j < i && s.testBit i) = true then 0 ^^^ (lCommN.getD i []).getD j 0 else 0)]
    split_ifs <;> simp [Nat.xor_assoc]

theorem cIn_le (s j : ℕ) (l : List ℕ) (hl : ∀ i ∈ l, i ≤ j) (a : ℕ) : cIn s j l a = a := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    simp only [cIn, List.foldl_cons] at ih ⊢
    have hi : ¬ j < i := Nat.not_lt.2 (hl i (List.mem_cons_self ..))
    rw [if_neg (by simp [hi])]
    exact ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) a

theorem cIn_congr {s s' j : ℕ} (l : List ℕ) (h : ∀ i ∈ l, j < i → s.testBit i = s'.testBit i)
    (a : ℕ) : cIn s j l a = cIn s' j l a := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    simp only [cIn, List.foldl_cons] at ih ⊢
    have hc : (j < i && s.testBit i) = (j < i && s'.testBit i) := by
      by_cases hji : j < i
      · rw [h i (List.mem_cons_self ..) hji]
      · simp [hji]
    rw [hc]
    exact ih (fun c hc' => h c (List.mem_cons_of_mem _ hc')) _

theorem cIn_append_single (s j n : ℕ) (l : List ℕ) (a : ℕ) :
    cIn s j (l ++ [n]) a = if j < n && s.testBit n then cIn s j l a ^^^ (lCommN.getD n []).getD j 0
      else cIn s j l a := by
  simp [cIn, List.foldl_append]

@[expose] def gPre (s s' n : ℕ) : ℕ :=
  (List.range n).foldl (fun acc j => if s'.testBit j then cIn s j (List.range 16) acc else acc) 0

theorem gPre_succ (s s' n : ℕ) :
    gPre s s' (n + 1) =
      if s'.testBit n then cIn s n (List.range 16) (gPre s s' n) else gPre s s' n := by
  simp [gPre, List.range_succ, List.foldl_append]

theorem gam_eq_gPre (s s' : ℕ) : gam p0Data.beta s s' = gPre s s' 16 := rfl

@[expose] def pcL (x : ℕ × ℕ) : Dfull := lD x.1 * tD x.2

@[expose] def pcElt (g : (ℕ × ℕ) × ℕ) : Dfull := pcL g.1 * uE g.2

theorem pc_comm_tD {a : Dfull} (ha : a ∈ Lgrp) (τ : ℕ) : a * tD τ = tD τ * a := by
  have hmem : (⟨tD τ, T9_le_Lgrp (tD_mem_T9 τ)⟩ : Lgrp) ∈ T9.subgroupOf Lgrp :=
    Subgroup.mem_subgroupOf.2 (tD_mem_T9 τ)
  have h := Subgroup.mem_center_iff.1 (T9_le_center_Lgrp hmem) ⟨a, ha⟩
  exact congrArg Subtype.val h

theorem pc_tD_zero : tD 0 = (1 : Dfull) := by
  have h := tD_xor 0 0
  rw [Nat.zero_xor] at h
  exact mul_left_cancel (a := tD 0) (by rw [mul_one]; exact h.symm)

theorem pc_lD_zero : lD 0 = (1 : Dfull) := by
  rw [lD_eq_prod]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
  simp

theorem pc_tD_comm (a b : ℕ) : tD a * tD b = tD b * tD a := by
  rw [← tD_xor, ← tD_xor, Nat.xor_comm]

theorem pcL_mem (x : ℕ × ℕ) : pcL x ∈ Lgrp :=
  Lgrp.mul_mem (lD_mem_Lgrp _) (T9_le_Lgrp (tD_mem_T9 _))

theorem pc_lD_congr {a b : ℕ} (h : ∀ j < 16, a.testBit j = b.testBit j) : lD a = lD b := by
  rw [lD_eq_prod a, lD_eq_prod b]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [h j (List.mem_range.1 hj)]

@[expose] def lp (s n : ℕ) : Dfull :=
  ((List.range n).map fun j => if s.testBit j then lD (2 ^ j) else 1).prod

theorem lp_succ (s n : ℕ) : lp s (n + 1) = lp s n * (if s.testBit n then lD (2 ^ n) else 1) := by
  simp [lp, List.range_succ]

theorem lp_congr {s s' n : ℕ} (h : ∀ i < n, s.testBit i = s'.testBit i) : lp s n = lp s' n := by
  unfold lp
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.1 hi)]

theorem lp_mem (s n : ℕ) : lp s n ∈ Lgrp := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
  split_ifs
  · exact lD_mem_Lgrp _
  · exact Lgrp.one_mem

theorem lp_sixteen (s : ℕ) : lp s 16 = lD s := (lD_eq_prod s).symm

theorem lp_mul_gen (s j : ℕ) (hj : j < 16) : ∀ n, j < n → n ≤ 16 →
    lp s n * lD (2 ^ j) = lp (s ^^^ 2 ^ j) n * tD (cIn s j (List.range n) 0) := by
  intro n hjn hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge j n with hlt | hge
    · have ih' := ih hlt (by omega)
      have hn16 : n < 16 := by omega
      have hjn2 : j ≠ n := by omega
      have hbit : (s ^^^ 2 ^ j).testBit n = s.testBit n := by
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        simp [hjn2]
      rw [lp_succ, lp_succ, List.range_succ, cIn_append_single, hbit]
      by_cases hs : s.testBit n
      · have hd : (decide (j < n) && s.testBit n) = true := by simp [hlt, hs]
        rw [if_pos hs, if_pos hd, tD_xor]
        have hc := pc_comm_tD (lD_mem_Lgrp (2 ^ n)) (cIn s j (List.range n) 0)
        calc lp s n * lD (2 ^ n) * lD (2 ^ j)
            = lp s n * (lD (2 ^ n) * lD (2 ^ j)) := by group
          _ = lp s n * (lD (2 ^ j) * lD (2 ^ n) * tD ((lCommN.getD n []).getD j 0)) := by
              rw [lD_mul_lD hn16 hj]
          _ = (lp s n * lD (2 ^ j)) * lD (2 ^ n) * tD ((lCommN.getD n []).getD j 0) := by group
          _ = lp (s ^^^ 2 ^ j) n * (tD (cIn s j (List.range n) 0) * lD (2 ^ n)) *
                tD ((lCommN.getD n []).getD j 0) := by rw [ih']; group
          _ = _ := by rw [← hc]; group
      · have hd : (decide (j < n) && s.testBit n) = false := by simp [hs]
        rw [if_neg hs, if_neg (by simp [hd]), mul_one, mul_one, ih']
    · have hjn' : n = j := by omega
      subst hjn'
      have hlow : lp (s ^^^ 2 ^ n) n = lp s n := lp_congr fun i hi => by
        have hni : n ≠ i := by omega
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        simp [hni]
      have hc0 : cIn s n (List.range (n + 1)) 0 = 0 :=
        cIn_le s n _ (fun i hi => Nat.lt_succ_iff.1 (List.mem_range.1 hi)) 0
      have hbit : (s ^^^ 2 ^ n).testBit n = !s.testBit n := by
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        simp
      rw [lp_succ, lp_succ, hlow, hc0, pc_tD_zero, mul_one, hbit]
      by_cases hs : s.testBit n
      · rw [if_pos hs, mul_assoc, lD_mul_self hn]
        simp [hs]
      · simp [hs]

theorem lD_mul_lp (s s' : ℕ) : ∀ n ≤ 16,
    lD s * lp s' n = lD (s ^^^ s' % 2 ^ n) * tD (gPre s s' n) := by
  intro n hn
  induction n with
  | zero =>
    simp [lp, gPre, pc_tD_zero, Nat.mod_one]
  | succ n ih =>
    have hn16 : n < 16 := by omega
    have ih' := ih (by omega)
    rw [lp_succ, gPre_succ, ← mul_assoc, ih']
    by_cases hs' : s'.testBit n
    · rw [if_pos hs', if_pos hs']
      set x := s ^^^ s' % 2 ^ n with hx
      have hxs : x ^^^ 2 ^ n = s ^^^ s' % 2 ^ (n + 1) := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [hx, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
        rcases lt_trichotomy i n with h | rfl | h
        · have h1 : i < n + 1 := by omega
          have h2 : n ≠ i := by omega
          simp [h, h1, h2]
        · simp [hs']
        · have h1 : ¬ i < n := by omega
          have h2 : ¬ i < n + 1 := by omega
          have h3 : n ≠ i := by omega
          simp [h1, h2, h3]
      have hcx : cIn x n (List.range 16) 0 = cIn s n (List.range 16) 0 :=
        cIn_congr _ (fun i _ hi => by
          have h1 : ¬ i < n := by omega
          simp only [hx, Nat.testBit_xor, Nat.testBit_mod_two_pow]
          simp [h1]) 0
      have hstep := lp_mul_gen x n hn16 16 hn16 le_rfl
      rw [lp_sixteen, lp_sixteen, hxs, hcx] at hstep
      have hc := pc_comm_tD (lD_mem_Lgrp (2 ^ n)) (gPre s s' n)
      rw [cIn_acc, tD_xor]
      calc lD x * tD (gPre s s' n) * lD (2 ^ n)
          = lD x * (lD (2 ^ n) * tD (gPre s s' n)) := by rw [hc]; group
        _ = (lD x * lD (2 ^ n)) * tD (gPre s s' n) := by group
        _ = lD (s ^^^ s' % 2 ^ (n + 1)) * (tD (cIn s n (List.range 16) 0) * tD (gPre s s' n)) := by
            rw [hstep]; group
        _ = _ := by rw [pc_tD_comm]
    · rw [if_neg hs', if_neg hs', mul_one]
      congr 2
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow]
      rcases lt_trichotomy i n with h | rfl | h
      · have h1 : i < n + 1 := by omega
        simp [h, h1]
      · simp [hs']
      · have h1 : ¬ i < n := by omega
        have h2 : ¬ i < n + 1 := by omega
        simp [h1, h2]

theorem pc_lD_mul_lD (s s' : ℕ) : lD s * lD s' = lD (s ^^^ s') * tD (gam p0Data.beta s s') := by
  have h := lD_mul_lp s s' 16 le_rfl
  rw [lp_sixteen] at h
  rw [h, gam_eq_gPre]
  congr 1
  apply pc_lD_congr
  intro j hj
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_mod_two_pow]
  simp [hj]

theorem pcL_lmul (x y : ℕ × ℕ) : pcL (lmul p0Data.beta x y) = pcL x * pcL y := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [pcL, lmul]
  have hc := pc_comm_tD (lD_mem_Lgrp y1) x2
  rw [tD_xor, tD_xor]
  calc lD (x1 ^^^ y1) * (tD x2 * tD y2 * tD (gam p0Data.beta x1 y1))
      = lD (x1 ^^^ y1) * tD (gam p0Data.beta x1 y1) * (tD x2 * tD y2) := by
        rw [← tD_xor x2 y2, pc_tD_comm (x2 ^^^ y2)]; group
    _ = lD x1 * lD y1 * (tD x2 * tD y2) := by rw [pc_lD_mul_lD]
    _ = lD x1 * (tD x2 * lD y1) * tD y2 := by rw [← hc]; group
    _ = _ := by group

private theorem wordX_flatMap_range' (n : ℕ) (f : ℕ → List XLetter) :
    wordX ((List.range n).flatMap f) = ((List.range n).map (fun j => wordX (f j))).prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, wordX_append, ih, List.map_append, List.prod_append,
      List.flatMap_singleton, List.map_singleton, List.prod_singleton]

theorem pc_tD_eq_prod (τ : ℕ) :
    tD τ = ((List.range 9).map fun j => if τ.testBit j then tD (2 ^ j) else 1).prod := by
  change wordX (tWord τ) = _
  rw [tWord, wordX_flatMap_range']
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj9 := List.mem_range.1 hj
  by_cases h : τ.testBit j
  · rw [if_pos h, if_pos h]
    change _ = wordX (tWord (2 ^ j))
    congr 1
    interval_cases j <;> rfl
  · rw [if_neg h, if_neg h]
    rfl

theorem pc_conj_tD {k : ℕ} (hk : k < 10) (τ : ℕ) :
    uD k * tD τ * (uD k)⁻¹ = tD (colsAct (uConjTN.getD k []) τ) := by
  have hlen : (uConjTN.getD k []).length = 9 := by interval_cases k <;> rfl
  rw [colsAct_prod tD tD_xor, hlen, pc_tD_eq_prod τ, ← MulAut.conj_apply, map_list_prod,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj9 := List.mem_range.1 hj
  simp only [Function.comp_apply]
  split_ifs
  · rw [MulAut.conj_apply, uD_mul_tD hk hj9, mul_inv_cancel_right]
  · simp

theorem pcL_foldl_lmul (l : List ℕ) (p : ℕ → Bool) (g : ℕ → ℕ × ℕ) (a : ℕ × ℕ) :
    pcL (l.foldl (fun acc j => if p j then lmul p0Data.beta acc (g j) else acc) a) =
      pcL a * (l.map fun j => if p j then pcL (g j) else 1).prod := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons]
    split_ifs
    · rw [pcL_lmul, mul_assoc]
    · rw [one_mul]

theorem pcL_conjk {k : ℕ} (hk : k < 10) (x : ℕ × ℕ) :
    pcL (conjk p0Data k x) = uD k * pcL x * (uD k)⁻¹ := by
  rw [conjk, pcL_foldl_lmul]
  have h0 : pcL (0, colsAct (p0Data.uConjT.getD k []) x.2) = uD k * tD x.2 * (uD k)⁻¹ := by
    rw [pcL, pc_lD_zero, one_mul, pc_conj_tD hk]
    rfl
  have hl : ((List.range 16).map fun j => if x.1.testBit j then
      pcL ((p0Data.uConjL.getD k []).getD j (0, 0)) else 1).prod = uD k * lD x.1 * (uD k)⁻¹ := by
    rw [lD_eq_prod x.1, ← MulAut.conj_apply, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj16 := List.mem_range.1 hj
    simp only [Function.comp_apply]
    split_ifs
    · rw [MulAut.conj_apply, uD_mul_lD hk hj16, mul_inv_cancel_right]
      rfl
    · simp
  rw [h0, hl, pcL]
  have hc := pc_comm_tD (lD_mem_Lgrp x.1) x.2
  calc uD k * tD x.2 * (uD k)⁻¹ * (uD k * lD x.1 * (uD k)⁻¹)
      = uD k * (tD x.2 * lD x.1) * (uD k)⁻¹ := by group
    _ = _ := by rw [← hc]

private theorem pcL_foldr_conjk (κ : ℕ) (x : ℕ × ℕ) (l : List ℕ) (hl : ∀ k ∈ l, k < 10) :
    pcL (l.foldr (fun k y => if κ.testBit k then conjk p0Data k y else y) x) =
      (l.map fun k => if κ.testBit k then uD k else 1).prod * pcL x *
        ((l.map fun k => if κ.testBit k then uD k else 1).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons k l ih =>
    rw [List.foldr_cons, List.map_cons, List.prod_cons]
    have ih' := ih (fun c hc => hl c (List.mem_cons_of_mem _ hc))
    by_cases h : κ.testBit k
    · rw [if_pos h, if_pos h, pcL_conjk (hl k (List.mem_cons_self ..)), ih']
      group
    · rw [if_neg h, if_neg h, ih']
      group

private theorem wordX_flatMap_uWord' (κ : ℕ) (l : List ℕ) :
    wordX (l.flatMap fun k => if κ.testBit k then uWord k else []) =
      (l.map fun k => if κ.testBit k then uD k else 1).prod := by
  induction l with
  | nil => simp [wordX_nil]
  | cons a l ih =>
    rw [List.flatMap_cons, wordX_append, ih, List.map_cons, List.prod_cons]
    by_cases h : κ.testBit a
    · simp [h, uD]
    · simp [h, wordX_nil]

theorem pc_uE_eq_prod (κ : ℕ) :
    uE κ = ((List.range 10).map fun k => if κ.testBit k then uD k else 1).prod := by
  rw [uE, uProd]
  exact wordX_flatMap_uWord' κ (List.range 10)

theorem pcL_conjkap (κ : ℕ) (x : ℕ × ℕ) :
    pcL (conjkap p0Data κ x) = uE κ * pcL x * (uE κ)⁻¹ := by
  rw [conjkap, pcL_foldr_conjk _ _ _ (fun k hk => List.mem_range.1 hk), ← pc_uE_eq_prod]

private theorem pcL_foldl_conjk (l : List ℕ) (hl : ∀ c ∈ l, c < 10) (X : ℕ × ℕ) :
    pcL (l.foldl (fun x c => conjk p0Data c x) X) =
      (l.reverse.map uD).prod * pcL X * ((l.reverse.map uD).prod)⁻¹ := by
  induction l generalizing X with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)),
      pcL_conjk (hl c (List.mem_cons_self ..)), List.reverse_cons, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton]
    group

theorem moveleftR_spec {k : ℕ} (hk : k < 10) (l : List ℕ) (hl : ∀ c ∈ l, c < 10) :
    (l.reverse.map uD).prod * uD k =
      pcL (moveleftR p0Data k l) * uD k * (l.reverse.map uD).prod := by
  induction l with
  | nil => simp [moveleftR, pcL, pc_lD_zero, pc_tD_zero]
  | cons c rest ih =>
    have hrest : ∀ c ∈ rest, c < 10 := fun c hc => hl c (List.mem_cons_of_mem _ hc)
    have hc : c < 10 := hl c (List.mem_cons_self ..)
    simp only [moveleftR]
    rw [pcL_lmul, pcL_foldl_conjk rest hrest, List.reverse_cons, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton]
    have hX : uD c * uD k = pcL ((p0Data.uComm.getD c []).getD k (0, 0)) * uD k * uD c :=
      uD_mul_uD hc hk
    have ih' := ih hrest
    set R := (rest.reverse.map uD).prod
    calc R * uD c * uD k = R * (uD c * uD k) := by group
      _ = R * (pcL ((p0Data.uComm.getD c []).getD k (0, 0)) * uD k * uD c) := by rw [hX]
      _ = (R * pcL ((p0Data.uComm.getD c []).getD k (0, 0)) * R⁻¹) * (R * uD k) * uD c := by
          group
      _ = (R * pcL ((p0Data.uComm.getD c []).getD k (0, 0)) * R⁻¹) *
            (pcL (moveleftR p0Data k rest) * uD k * R) * uD c := by rw [ih']
      _ = _ := by group

private theorem prod_map_ite_filter (p : ℕ → Bool) (l : List ℕ) :
    (l.map fun c => if p c then uD c else 1).prod = ((l.filter p).map uD).prod := by
  induction l with
  | nil => rfl
  | cons c l ih => by_cases h : p c <;> simp [List.filter_cons, h, ih]

theorem uE_split {k : ℕ} (hk : k < 10) (κ : ℕ) :
    uE κ = (((List.range k).filter κ.testBit).map uD).prod * (if κ.testBit k then uD k else 1) *
      (((List.range 10).filter fun c => k < c && κ.testBit c).map uD).prod := by
  have hr : List.range 10 = List.range k ++ k :: List.range' (k + 1) (9 - k) := by
    interval_cases k <;> decide
  have hQ : (List.range 10).filter (fun c => k < c && κ.testBit c) =
      (List.range' (k + 1) (9 - k)).filter κ.testBit := by
    rw [hr, List.filter_append, List.filter_cons]
    have h1 : (List.range k).filter (fun c => k < c && κ.testBit c) = [] :=
      List.filter_eq_nil_iff.2 fun c hc => by
        have := List.mem_range.1 hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro h
        omega
    have h2 : (List.range' (k + 1) (9 - k)).filter (fun c => k < c && κ.testBit c) =
        (List.range' (k + 1) (9 - k)).filter κ.testBit :=
      List.filter_congr fun c hc => by
        have hkc : k < c := by
          have := List.mem_range'_1.1 hc
          omega
        simp only [hkc, decide_true, Bool.true_and]
    simp [h1, h2]
  rw [pc_uE_eq_prod, hQ, hr, List.map_append, List.prod_append, List.map_cons, List.prod_cons,
    prod_map_ite_filter, prod_map_ite_filter, mul_assoc]

theorem pcElt_rmulU (g : (ℕ × ℕ) × ℕ) {k : ℕ} (hk : k < 10) :
    pcElt (rmulU p0Data g k) = pcElt g * uD k := by
  obtain ⟨x, κ⟩ := g
  simp only [rmulU]
  set P := (List.range k).filter κ.testBit with hP
  set Q := (List.range 10).filter (fun c => k < c && κ.testBit c) with hQ
  have hPl : ∀ c ∈ P.reverse, c < 10 := fun c hc => by
    have := List.mem_range.1 (List.mem_filter.1 (List.mem_reverse.1 hc)).1
    omega
  have hQl : ∀ c ∈ Q.reverse, c < 10 := fun c hc =>
    List.mem_range.1 (List.mem_filter.1 (List.mem_reverse.1 hc)).1
  have hY := moveleftR_spec hk Q.reverse hQl
  rw [List.reverse_reverse] at hY
  have hG := pcL_foldl_conjk P.reverse hPl
  simp only [List.reverse_reverse] at hG
  set Y := moveleftR p0Data k Q.reverse
  set Pp := (P.map uD).prod with hPp
  set Qp := (Q.map uD).prod with hQp
  have hsplit := uE_split hk κ
  rw [← hP, ← hQ] at hsplit
  by_cases hκ : κ.testBit k
  · rw [if_pos hκ]
    have hP' : (List.range k).filter (κ ^^^ 2 ^ k).testBit = P :=
      List.filter_congr fun c hc => by
        have hkc : k ≠ c := by
          have := List.mem_range.1 hc
          omega
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        simp [hkc]
    have hQ' : (List.range 10).filter (fun c => k < c && (κ ^^^ 2 ^ k).testBit c) = Q :=
      List.filter_congr fun c _ => by
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        by_cases hkc : k < c
        · have hkc' : k ≠ c := by omega
          simp [hkc, hkc']
        · simp [hkc]
    have hbit : (κ ^^^ 2 ^ k).testBit k = false := by
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      simp [hκ]
    have hs := uE_split hk (κ ^^^ 2 ^ k)
    rw [hP', hQ', hbit] at hs
    have hsq : pcL (p0Data.uSq.getD k (0, 0)) = uD k * uD k := (uD_mul_self hk).symm
    simp only [pcElt]
    rw [hs, hsplit, if_pos hκ, pcL_lmul, hG, pcL_lmul, pcL_conjk hk, hsq]
    have hre : pcL x * (Pp * uD k * Qp) * uD k = pcL x * Pp * uD k * (Qp * uD k) := by group
    rw [hre, hY]
    simp only [Bool.false_eq_true, if_false]
    rw [← hPp, ← hQp]
    group
  · rw [if_neg hκ]
    have hP' : (List.range k).filter (κ ||| 2 ^ k).testBit = P :=
      List.filter_congr fun c hc => by
        have hkc : k ≠ c := by
          have := List.mem_range.1 hc
          omega
        rw [Nat.testBit_or, Nat.testBit_two_pow]
        simp [hkc]
    have hQ' : (List.range 10).filter (fun c => k < c && (κ ||| 2 ^ k).testBit c) = Q :=
      List.filter_congr fun c _ => by
        rw [Nat.testBit_or, Nat.testBit_two_pow]
        by_cases hkc : k < c
        · have hkc' : k ≠ c := by omega
          simp [hkc, hkc']
        · simp [hkc]
    have hbit : (κ ||| 2 ^ k).testBit k = true := by
      rw [Nat.testBit_or, Nat.testBit_two_pow]
      simp
    have hs := uE_split hk (κ ||| 2 ^ k)
    rw [hP', hQ', hbit, if_pos rfl] at hs
    simp only [pcElt]
    rw [hs, hsplit, if_neg hκ, pcL_lmul, hG]
    have hre : pcL x * (Pp * 1 * Qp) * uD k = pcL x * Pp * (Qp * uD k) := by group
    rw [hre, hY]
    rw [← hPp, ← hQp]
    group

private theorem pcElt_foldl_rmulU (l : List ℕ) (hl : ∀ k ∈ l, k < 10) (g : (ℕ × ℕ) × ℕ) :
    pcElt (l.foldl (rmulU p0Data) g) = pcElt g * (l.map uD).prod := by
  induction l generalizing g with
  | nil => simp
  | cons k l ih =>
    rw [List.foldl_cons, ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)),
      pcElt_rmulU _ (hl k (List.mem_cons_self ..)), List.map_cons, List.prod_cons, mul_assoc]

theorem pcElt_pmul (g h : (ℕ × ℕ) × ℕ) : pcElt (MonsterB.P0Rank.pmul p0Data g h) = pcElt g * pcElt h := by
  rw [MonsterB.P0Rank.pmul, pcElt_foldl_rmulU _ (fun k hk => List.mem_range.1 (List.mem_filter.1 hk).1),
    ← prod_map_ite_filter, ← pc_uE_eq_prod]
  simp only [pcElt]
  rw [pcL_lmul, pcL_conjkap]
  group

end CFSG.KC.P0Col
