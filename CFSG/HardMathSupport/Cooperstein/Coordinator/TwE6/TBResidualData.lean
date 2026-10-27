module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.PolyIndep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Interfaces

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

@[expose] def repLines : List (List (Fin 4) × ℕ × ℕ) :=
  [([], 0, 1),
    ([1], 0, 2),
    ([0,1], 1, 2),
    ([2,1], 0, 3),
    ([2,0,1], 1, 3),
    ([1,2,1], 0, 5),
    ([3,2,1], 0, 4),
    ([1,2,0,1], 2, 5),
    ([3,2,0,1], 1, 4),
    ([0,1,2,1], 1, 7),
    ([3,1,2,1], 0, 6),
    ([0,1,2,0,1], 2, 7),
    ([2,1,2,0,1], 3, 5),
    ([3,1,2,0,1], 2, 6),
    ([3,0,1,2,1], 1, 9),
    ([2,3,1,2,1], 0, 8),
    ([2,0,1,2,0,1], 3, 7),
    ([3,0,1,2,0,1], 2, 9),
    ([3,2,1,2,0,1], 4, 6),
    ([2,3,1,2,0,1], 3, 8),
    ([2,3,0,1,2,1], 1, 11),
    ([1,2,3,1,2,1], 0, 10),
    ([1,2,0,1,2,0,1], 5, 7),
    ([3,2,0,1,2,0,1], 4, 9),
    ([2,3,0,1,2,0,1], 3, 11),
    ([2,3,2,1,2,0,1], 4, 8),
    ([1,2,3,1,2,0,1], 5, 10),
    ([1,2,3,0,1,2,1], 2, 16),
    ([0,1,2,3,1,2,1], 1, 15),
    ([3,1,2,0,1,2,0,1], 6, 9),
    ([2,3,2,0,1,2,0,1], 4, 11),
    ([1,2,3,0,1,2,0,1], 5, 16),
    ([1,2,3,2,1,2,0,1], 6, 10),
    ([0,1,2,3,1,2,0,1], 7, 15),
    ([0,1,2,3,0,1,2,1], 2, 17),
    ([2,1,2,3,0,1,2,1], 3, 18),
    ([2,3,1,2,0,1,2,0,1], 8, 11),
    ([1,2,3,2,0,1,2,0,1], 6, 16),
    ([0,1,2,3,0,1,2,0,1], 7, 17),
    ([2,1,2,3,0,1,2,0,1], 5, 18),
    ([0,1,2,3,2,1,2,0,1], 9, 15),
    ([2,1,2,3,2,1,2,0,1], 8, 10),
    ([2,0,1,2,3,0,1,2,1], 3, 19),
    ([3,2,1,2,3,0,1,2,1], 4, 20),
    ([1,2,3,1,2,0,1,2,0,1], 10, 16),
    ([0,1,2,3,2,0,1,2,0,1], 9, 17),
    ([2,0,1,2,3,0,1,2,0,1], 7, 19),
    ([1,2,0,1,2,3,0,1,2,1], 5, 22)]
@[expose] def piIdx : List ℕ := [26,25,24,23,22,21,19,20,17,18,15,16,12,13,14,10,11,8,9,6,7,5,4,3,2,1,0]
@[expose] def wordIdxN (l : List (Fin 4)) (b : ℕ) : ℕ :=
  l.foldr (fun a b => (TwistTag.E6.orbitWord a).foldr (fun i b => e6Data.weyl b i) b) b
@[expose] def w0word : List (Fin 4) := (List.replicate 6 [0, 1, 2, 3]).flatten
theorem w0word_ok :
    (List.range 27).all (fun b => wordIdxN w0word b = piIdx.getD b 0) = true := by decide +kernel
@[expose] def allLines : List (ℕ × ℕ) :=
  repLines.map (fun x => (x.2.1, x.2.2)) ++
    repLines.map (fun x => (piIdx.getD x.2.1 0, piIdx.getD x.2.2 0))
@[expose] def entry (p q : (ℕ × ℕ) × Bool) : Bool :=
  let a := piIdx.getD p.1.1 0
  let b := piIdx.getD p.1.2 0
  let n := (if q.1.1 = a ∨ q.1.1 = b then 1 else 0) + (if q.1.2 = a ∨ q.1.2 = b then 1 else 0)
  if n = 1 then true else if q.1.1 = a ∧ q.1.2 = b then p.2 != q.2 else false
@[expose] def pts : List ((ℕ × ℕ) × Bool) := allLines.flatMap fun l => [(l, false), (l, true)]

private def eq2Star (l : ℕ × ℕ) : ℕ × ℕ := (piIdx.getD l.1 0, piIdx.getD l.2 0)

private def eq2Cnt (x y : ℕ × ℕ) : ℕ :=
  (if y.1 = (eq2Star x).1 ∨ y.1 = (eq2Star x).2 then 1 else 0) +
    (if y.2 = (eq2Star x).1 ∨ y.2 = (eq2Star x).2 then 1 else 0)

private def eq2Ind (b : Bool) : ZMod 2 := if b then 1 else 0

private def eq2A (x y : ℕ × ℕ) : ZMod 2 := if eq2Cnt x y = 1 then 1 else 0

private def eq2B (x y : ℕ × ℕ) : ZMod 2 := if y = eq2Star x then 1 else 0

private def eq2D (β β' : Bool) : ZMod 2 := if β = β' then 0 else 1

private theorem eq2_nodup : allLines.Nodup := by decide +kernel

private theorem eq2_star_mem : ∀ x ∈ allLines, eq2Star x ∈ allLines := by decide +kernel

private theorem eq2_star_star : ∀ x ∈ allLines, eq2Star (eq2Star x) = x := by decide +kernel

private theorem eq2_piIdx_inv : ∀ i < 27, piIdx.getD (piIdx.getD i 0) 0 = i := by
  decide +kernel

private theorem eq2_piIdx_inj :
    ∀ a < 27, ∀ b < 27, (piIdx.getD a 0 = piIdx.getD b 0 ↔ a = b) := by
  decide +kernel

private theorem eq2_lt : ∀ x ∈ allLines, x.1 < 27 ∧ x.2 < 27 := by decide +kernel

private theorem eq2_cnt_comm : ∀ x ∈ allLines, ∀ z ∈ allLines,
    eq2Cnt x (eq2Star z) = eq2Cnt (eq2Star x) z := by
  intro x hx z hz
  obtain ⟨hx1, hx2⟩ := eq2_lt x hx
  obtain ⟨hz1, hz2⟩ := eq2_lt z hz
  simp only [eq2Cnt, eq2Star, eq2_piIdx_inv x.1 hx1, eq2_piIdx_inv x.2 hx2,
    eq2_piIdx_inj z.1 hz1 x.1 hx1, eq2_piIdx_inj z.1 hz1 x.2 hx2,
    eq2_piIdx_inj z.2 hz2 x.1 hx1, eq2_piIdx_inj z.2 hz2 x.2 hx2]

private theorem eq2_cnt_self (x : ℕ × ℕ) : eq2Cnt x (eq2Star x) = 2 := by
  simp [eq2Cnt]

private theorem eq2_entry_unfold (x y : ℕ × ℕ) (β β' : Bool) :
    entry (x, β) (y, β') =
      if eq2Cnt x y = 1 then true else if y = eq2Star x then (β != β') else false := by
  unfold entry eq2Cnt eq2Star
  simp only [Prod.ext_iff]

private theorem eq2_entry_ind (x y : ℕ × ℕ) (β β' : Bool) :
    eq2Ind (entry (x, β) (y, β')) = eq2A x y + eq2B x y * eq2D β β' := by
  rw [eq2_entry_unfold]
  by_cases hn : eq2Cnt x y = 1
  · have hy : y ≠ eq2Star x := by
      intro h
      subst h
      rw [eq2_cnt_self] at hn
      exact absurd hn (by norm_num)
    simp [eq2Ind, eq2A, eq2B, hn, hy]
  · by_cases hy : y = eq2Star x
    · subst hy
      cases β <;> cases β' <;> simp [eq2Ind, eq2A, eq2B, eq2D, hn]
    · simp [eq2Ind, eq2A, eq2B, eq2D, hn, hy]

private theorem eq2_ind_and (a b : Bool) : eq2Ind (a && b) = eq2Ind a * eq2Ind b := by
  cases a <;> cases b <;> decide

private theorem eq2_bool_expand : ∀ (a a' b b' : ZMod 2) (β β'' : Bool),
    ∑ β' : Bool, (a + b * eq2D β β') * (a' + b' * eq2D β' β'') =
      a * b' + b * a' + (if β = β'' then 1 else 0) * (b * b') := by
  decide +kernel

private theorem eq2_sum_1 (x : ℕ × ℕ) {z : ℕ × ℕ} (hz : z ∈ allLines) :
    ∑ y ∈ allLines.toFinset, eq2A x y * eq2B y z = eq2A x (eq2Star z) := by
  have hzs : eq2Star z ∈ allLines.toFinset := List.mem_toFinset.2 (eq2_star_mem z hz)
  calc ∑ y ∈ allLines.toFinset, eq2A x y * eq2B y z
      = ∑ y ∈ allLines.toFinset, if y = eq2Star z then eq2A x y else 0 := by
        refine Finset.sum_congr rfl fun y hy => ?_
        have hy' : y ∈ allLines := List.mem_toFinset.1 hy
        by_cases h : y = eq2Star z
        · subst h
          simp [eq2B, eq2_star_star z hz]
        · have h0 : eq2B y z = 0 := by
            unfold eq2B
            rw [if_neg]
            intro hc
            apply h
            rw [hc, eq2_star_star y hy']
          simp [h, h0]
    _ = eq2A x (eq2Star z) := by simp [hzs]

private theorem eq2_sum_2 {x : ℕ × ℕ} (hx : x ∈ allLines) (z : ℕ × ℕ) :
    ∑ y ∈ allLines.toFinset, eq2B x y * eq2A y z = eq2A (eq2Star x) z := by
  have hxs : eq2Star x ∈ allLines.toFinset := List.mem_toFinset.2 (eq2_star_mem x hx)
  calc ∑ y ∈ allLines.toFinset, eq2B x y * eq2A y z
      = ∑ y ∈ allLines.toFinset, if y = eq2Star x then eq2A y z else 0 := by
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases h : y = eq2Star x
        · subst h
          simp [eq2B]
        · simp [eq2B, h]
    _ = eq2A (eq2Star x) z := by simp [hxs]

private theorem eq2_sum_3 {x : ℕ × ℕ} (hx : x ∈ allLines) (z : ℕ × ℕ) :
    ∑ y ∈ allLines.toFinset, eq2B x y * eq2B y z = if z = x then 1 else 0 := by
  have hxs : eq2Star x ∈ allLines.toFinset := List.mem_toFinset.2 (eq2_star_mem x hx)
  calc ∑ y ∈ allLines.toFinset, eq2B x y * eq2B y z
      = ∑ y ∈ allLines.toFinset, if y = eq2Star x then (if z = x then 1 else 0) else 0 := by
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases h : y = eq2Star x
        · subst h
          simp [eq2B, eq2_star_star x hx]
        · simp [eq2B, h]
    _ = if z = x then 1 else 0 := by simp [hxs]

private theorem eq2_mem_fst {q : (ℕ × ℕ) × Bool} (h : q ∈ pts) : q.1 ∈ allLines := by
  unfold pts at h
  obtain ⟨l, hl, hq⟩ := List.mem_flatMap.1 h
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> exact hl

private theorem eq2_cast_countP (P : (ℕ × ℕ) × Bool → Bool) :
    ∀ l : List ((ℕ × ℕ) × Bool), ((l.countP P : ℕ) : ZMod 2) = (l.map fun q => eq2Ind (P q)).sum
  | [] => by simp
  | a :: l => by
    rw [List.countP_cons, List.map_cons, List.sum_cons, Nat.cast_add, eq2_cast_countP P l]
    by_cases h : P a = true <;> simp [eq2Ind, h, add_comm]

private theorem eq2_sum_flatMap (g : (ℕ × ℕ) × Bool → ZMod 2) :
    ∀ L : List (ℕ × ℕ), ((L.flatMap fun l => [(l, false), (l, true)]).map g).sum =
      (L.map fun l => g (l, false) + g (l, true)).sum
  | [] => by simp
  | a :: L => by
    simp [List.flatMap_cons, eq2_sum_flatMap g L, add_assoc]

private theorem eq2_two_eq_zero : ∀ a : ZMod 2, a + a = 0 := by decide

theorem entry_sq_eq_one : pts.all (fun p => pts.all (fun r =>
    decide ((pts.countP fun q => entry p q && entry q r) % 2 = if p = r then 1 else 0))) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  rintro ⟨x, β⟩ hp ⟨z, β''⟩ hr
  have hx : x ∈ allLines := eq2_mem_fst hp
  have hz : z ∈ allLines := eq2_mem_fst hr
  have hcount : ((pts.countP fun q => entry (x, β) q && entry q (z, β'')) : ZMod 2) =
      if (x, β) = (z, β'') then 1 else 0 := by
    rw [eq2_cast_countP]
    unfold pts
    rw [eq2_sum_flatMap]
    have hS : ∀ F : (ℕ × ℕ) → ZMod 2, (allLines.map F).sum = ∑ y ∈ allLines.toFinset, F y :=
      fun F => (List.sum_toFinset F eq2_nodup).symm
    rw [hS]
    have hterm : ∀ y : ℕ × ℕ,
        eq2Ind (entry (x, β) (y, false) && entry (y, false) (z, β'')) +
            eq2Ind (entry (x, β) (y, true) && entry (y, true) (z, β'')) =
          eq2A x y * eq2B y z + eq2B x y * eq2A y z +
            (if β = β'' then 1 else 0) * (eq2B x y * eq2B y z) := by
      intro y
      have h1 := eq2_bool_expand (eq2A x y) (eq2A y z) (eq2B x y) (eq2B y z) β β''
      rw [Fintype.sum_bool] at h1
      simp only [eq2_ind_and, eq2_entry_ind]
      linear_combination h1
    rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, eq2_sum_1 x hz, eq2_sum_2 hx z,
      eq2_sum_3 hx z]
    have hN : eq2A x (eq2Star z) = eq2A (eq2Star x) z := by
      unfold eq2A
      rw [eq2_cnt_comm x hx z hz]
    rw [hN, eq2_two_eq_zero, zero_add]
    by_cases h1 : x = z
    · subst h1
      by_cases h2 : β = β''
      · subst h2
        simp
      · simp [h2]
    · have h1' : z ≠ x := fun h => h1 h.symm
      simp [h1, h1']
  have hval := congrArg ZMod.val hcount
  rw [ZMod.val_natCast] at hval
  rw [hval]
  split_ifs <;> rfl

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
