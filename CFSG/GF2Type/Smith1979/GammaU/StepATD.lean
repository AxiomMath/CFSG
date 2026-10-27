module

public import CFSG.GF2Type.Smith1979.GammaU.StepASpec

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

theorem ite_inj {b b' : Bool} (h : (if b then (1 : ZMod 2) else 0) = if b' then 1 else 0) :
    b = b' := by
  cases b <;> cases b' <;> first | rfl | exact absurd h (by decide)

theorem f0_add_left (x y z : V12) : f0 (x + y) z = f0 x z + f0 y z := by
  simp only [f0, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem f0b_xor_left (m n k : ℕ) : f0b (m ^^^ n) k = (f0b m k ^^ f0b n k) := by
  apply ite_inj
  rw [← ite_add_ite, ← f0_vecOf, ← f0_vecOf, ← f0_vecOf, vecOf_xor, f0_add_left]

theorem f0_isometry {g : V12 ≃ₗ[ZMod 2] V12} (hg : ∀ x, q0 (g x) = q0 x) (x y : V12) :
    f0 (g x) (g y) = f0 x y := by
  rw [← polar_q0, ← polar_q0, QuadraticMap.polar, QuadraticMap.polar, ← map_add, hg, hg, hg]

theorem vec_sub_mem_span {D : List ℕ} (hD : ∀ d ∈ D, d < 4096) {m : ℕ} (hm : m < 4096)
    {x : V12} (hx : x ∈ spanOf D) (h : vecOf m = x) : (spanList D).contains m = true := by
  rw [List.contains_iff_mem, mem_spanList_iff hD hm, h]
  exact hx

section Y

variable {g : V12 ≃ₗ[ZMod 2] V12}

@[expose] noncomputable def Y (g : V12 ≃ₗ[ZMod 2] V12) (n : ℕ) : ℕ := codeOf (g (vecOf n))

theorem vecOf_Y (n : ℕ) : vecOf (Y g n) = g (vecOf n) := vecOf_codeOf _

theorem Y_lt (n : ℕ) : Y g n < 4096 := codeOf_lt _

theorem Y_zero : Y g 0 = 0 := by
  rw [Y, vecOf_zero, map_zero]
  exact codeOf_vecOf (n := 0) (by norm_num)

theorem Y_xor {m n : ℕ} : Y g (m ^^^ n) = Y g m ^^^ Y g n :=
  vecOf_inj (Y_lt _) (xor_lt (Y_lt _) (Y_lt _)) (by rw [vecOf_xor, vecOf_Y, vecOf_Y, vecOf_Y,
    vecOf_xor, map_add])

theorem q0b_Y (hg : g ∈ gammaU) (n : ℕ) : q0b (Y g n) = q0b n :=
  ite_inj (by rw [← q0_vecOf, ← q0_vecOf, vecOf_Y, hg.1])

theorem f0b_Y (hg : g ∈ gammaU) (m n : ℕ) : f0b (Y g m) (Y g n) = f0b m n :=
  ite_inj (by rw [← f0_vecOf, ← f0_vecOf, vecOf_Y, vecOf_Y, f0_isometry hg.1])

theorem Y_theta_one (hu : ∀ x, g (theta0 x) = theta0 (g x)) {n : ℕ} (hn : n < 4096) :
    Y g (theta0N n) = thetaPow 1 (Y g n) := by
  simp only [thetaPow, if_true]
  refine vecOf_inj (Y_lt _) (theta0N_lt (Y_lt _)) ?_
  rw [vecOf_Y, vecOf_theta0N hn, hu, vecOf_theta0N (Y_lt _), vecOf_Y]

theorem Y_theta_two (ha : ∀ x, g (theta0 x) = theta0 (theta0 (g x))) {n : ℕ} (hn : n < 4096) :
    Y g (theta0N n) = thetaPow 2 (Y g n) := by
  simp only [thetaPow, show (2 : ℕ) ≠ 1 by norm_num, if_false]
  refine vecOf_inj (Y_lt _) (theta0N_lt (theta0N_lt (Y_lt _))) ?_
  rw [vecOf_Y, vecOf_theta0N hn, ha, vecOf_theta0N (theta0N_lt (Y_lt _)),
    vecOf_theta0N (Y_lt _), vecOf_Y]

end Y

theorem getElem!_map_Y {g : V12 ≃ₗ[ZMod 2] V12} (l : List ℕ) (k : ℕ) :
    (l.map (Y g))[k]! = Y g l[k]! := by
  by_cases hk : k < l.length
  · rw [getElem!_pos (l.map (Y g)) k (by simpa using hk), getElem!_pos l k hk, List.getElem_map]
  · rw [getElem!_neg (l.map (Y g)) k (by simpa using hk), getElem!_neg l k hk]
    exact Y_zero.symm

theorem xorSel_map_Y {g : V12 ≃ₗ[ZMod 2] V12} (c : ℕ) (l : List ℕ) :
    xorSel c (l.map (Y g)) = Y g (xorSel c l) := by
  unfold xorSel
  generalize (List.range 12) = L
  suffices h : ∀ acc, L.foldl (fun acc k => if c.testBit k then acc ^^^ (l.map (Y g))[k]! else acc)
      (Y g acc) = Y g (L.foldl (fun acc k => if c.testBit k then acc ^^^ l[k]! else acc) acc) by
    have h0 := h 0
    rw [Y_zero] at h0
    exact h0
  induction L with
  | nil => exact fun _ => rfl
  | cons k L ih =>
    intro acc
    simp only [List.foldl_cons]
    split_ifs
    · rw [getElem!_map_Y, ← Y_xor, ih]
    · exact ih acc

theorem xorSel_lt {c : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < 4096) : xorSel c l < 4096 := by
  unfold xorSel
  generalize (List.range 12) = L
  suffices h : ∀ acc, acc < 4096 →
      L.foldl (fun acc k => if c.testBit k then acc ^^^ l[k]! else acc) acc < 4096 from
    h 0 (by norm_num)
  induction L with
  | nil => exact fun _ h => h
  | cons k L ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    refine ih _ ?_
    split_ifs
    · refine xor_lt hacc ?_
      by_cases hk : k < l.length
      · rw [getElem!_pos l k hk]
        exact hl _ (List.getElem_mem hk)
      · rw [getElem!_neg l k hk]
        norm_num
    · exact hacc

@[expose] def basisW : List ℕ := [3072, 3120, 1, 64, 2, 128, 4, 256, 8, 512, 16, 1024]

theorem xorSel_coefW : ∀ j < 12, xorSel coefW[j]! basisW = 2 ^ j := by decide

theorem linOfRows_unit (r : Array ℕ) (j : Fin 12) :
    linOfRows r (vecOf (2 ^ (j : ℕ))) = vecOf r[(j : ℕ)]! := by
  rw [linOfRows_apply, vecOf_two_pow, Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Pi.single_apply, hkj]
  · simp

section Complete

variable {D : List ℕ} (hD : ∀ d ∈ D, d < 4096) {g : V12 ≃ₗ[ZMod 2] V12} (hg : g ∈ gammaU)
  (ha : g (vecOf a0) = vecOf a0)
  (hperp : ∀ x, f0 x (vecOf a0) = 0 → g x - x ∈ spanOf D)
  (hDD : ∀ d ∈ spanOf D, g d - d = 0 ∨ g d - d = vecOf a0)
include hD hg ha hperp hDD

theorem Y_a0 : Y g a0 = a0 := by
  rw [Y, ha]
  exact codeOf_vecOf (by norm_num [a0])

theorem contains_Y_xor {n : ℕ} (hn : n < 4096) (hf : f0b n a0 = false) :
    (spanList D).contains (Y g n ^^^ n) = true := by
  have h0 : f0 (vecOf n) (vecOf a0) = 0 := by rw [f0_vecOf, hf]; rfl
  refine vec_sub_mem_span hD (xor_lt (Y_lt _) hn) (hperp _ h0) ?_
  rw [vecOf_xor, vecOf_Y, ← vec_sub_eq_add]

theorem coset_mem {w tw : ℕ} (hw : w < 4096) (htw : tw < 4096) (hfw : f0b w a0 = false)
    (hftw : f0b tw a0 = false) :
    Y g w ∈ (spanList D).map (w ^^^ ·) ∧ (spanList D).contains (Y g tw ^^^ tw) = true :=
  ⟨List.mem_map.2 ⟨Y g w ^^^ w, (List.contains_iff_mem).1
      (contains_Y_xor hD hg ha hperp hDD hw hfw), by
        rw [Nat.xor_comm (Y g w) w, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]⟩,
    contains_Y_xor hD hg ha hperp hDD htw hftw⟩

theorem cand_mem {e : ℕ} (he : e = 1 ∨ e = 2)
    (hY : ∀ n < 4096, Y g (theta0N n) = thetaPow e (Y g n)) :
    ∀ (i : ℕ) (hi : i < (ws.map (Y g)).length),
      (ws.map (Y g))[i] ∈ candT (spanList D) (perp5 e) e ([] ++ (ws.map (Y g)).take i) := by
  have h1 : thetaPow e (Y g 3072) = Y g 3120 := (hY 3072 (by norm_num)).symm
  have h2 : thetaPow e (Y g 1) = Y g 64 := (hY 1 (by norm_num)).symm
  have h3 : thetaPow e (Y g 2) = Y g 128 := (hY 2 (by norm_num)).symm
  have h4 : thetaPow e (Y g 4) = Y g 256 := (hY 4 (by norm_num)).symm
  have h5 : thetaPow e (Y g 8) = Y g 512 := (hY 8 (by norm_num)).symm
  have h6 : thetaPow e (Y g 16) = Y g 1024 := (hY 16 (by norm_num)).symm
  have hq := q0b_Y hg
  have hf := f0b_Y hg
  intro i hi
  simp only [List.length_map, ws, List.length_cons, List.length_nil] at hi
  interval_cases i
  all_goals
    simp (config := { decide := true }) only [candT, ws, List.map_cons, List.map_nil, List.take,
      List.nil_append, List.length_cons, List.length_nil, List.getElem_cons_zero,
      List.getElem_cons_succ, List.getElem!_cons_zero, List.getElem!_cons_succ, zero_add,
      Nat.reduceAdd, List.mem_filter, theta0N, Nat.reduceShiftRight, Nat.reduceAnd, Nat.reduceXor,
      Nat.reduceOr, Nat.reduceShiftLeft, List.range_succ, List.range_zero, List.nil_append,
      List.all_append, List.all_cons, List.all_nil, if_true, if_false, h1, h2, h3, h4, h5, h6, hq,
      hf, beq_self_eq_true, Bool.true_and, Bool.and_true, Bool.true_or, Bool.or_true,
      Nat.reduceBEq, decide_false, decide_true, Bool.false_or, and_true]
  case «0» =>
    rw [show Y g 3072 = 3072 from Y_a0 hD hg ha hperp hDD]
    exact List.mem_singleton_self _
  case «1» => exact coset_mem hD hg ha hperp hDD (by norm_num) (by norm_num) (by decide) (by decide)
  case «2» => exact coset_mem hD hg ha hperp hDD (by norm_num) (by norm_num) (by decide) (by decide)
  case «3» => exact coset_mem hD hg ha hperp hDD (by norm_num) (by norm_num) (by decide) (by decide)
  case «4» => exact coset_mem hD hg ha hperp hDD (by norm_num) (by norm_num) (by decide) (by decide)
  case «5» =>
    refine List.mem_map.2 ⟨Y g 16 ^^^ 16, ?_, by
      rw [Nat.xor_comm (Y g 16) 16, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]⟩
    have hYa : Y g 3072 = 3072 := Y_a0 hD hg ha hperp hDD
    rw [hYa] at h1
    simp only [perp5, List.mem_filter, List.mem_range, xor_lt (Y_lt _) (show 16 < 4096 by norm_num),
      true_and, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, f0b_xor_left]
    refine ⟨?_, ?_⟩
    · have key : f0b (Y g 16) 3072 = f0b 16 3072 := by rw [← hf 16 3072, hYa]
      change (f0b (Y g 16) 3072 ^^ f0b 16 3072) = false
      rw [key, Bool.xor_self]
    · rw [show theta0N a0 = 3120 by decide]
      rcases he with rfl | rfl
      · have h31 : Y g 3120 = 3120 := by rw [← h1]; decide
        have key : f0b (Y g 16) 3120 = f0b 16 3120 := by rw [← hf 16 3120, h31]
        rw [key]
        decide
      · have h31 : Y g 3120 = 48 := by rw [← h1]; decide
        have h48 : Y g 48 = 3120 := by
          rw [show (48 : ℕ) = 3120 ^^^ 3072 by decide, Y_xor, h31, hYa]
          decide
        have key : f0b (Y g 16) 3120 = f0b 16 48 := by rw [← hf 16 48, h48]
        rw [key]
        decide

theorem mem_tdList : ∃ r ∈ tdList D, (∀ x ∈ r, x < 4096) ∧ ∀ x, g x = linOfRows r x := by
  obtain ⟨e, he, hY⟩ : ∃ e, (e = 1 ∨ e = 2) ∧
      ∀ n < 4096, Y g (theta0N n) = thetaPow e (Y g n) := by
    rcases hg.2 with hu | hanti
    · exact ⟨1, Or.inl rfl, fun n hn => Y_theta_one hu hn⟩
    · exact ⟨2, Or.inr rfl, fun n hn => Y_theta_two hanti hn⟩
  have hleaf : ws.map (Y g) ∈ extDFS (candT (spanList D) (perp5 e) e) 6 [] := by
    have := mem_extDFS (candT (spanList D) (perp5 e) e) (ws.map (Y g)) []
      (cand_mem hD hg ha hperp hDD he hY)
    simpa [ws] using this
  set r := rowsOfImgs (imgsOf e (ws.map (Y g))) with hr
  have himgs : imgsOf e (ws.map (Y g)) = basisW.map (Y g) := by
    have h1 : thetaPow e (Y g 3072) = Y g 3120 := (hY 3072 (by norm_num)).symm
    have h2 : thetaPow e (Y g 1) = Y g 64 := (hY 1 (by norm_num)).symm
    have h3 : thetaPow e (Y g 2) = Y g 128 := (hY 2 (by norm_num)).symm
    have h4 : thetaPow e (Y g 4) = Y g 256 := (hY 4 (by norm_num)).symm
    have h5 : thetaPow e (Y g 8) = Y g 512 := (hY 8 (by norm_num)).symm
    have h6 : thetaPow e (Y g 16) = Y g 1024 := (hY 16 (by norm_num)).symm
    simp only [imgsOf, ws, basisW, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, h1, h2, h3, h4, h5, h6]
  have hbasis_lt : ∀ x ∈ basisW.map (Y g), x < 4096 := fun x hx => by
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hx
    exact Y_lt n
  have hr_lt : ∀ x ∈ r, x < 4096 := fun x hx => by
    rw [hr, rowsOfImgs, himgs, List.mem_toArray, List.mem_map] at hx
    obtain ⟨c, -, rfl⟩ := hx
    exact xorSel_lt hbasis_lt
  have hrows : ∀ j : Fin 12, vecOf r[(j : ℕ)]! = g (vecOf (2 ^ (j : ℕ))) := by
    intro j
    have hj : (j : ℕ) < (coefW.map fun c => xorSel c (basisW.map (Y g))).length := by
      simp [coefW]
    have hc : coefW[(j : ℕ)]! = coefW[(j : ℕ)]'(by simp [coefW]) :=
      getElem!_pos coefW (j : ℕ) (by simp [coefW])
    rw [hr, rowsOfImgs, himgs, List.getElem!_toArray,
      getElem!_pos (coefW.map fun c => xorSel c (basisW.map (Y g))) (j : ℕ) hj, List.getElem_map,
      xorSel_map_Y, ← hc, xorSel_coefW j j.isLt, vecOf_Y]
  have hlin : ∀ x, g x = linOfRows r x := by
    have h : (g : V12 →ₗ[ZMod 2] V12) = linOfRows r :=
      linMap_ext fun j => by rw [linOfRows_unit, hrows]; rfl
    exact fun x => LinearMap.congr_fun h x
  have happ : ∀ n < 4096, appN r n = Y g n := fun n hn =>
    vecOf_inj (appN_lt hr_lt n) (Y_lt n) (by rw [vecOf_appN, ← hlin, vecOf_Y])
  have hleafOK : leafOK D (spanList D) r = true := by
    simp only [leafOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨fun d hd => ?_, ?_⟩
    · have hd4 := hD d hd
      rw [happ d hd4]
      have hv : vecOf (Y g d ^^^ d) = g (vecOf d) - vecOf d := by
        rw [vecOf_xor, vecOf_Y, vec_sub_eq_add]
      rcases hDD (vecOf d) (mem_spanOf_of_mem hd) with h0 | h0
      · left
        exact vecOf_inj (xor_lt (Y_lt _) hd4) (by norm_num) (by rw [hv, h0, vecOf_zero])
      · right
        exact vecOf_inj (xor_lt (Y_lt _) hd4) (by norm_num [a0]) (by rw [hv, h0])
    · rw [happ u0 (by norm_num [u0])]
      exact contains_Y_xor hD hg ha hperp hDD (by norm_num [u0]) (by decide)
  refine ⟨r, ?_, hr_lt, hlin⟩
  simp only [tdList, List.mem_flatMap, List.mem_filterMap]
  refine ⟨e, by rcases he with rfl | rfl <;> simp, ws.map (Y g), hleaf, ?_⟩
  simp only [← hr, hleafOK, if_true]

end Complete

end CFSG.GF2Type.Smith1979.GammaU.StepA
