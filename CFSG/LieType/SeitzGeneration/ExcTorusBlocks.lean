module

public import CFSG.RankThree.Lattice.SteinbergBIDet

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.Lattice Polynomial

theorem cyclotomic_eq_of_mul {e : ℕ} (he : 0 < e) {P : ℤ[X]}
    (h : P * ∏ d ∈ e.properDivisors, cyclotomic d ℤ = X ^ e - 1) : cyclotomic e ℤ = P := by
  have h1 := prod_cyclotomic_eq_X_pow_sub_one he ℤ
  rw [← Nat.cons_self_properDivisors he.ne', Finset.prod_cons] at h1
  have hne : ∏ d ∈ e.properDivisors, cyclotomic d ℤ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun d _ => (cyclotomic.monic d ℤ).ne_zero
  exact mul_right_cancel₀ hne (h1.trans h.symm)

theorem cyclotomic_three_eq : cyclotomic 3 ℤ = X ^ 2 + X + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 3 = {1} by decide, Finset.prod_singleton, cyclotomic_one]
  ring

theorem cyclotomic_four_eq : cyclotomic 4 ℤ = X ^ 2 + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 4 = {1, 2} by decide, Finset.prod_pair (by decide),
    cyclotomic_one, cyclotomic_two]
  ring

theorem cyclotomic_five_eq : cyclotomic 5 ℤ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 5 = {1} by decide, Finset.prod_singleton, cyclotomic_one]
  ring

theorem cyclotomic_six_eq : cyclotomic 6 ℤ = X ^ 2 - X + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 6 = {1, 2, 3} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by decide), cyclotomic_one, cyclotomic_two, cyclotomic_three_eq]
  ring

theorem cyclotomic_seven_eq :
    cyclotomic 7 ℤ = X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 7 = {1} by decide, Finset.prod_singleton, cyclotomic_one]
  ring

theorem cyclotomic_eight_eq : cyclotomic 8 ℤ = X ^ 4 + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 8 = {1, 2, 4} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by decide), cyclotomic_one, cyclotomic_two, cyclotomic_four_eq]
  ring

theorem cyclotomic_nine_eq : cyclotomic 9 ℤ = X ^ 6 + X ^ 3 + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 9 = {1, 3} by decide, Finset.prod_pair (by decide),
    cyclotomic_one, cyclotomic_three_eq]
  ring

theorem cyclotomic_ten_eq : cyclotomic 10 ℤ = X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 10 = {1, 2, 5} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by decide), cyclotomic_one, cyclotomic_two, cyclotomic_five_eq]
  ring

theorem cyclotomic_twelve_eq : cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 12 = {1, 2, 3, 4, 6} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide),
    cyclotomic_one, cyclotomic_two, cyclotomic_three_eq, cyclotomic_four_eq, cyclotomic_six_eq]
  ring

theorem cyclotomic_fourteen_eq :
    cyclotomic 14 ℤ = X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 14 = {1, 2, 7} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by decide), cyclotomic_one, cyclotomic_two, cyclotomic_seven_eq]
  ring

theorem cyclotomic_eighteen_eq : cyclotomic 18 ℤ = X ^ 6 - X ^ 3 + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 18 = {1, 2, 3, 6, 9} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide),
    cyclotomic_one, cyclotomic_two, cyclotomic_three_eq, cyclotomic_six_eq, cyclotomic_nine_eq]
  ring

theorem cyclotomic_fifteen_eq :
    cyclotomic 15 ℤ = X ^ 8 - X ^ 7 + X ^ 5 - X ^ 4 + X ^ 3 - X + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 15 = {1, 3, 5} by decide, Finset.prod_insert (by decide),
    Finset.prod_pair (by decide), cyclotomic_one, cyclotomic_three_eq, cyclotomic_five_eq]
  ring

theorem cyclotomic_twenty_eq : cyclotomic 20 ℤ = X ^ 8 - X ^ 6 + X ^ 4 - X ^ 2 + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 20 = {1, 2, 4, 5, 10} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide),
    cyclotomic_one, cyclotomic_two, cyclotomic_four_eq, cyclotomic_five_eq, cyclotomic_ten_eq]
  ring

theorem cyclotomic_twentyfour_eq : cyclotomic 24 ℤ = X ^ 8 - X ^ 4 + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 24 = {1, 2, 3, 4, 6, 8, 12} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide),
    cyclotomic_one, cyclotomic_two, cyclotomic_three_eq, cyclotomic_four_eq, cyclotomic_six_eq,
    cyclotomic_eight_eq, cyclotomic_twelve_eq]
  ring

theorem cyclotomic_thirty_eq :
    cyclotomic 30 ℤ = X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 := by
  refine cyclotomic_eq_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 30 = {1, 2, 3, 5, 6, 10, 15} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide),
    cyclotomic_one, cyclotomic_two, cyclotomic_three_eq, cyclotomic_five_eq, cyclotomic_six_eq,
    cyclotomic_ten_eq, cyclotomic_fifteen_eq]
  ring

@[expose] def cycloSupported : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30]

@[expose] def cycloList : ℕ → List ℤ
  | 1 => [-1, 1]
  | 2 => [1, 1]
  | 3 => [1, 1, 1]
  | 4 => [1, 0, 1]
  | 5 => [1, 1, 1, 1, 1]
  | 6 => [1, -1, 1]
  | 7 => [1, 1, 1, 1, 1, 1, 1]
  | 8 => [1, 0, 0, 0, 1]
  | 9 => [1, 0, 0, 1, 0, 0, 1]
  | 10 => [1, -1, 1, -1, 1]
  | 12 => [1, 0, -1, 0, 1]
  | 14 => [1, -1, 1, -1, 1, -1, 1]
  | 15 => [1, -1, 0, 1, -1, 1, 0, -1, 1]
  | 18 => [1, 0, 0, -1, 0, 0, 1]
  | 20 => [1, 0, -1, 0, 1, 0, -1, 0, 1]
  | 24 => [1, 0, 0, 0, -1, 0, 0, 0, 1]
  | 30 => [1, 1, 0, -1, -1, -1, 0, 1, 1]
  | _ => []

@[expose] def cycloDeg : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 4
  | 6 => 2
  | 7 => 6
  | 8 => 4
  | 9 => 6
  | 10 => 4
  | 12 => 4
  | 14 => 6
  | 15 => 8
  | 18 => 6
  | 20 => 8
  | 24 => 8
  | 30 => 8
  | _ => 0

@[expose] def lcompanion (d : ℕ) (cs : List ℤ) : List (List ℤ) :=
  lofFn d fun i j =>
    if (j : ℕ) + 1 = d then -(cs.getD i 0) else if (i : ℕ) = j + 1 then 1 else 0

theorem charpoly_companion_one :
    (toMat 1 (lcompanion 1 (cycloList 1))).charpoly = cyclotomic 1 ℤ := by
  rw [cyclotomic_one]
  exact charpoly_eq_of_lists (cs := cycloList 1) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 1) (by decide +kernel))

theorem charpoly_companion_two :
    (toMat 1 (lcompanion 1 (cycloList 2))).charpoly = cyclotomic 2 ℤ := by
  rw [cyclotomic_two]
  exact charpoly_eq_of_lists (cs := cycloList 2) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 1) (by decide +kernel))

theorem charpoly_companion_three :
    (toMat 2 (lcompanion 2 (cycloList 3))).charpoly = cyclotomic 3 ℤ := by
  rw [cyclotomic_three_eq]
  exact charpoly_eq_of_lists (cs := cycloList 3) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 2) (by decide +kernel))

theorem charpoly_companion_four :
    (toMat 2 (lcompanion 2 (cycloList 4))).charpoly = cyclotomic 4 ℤ := by
  rw [cyclotomic_four_eq]
  exact charpoly_eq_of_lists (cs := cycloList 4) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 2) (by decide +kernel))

theorem charpoly_companion_five :
    (toMat 4 (lcompanion 4 (cycloList 5))).charpoly = cyclotomic 5 ℤ := by
  rw [cyclotomic_five_eq]
  exact charpoly_eq_of_lists (cs := cycloList 5) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 4) (by decide +kernel))

theorem charpoly_companion_six :
    (toMat 2 (lcompanion 2 (cycloList 6))).charpoly = cyclotomic 6 ℤ := by
  rw [cyclotomic_six_eq]
  exact charpoly_eq_of_lists (cs := cycloList 6) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 2) (by decide +kernel))

theorem charpoly_companion_seven :
    (toMat 6 (lcompanion 6 (cycloList 7))).charpoly = cyclotomic 7 ℤ := by
  rw [cyclotomic_seven_eq]
  exact charpoly_eq_of_lists (cs := cycloList 7) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 6) (by decide +kernel))

theorem charpoly_companion_eight :
    (toMat 4 (lcompanion 4 (cycloList 8))).charpoly = cyclotomic 8 ℤ := by
  rw [cyclotomic_eight_eq]
  exact charpoly_eq_of_lists (cs := cycloList 8) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 4) (by decide +kernel))

theorem charpoly_companion_nine :
    (toMat 6 (lcompanion 6 (cycloList 9))).charpoly = cyclotomic 9 ℤ := by
  rw [cyclotomic_nine_eq]
  exact charpoly_eq_of_lists (cs := cycloList 9) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 6) (by decide +kernel))

theorem charpoly_companion_ten :
    (toMat 4 (lcompanion 4 (cycloList 10))).charpoly = cyclotomic 10 ℤ := by
  rw [cyclotomic_ten_eq]
  exact charpoly_eq_of_lists (cs := cycloList 10) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 4) (by decide +kernel))

theorem charpoly_companion_twelve :
    (toMat 4 (lcompanion 4 (cycloList 12))).charpoly = cyclotomic 12 ℤ := by
  rw [cyclotomic_twelve_eq]
  exact charpoly_eq_of_lists (cs := cycloList 12) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 4) (by decide +kernel))

theorem charpoly_companion_fourteen :
    (toMat 6 (lcompanion 6 (cycloList 14))).charpoly = cyclotomic 14 ℤ := by
  rw [cyclotomic_fourteen_eq]
  exact charpoly_eq_of_lists (cs := cycloList 14) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 6) (by decide +kernel))

theorem charpoly_companion_eighteen :
    (toMat 6 (lcompanion 6 (cycloList 18))).charpoly = cyclotomic 18 ℤ := by
  rw [cyclotomic_eighteen_eq]
  exact charpoly_eq_of_lists (cs := cycloList 18) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 6) (by decide +kernel))

theorem charpoly_companion_fifteen :
    (toMat 8 (lcompanion 8 (cycloList 15))).charpoly = cyclotomic 15 ℤ := by
  rw [cyclotomic_fifteen_eq]
  exact charpoly_eq_of_lists (cs := cycloList 15) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 8) (by decide +kernel))

theorem charpoly_companion_twenty :
    (toMat 8 (lcompanion 8 (cycloList 20))).charpoly = cyclotomic 20 ℤ := by
  rw [cyclotomic_twenty_eq]
  exact charpoly_eq_of_lists (cs := cycloList 20) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 8) (by decide +kernel))

theorem charpoly_companion_twentyfour :
    (toMat 8 (lcompanion 8 (cycloList 24))).charpoly = cyclotomic 24 ℤ := by
  rw [cyclotomic_twentyfour_eq]
  exact charpoly_eq_of_lists (cs := cycloList 24) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 8) (by decide +kernel))

theorem charpoly_companion_thirty :
    (toMat 8 (lcompanion 8 (cycloList 30))).charpoly = cyclotomic 30 ℤ := by
  rw [cyclotomic_thirty_eq]
  exact charpoly_eq_of_lists (cs := cycloList 30) (by monicity!) (by compute_degree!)
    (by simp [polyOfList, cycloList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 8) (by decide +kernel))

theorem charpoly_companion_cyclotomic {d : ℕ} (hd : d ∈ cycloSupported) :
    (toMat (cycloDeg d) (lcompanion (cycloDeg d) (cycloList d))).charpoly = cyclotomic d ℤ := by
  simp only [cycloSupported, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  exacts [charpoly_companion_one, charpoly_companion_two, charpoly_companion_three,
    charpoly_companion_four, charpoly_companion_five, charpoly_companion_six,
    charpoly_companion_seven, charpoly_companion_eight, charpoly_companion_nine,
    charpoly_companion_ten, charpoly_companion_twelve, charpoly_companion_fourteen,
    charpoly_companion_fifteen, charpoly_companion_eighteen, charpoly_companion_twenty,
    charpoly_companion_twentyfour, charpoly_companion_thirty]

@[expose] def blockSize : List ℕ → ℕ
  | [] => 0
  | d :: ds => cycloDeg d + blockSize ds

@[expose] def blockCheck : List ℕ → List (List ℤ) → Bool
  | [], _ => true
  | d :: ds, M =>
    lowerLeftZero (cycloDeg d) (blockSize ds) M &&
      decide (ltopLeft (cycloDeg d) M = lcompanion (cycloDeg d) (cycloList d)) &&
      blockCheck ds (lbotRight (cycloDeg d) (blockSize ds) M)

theorem charpoly_of_blockCheck : ∀ (ds : List ℕ) (M : List (List ℤ)),
    (∀ d ∈ ds, d ∈ cycloSupported) → blockCheck ds M = true →
      (toMat (blockSize ds) M).charpoly = (ds.map fun d => cyclotomic d ℤ).prod
  | [], M, _, _ => by
    have : IsEmpty (Fin (blockSize [])) := inferInstanceAs (IsEmpty (Fin 0))
    exact Matrix.charpoly_isEmpty
  | d :: ds, M, hds, hcheck => by
    simp only [blockCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcheck
    have hb := charpoly_eq_mul_of_blocks (k := cycloDeg d) (m := blockSize ds) M h1
    rw [h2, charpoly_companion_cyclotomic (hds d List.mem_cons_self),
      charpoly_of_blockCheck ds _ (fun e he => hds e (List.mem_cons_of_mem _ he)) h3] at hb
    show (toMat (cycloDeg d + blockSize ds) M).charpoly = _
    rw [List.map_cons, List.prod_cons]
    exact hb

theorem charpoly_of_basis {r : ℕ} (M B B' : List (List ℤ)) (ds : List ℕ)
    (hds : ∀ d ∈ ds, d ∈ cycloSupported) (hr : blockSize ds = r) (hBB' : lmul r B B' = lid r)
    (hcheck : blockCheck ds (lmul r (lmul r B' M) B) = true) :
    (toMat r M).charpoly = (ds.map fun d => cyclotomic d ℤ).prod := by
  subst hr
  have hc := charpoly_of_blockCheck ds _ hds hcheck
  rw [toMat_lmul, toMat_lmul] at hc
  rw [charpoly_eq_of_conj (B := toMat _ B) (B' := toMat _ B')
    (by rw [← toMat_lmul, hBB', toMat_lid])]
  exact hc

end CFSG.LieType.SeitzGeneration
