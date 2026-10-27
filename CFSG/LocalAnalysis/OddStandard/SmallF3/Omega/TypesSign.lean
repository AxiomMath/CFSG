module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap

instance instInvertibleTwoZMod3 : Invertible (2 : ZMod 3) := ⟨2, by decide, by decide⟩

@[expose] def toSign : (ZMod 3)ˣ →* ℤˣ where
  toFun a := if a = 1 then 1 else -1
  map_one' := by simp
  map_mul' := by decide

private theorem units_zmod3_eq_one_or_neg_one (a : (ZMod 3)ˣ) : a = 1 ∨ a = -1 := by
  revert a
  decide

private theorem neg_one_ne_one : (-1 : (ZMod 3)ˣ) ≠ 1 := by decide

private theorem isSquare_units_zmod3 (a : (ZMod 3)ˣ) : IsSquare a ↔ a = 1 := by
  revert a
  decide

private abbrev mk_one (a : (ZMod 3)ˣ) : RegularFormClass (ZMod 3) :=
  Quotient.mk (regularFormSetoid (ZMod 3)) ⟨1, fun _ => a⟩

private theorem mk_one_one : mk_one (1 : (ZMod 3)ˣ) = (1 : RegularFormClass (ZMod 3)) :=
  RegularFormClass.mk_rankOne_one

private theorem toSign_one : toSign (1 : (ZMod 3)ˣ) = 1 := by simp [toSign]

private theorem toSign_neg_one : toSign (-1 : (ZMod 3)ˣ) = -1 := by
  simp [toSign, neg_one_ne_one]

private theorem toSign_injective : Function.Injective toSign := by
  intro a b hab
  rcases units_zmod3_eq_one_or_neg_one a with rfl | rfl <;>
    rcases units_zmod3_eq_one_or_neg_one b with rfl | rfl
  · rfl
  · exact absurd hab (by rw [toSign_one, toSign_neg_one]; decide)
  · exact absurd hab (by rw [toSign_neg_one, toSign_one]; decide)
  · rfl

private theorem toSign_surjective : Function.Surjective toSign := by
  intro β
  rcases Int.units_eq_one_or β with rfl | rfl
  · exact ⟨1, toSign_one⟩
  · exact ⟨-1, toSign_neg_one⟩

private theorem aux_mem_unitValueSet_neg_neg :
    (-1 : (ZMod 3)ˣ) ∈ unitValueSet (weightedSumSquares (ZMod 3) ![(-1 : ZMod 3), -1]) :=
  mem_unitValueSet.mpr ((represents_iff _ _).mpr (Set.mem_range.mpr
    ⟨![1, 0], by simp [weightedSumSquares_apply, Fin.sum_univ_two]⟩))

private theorem aux_mem_unitValueSet_one_one :
    (-1 : (ZMod 3)ˣ) ∈ unitValueSet (weightedSumSquares (ZMod 3) ![(1 : ZMod 3), 1]) :=
  mem_unitValueSet.mpr ((represents_iff _ _).mpr (Set.mem_range.mpr
    ⟨![1, 1], by
      simp only [weightedSumSquares_apply, Fin.sum_univ_two]
      decide⟩))

private theorem aux_isSquare_discr :
    IsSquare ((-1) * (-1) * ((1 : (ZMod 3)ˣ) * 1)) := by
  refine ⟨1, ?_⟩
  simp

private theorem aux_neg_neg :
    mk_one (-1 : (ZMod 3)ˣ) + mk_one (-1 : (ZMod 3)ˣ) =
      mk_one (1 : (ZMod 3)ˣ) + mk_one (1 : (ZMod 3)ˣ) := by
  rw [← RegularFormClass.mk_succ_eq_mk_rankOne_add (fun _ : Fin 2 => (-1 : (ZMod 3)ˣ)),
    ← RegularFormClass.mk_succ_eq_mk_rankOne_add (fun _ : Fin 2 => (1 : (ZMod 3)ˣ))]
  rw [RegularFormClass.mk_eq_mk_iff, presentedForm_two, presentedForm_two]
  exact TauCeti.equivalent_binary_of_isSquare_of_mem_unitValueSet
    (a := -1) (b := -1) (c := 1) (d := 1) aux_isSquare_discr
    aux_mem_unitValueSet_neg_neg aux_mem_unitValueSet_one_one

private theorem mk_one_add_mk_one_eq_one_add (d a : (ZMod 3)ˣ) :
    ∃ d' : (ZMod 3)ˣ, mk_one d + mk_one a = 1 + mk_one d' := by
  rcases units_zmod3_eq_one_or_neg_one d with rfl | rfl
  · exact ⟨a, by rw [mk_one_one]⟩
  · rcases units_zmod3_eq_one_or_neg_one a with rfl | rfl
    · exact ⟨-1, by rw [mk_one_one]; exact add_comm _ _⟩
    · exact ⟨1, by rw [aux_neg_neg, mk_one_one]⟩

private theorem exists_normal_form (x : RegularFormClass (ZMod 3)) (hx : 1 ≤ x.rank) :
    ∃ d : (ZMod 3)ˣ, x = (x.rank - 1) • (1 : RegularFormClass (ZMod 3)) + mk_one d := by
  induction x using RegularFormClass.induction_on_rankOne with
  | zero => simp at hx
  | add_rankOne y a ih =>
      by_cases hy : y.rank = 0
      · have hy0 : y = 0 := RegularFormClass.rank_eq_zero_iff.mp hy
        refine ⟨a, ?_⟩
        rw [hy0]
        simp
      · have hypos : 1 ≤ y.rank := by omega
        obtain ⟨d, hd⟩ := ih hypos
        obtain ⟨d', hd'⟩ := mk_one_add_mk_one_eq_one_add d a
        refine ⟨d', ?_⟩
        have hrank : (y + mk_one a).rank = y.rank + 1 := by
          rw [RegularFormClass.rank_add, RegularFormClass.rank_mk]
        have hsub : (y.rank - 1) • (1 : RegularFormClass (ZMod 3)) + 1 = y.rank • 1 := by
          conv_rhs => rw [← Nat.sub_add_cancel hypos]
          rw [add_nsmul, one_nsmul]
        rw [hrank, Nat.add_sub_cancel]
        conv_lhs => rw [hd]
        rw [add_assoc, hd', ← add_assoc, hsub]

open Classical in
@[expose] noncomputable def signOf (x : RegularFormClass (ZMod 3)) : ℤˣ :=
  if RegularFormClass.signedDiscr x = 0 then 1 else -1

private theorem sqNegOne_ne_zero : squareClass (-1 : (ZMod 3)ˣ) ≠ 0 := by
  intro h
  rw [squareClass_eq_zero_iff, isSquare_units_zmod3] at h
  exact neg_one_ne_one h

private theorem sqNegOne_add_self :
    squareClass (-1 : (ZMod 3)ˣ) + squareClass (-1 : (ZMod 3)ˣ) = 0 := by
  rw [← squareClass_mul]
  rw [show (-1 : (ZMod 3)ˣ) * (-1) = 1 by simp]
  rw [squareClass_eq_zero_iff]
  exact ⟨1, by simp⟩

private theorem sqClass_zmod3_eq_zero_or_sqNegOne (x : SquareClassGroup (ZMod 3)) :
    x = 0 ∨ x = squareClass (-1 : (ZMod 3)ˣ) := by
  have hx : x = squareClass (Additive.toMul (Quotient.out x)) := (squareClass_toMul_out x).symm
  rcases units_zmod3_eq_one_or_neg_one (Additive.toMul (Quotient.out x)) with h | h
  · left
    rw [hx, h]
    rw [squareClass_eq_zero_iff]
    exact ⟨1, by simp⟩
  · right
    rw [hx, h]

open Classical in
private noncomputable def signVal (b : SquareClassGroup (ZMod 3)) : ℤˣ :=
  if b = 0 then 1 else -1

private theorem signOf_eq_signVal (x : RegularFormClass (ZMod 3)) :
    signOf x = signVal (RegularFormClass.signedDiscr x) := rfl

private theorem signVal_zero : signVal 0 = 1 := by simp [signVal]

private theorem signVal_sqNegOne : signVal (squareClass (-1 : (ZMod 3)ˣ)) = -1 := by
  classical
  change (if squareClass (-1 : (ZMod 3)ˣ) = 0 then (1 : ℤˣ) else -1) = -1
  rw [if_neg sqNegOne_ne_zero]

private theorem signVal_add (a b : SquareClassGroup (ZMod 3)) :
    signVal (a + b) = signVal a * signVal b := by
  rcases sqClass_zmod3_eq_zero_or_sqNegOne a with rfl | rfl <;>
    rcases sqClass_zmod3_eq_zero_or_sqNegOne b with rfl | rfl <;>
    simp [signVal_zero, signVal_sqNegOne, sqNegOne_add_self]

private theorem signVal_squareClass (u : (ZMod 3)ˣ) : signVal (squareClass u) = toSign u := by
  rcases units_zmod3_eq_one_or_neg_one u with rfl | rfl
  · rw [show squareClass (1 : (ZMod 3)ˣ) = 0 by
        rw [squareClass_eq_zero_iff]; exact ⟨1, by simp⟩]
    rw [signVal_zero, toSign_one]
  · rw [signVal_sqNegOne, toSign_neg_one]

private theorem signVal_nsmul_sqNegOne (k : ℕ) :
    signVal (k • squareClass (-1 : (ZMod 3)ˣ)) = (-1 : ℤˣ) ^ k := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow]
    obtain ⟨m, rfl⟩ := hk
    rw [← two_mul m, mul_nsmul, two_nsmul, sqNegOne_add_self, nsmul_zero, signVal_zero]
  · rw [hk.neg_one_pow]
    obtain ⟨m, rfl⟩ := hk
    rw [add_nsmul, one_nsmul, mul_nsmul, two_nsmul, sqNegOne_add_self, nsmul_zero, zero_add,
      signVal_sqNegOne]

private theorem choose_two_mod_two_eq_div_two_mod_two (r : ℕ) :
    r.choose 2 % 2 = r / 2 % 2 := by
  have hchoose : Nat.choose 2 2 = 1 := by decide
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more r ih =>
      have h1 : (r + 2).choose 2 = r.choose 2 + 1 + 2 * r := by
        rw [Nat.add_choose_two r 2, hchoose]; ring
      have h2 : (r + 2) / 2 = r / 2 + 1 := by omega
      rw [h1, h2]
      omega

private theorem even_choose_two_iff_even_div_two (r : ℕ) :
    Even (r.choose 2) ↔ Even (r / 2) := by
  rw [Nat.even_iff, Nat.even_iff, choose_two_mod_two_eq_div_two_mod_two r]

theorem signOf_eq_one_iff (x : RegularFormClass (ZMod 3)) :
    signOf x = 1 ↔ RegularFormClass.signedDiscr x = 0 := by
  rw [signOf]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h1 => absurd h1 (by decide : (-1 : ℤˣ) ≠ 1), fun h0 => absurd h0 h⟩

theorem signOf_zero : signOf (0 : RegularFormClass (ZMod 3)) = 1 := by
  rw [signOf_eq_one_iff, RegularFormClass.signedDiscr_zero]

theorem signOf_add (x y : RegularFormClass (ZMod 3)) :
    signOf (x + y) = signOf x * signOf y * (-1) ^ (x.rank * y.rank) := by
  simp only [signOf_eq_signVal]
  rw [RegularFormClass.signedDiscr_add, signVal_add, signVal_add, signVal_nsmul_sqNegOne]
  ac_rfl

theorem signOf_mk_diag {r : ℕ} (w : Fin r → (ZMod 3)ˣ) :
    signOf (Quotient.mk (regularFormSetoid (ZMod 3)) ⟨r, w⟩) =
      (∏ i, toSign (w i)) * (-1) ^ (r / 2) := by
  simp only [signOf_eq_signVal]
  rw [RegularFormClass.signedDiscr_mk, signVal_add, signVal_nsmul_sqNegOne, signVal_squareClass,
    map_prod toSign w Finset.univ, neg_one_pow_congr (even_choose_two_iff_even_div_two r)]
  ac_rfl

private theorem signOf_mk_one (d : (ZMod 3)ˣ) : signOf (mk_one d) = toSign d := by
  have h := signOf_mk_diag (r := 1) (fun _ : Fin 1 => d)
  simpa using h

private theorem signOf_one : signOf (1 : RegularFormClass (ZMod 3)) = 1 := by
  conv_lhs => rw [← RegularFormClass.mk_rankOne_one]
  exact (signOf_mk_one 1).trans toSign_one

private theorem rank_nsmul_one (m : ℕ) :
    (m • (1 : RegularFormClass (ZMod 3))).rank = m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [add_nsmul, one_nsmul, RegularFormClass.rank_add, ih, RegularFormClass.rank_one]

private theorem signOf_nsmul_one (m : ℕ) :
    signOf (m • (1 : RegularFormClass (ZMod 3))) = (-1 : ℤˣ) ^ (m.choose 2) := by
  induction m with
  | zero =>
      rw [zero_nsmul, signOf_zero, Nat.choose_eq_zero_of_lt (by norm_num : 0 < 2), pow_zero]
  | succ m ih =>
      rw [add_nsmul, one_nsmul, signOf_add, ih, signOf_one, rank_nsmul_one,
        RegularFormClass.rank_one, mul_one]
      rw [Nat.add_choose_two m 1, show (1 : ℕ).choose 2 = 0 by decide, Nat.mul_one, add_zero,
        ← pow_add]

private theorem signOf_normal_form (m : ℕ) (d : (ZMod 3)ˣ) :
    signOf (m • (1 : RegularFormClass (ZMod 3)) + mk_one d) =
      (-1 : ℤˣ) ^ (m.choose 2) * toSign d * (-1 : ℤˣ) ^ m := by
  rw [signOf_add, signOf_nsmul_one, signOf_mk_one, rank_nsmul_one, RegularFormClass.rank_mk,
    mul_one]

theorem eq_of_rank_eq_of_signOf_eq {x y : RegularFormClass (ZMod 3)} (hr : x.rank = y.rank)
    (hs : signOf x = signOf y) : x = y := by
  rcases Nat.eq_zero_or_pos x.rank with h0 | hpos
  · have hx0 : x = 0 := RegularFormClass.rank_eq_zero_iff.mp h0
    have hy0 : y = 0 := RegularFormClass.rank_eq_zero_iff.mp (by rw [← hr]; exact h0)
    rw [hx0, hy0]
  · obtain ⟨d, hd⟩ := exists_normal_form x (by omega)
    obtain ⟨d', hd'⟩ := exists_normal_form y (by rw [← hr]; omega)
    have hd_eq : d = d' := by
      have h := hs
      rw [hd, hd'] at h
      simp only [signOf_normal_form] at h
      rw [hr] at h
      exact toSign_injective (mul_left_cancel (mul_right_cancel h))
    rw [hd, hd', hd_eq, hr]

theorem exists_weights_of_sign (r : ℕ) (α : ℤˣ) (h : r = 0 → α = 1) :
    ∃ w : Fin r → (ZMod 3)ˣ, (∏ i, toSign (w i)) * (-1) ^ (r / 2) = α := by
  rcases r with _ | k
  · refine ⟨Fin.elim0, ?_⟩
    simp [h rfl]
  · obtain ⟨u, hu⟩ := toSign_surjective (α * (-1) ^ ((k + 1) / 2))
    refine ⟨Fin.cons u (fun _ => 1), ?_⟩
    have hsq : ((-1 : ℤˣ) ^ ((k + 1) / 2)) * ((-1 : ℤˣ) ^ ((k + 1) / 2)) = 1 := by
      rw [← pow_add, show (k + 1) / 2 + (k + 1) / 2 = 2 * ((k + 1) / 2) by ring, pow_mul]
      norm_num
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, toSign_one, Finset.prod_const_one, mul_one]
    rw [hu, mul_assoc, hsq, mul_one]

end CFSG.OddStandard.SmallF3.Omega
