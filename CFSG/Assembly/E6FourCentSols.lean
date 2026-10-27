module

public import CFSG.Assembly.E6FourCentRoots

public section

namespace CFSG.Assembly

open CFSG.Blueprint.Chevalley CFSG.Assembly.E6FourCentChk CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Lattice


private lemma e6SolVec_one (n : ℕ) : e6SolVec n 1 = ((n % 5 : ℕ) : ZMod 5) := rfl

private lemma e6SolVec_two (n : ℕ) : e6SolVec n 2 = ((n / 5 % 5 : ℕ) : ZMod 5) := rfl

private lemma e6SolVec_three (n : ℕ) : e6SolVec n 3 = ((n / 25 % 5 : ℕ) : ZMod 5) := rfl

private lemma e6SolVec_four (n : ℕ) : e6SolVec n 4 = ((n / 125 % 5 : ℕ) : ZMod 5) := rfl

private lemma e6SolVec_zero (n : ℕ) :
    e6SolVec n 0 =
      2 * (e6SolVec n 1 + 2 * e6SolVec n 2 + 2 * e6SolVec n 3 + e6SolVec n 4) := by
  rw [e6SolVec_one, e6SolVec_two, e6SolVec_three, e6SolVec_four]
  change (((2 * (n % 5 + 2 * (n / 5 % 5) + 2 * (n / 25 % 5) + n / 125 % 5)) % 5 : ℕ) :
      ZMod 5) = 2 * (((n % 5 : ℕ) : ZMod 5) + 2 * ((n / 5 % 5 : ℕ) : ZMod 5) +
        2 * ((n / 25 % 5 : ℕ) : ZMod 5) + ((n / 125 % 5 : ℕ) : ZMod 5))
  conv_lhs => rw [ZMod.natCast_mod]
  push_cast
  ring

private lemma e6SolVec_five (n : ℕ) :
    e6SolVec n 5 =
      2 * (e6SolVec n 1 + e6SolVec n 2 + 2 * e6SolVec n 3 + 2 * e6SolVec n 4) := by
  rw [e6SolVec_one, e6SolVec_two, e6SolVec_three, e6SolVec_four]
  change (((2 * (n % 5 + n / 5 % 5 + 2 * (n / 25 % 5) + 2 * (n / 125 % 5))) % 5 : ℕ) :
      ZMod 5) = 2 * (((n % 5 : ℕ) : ZMod 5) + ((n / 5 % 5 : ℕ) : ZMod 5) +
        2 * ((n / 25 % 5 : ℕ) : ZMod 5) + 2 * ((n / 125 % 5 : ℕ) : ZMod 5))
  conv_lhs => rw [ZMod.natCast_mod]
  push_cast
  ring

private lemma e6FourIsSol_fin6 (v : Fin 6 → ZMod 5)
    (h0 : v 0 = 2 * (v 1 + 2 * v 2 + 2 * v 3 + v 4))
    (h5 : v 5 = 2 * (v 1 + v 2 + 2 * v 3 + 2 * v 4)) :
    ∀ j : Fin 6, ∑ i : Fin 6, ((toMat 6 e6TwoMat i j : ℤ) : ZMod 5) * v i = - v j := by
  intro j
  have h5e : (5 : ZMod 5) = 0 := by decide
  fin_cases j <;>
    simp [toMat, lget, e6TwoMat, Fin.sum_univ_six] <;>
    first
      | linear_combination 2 * h0 + (v 1 + 2 * v 2 + 2 * v 3 + v 4) * h5e
      | linear_combination 2 * h5 + (v 1 + v 2 + 2 * v 3 + 2 * v 4) * h5e
      | ring

private lemma e6FourIsSol_of_zero_five (v : Fin Tag.E6.rank → ZMod 5)
    (h0 : v 0 = 2 * (v 1 + 2 * v 2 + 2 * v 3 + v 4))
    (h5 : v 5 = 2 * (v 1 + v 2 + 2 * v 3 + 2 * v 4)) :
    E6FourIsSol v := by
  intro j
  rw [e6Two_wordMat]
  exact e6FourIsSol_fin6 v h0 h5 j

private lemma e6FourIsSol_zero (v : Fin 6 → ZMod 5)
    (hv : ∀ j : Fin 6, ∑ i : Fin 6, ((toMat 6 e6TwoMat i j : ℤ) : ZMod 5) * v i = - v j) :
    v 0 = 2 * (v 1 + 2 * v 2 + 2 * v 3 + v 4) := by
  have h := hv 0
  simp [toMat, lget, e6TwoMat, Fin.sum_univ_six] at h
  have h5e : (5 : ZMod 5) = 0 := by decide
  have h' : 2 * v 0 + (v 1 + 2 * v 2 + 2 * v 3 + v 4) = 0 := by linear_combination h
  linear_combination 3 * h' - (v 0 + v 1 + 2 * v 2 + 2 * v 3 + v 4) * h5e

private lemma e6FourIsSol_five (v : Fin 6 → ZMod 5)
    (hv : ∀ j : Fin 6, ∑ i : Fin 6, ((toMat 6 e6TwoMat i j : ℤ) : ZMod 5) * v i = - v j) :
    v 5 = 2 * (v 1 + v 2 + 2 * v 3 + 2 * v 4) := by
  have h := hv 5
  simp [toMat, lget, e6TwoMat, Fin.sum_univ_six] at h
  have h5e : (5 : ZMod 5) = 0 := by decide
  have h' : 2 * v 5 + (v 1 + v 2 + 2 * v 3 + 2 * v 4) = 0 := by linear_combination h
  linear_combination 3 * h' - (v 5 + v 1 + v 2 + 2 * v 3 + 2 * v 4) * h5e

private lemma zmod5_natCast_eq_zero {m : ℕ} (hm : m < 5) (h : (m : ZMod 5) = 0) : m = 0 :=
  Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff m 5).mp h) hm

private lemma zmod5_digit_eq {m m' : ℕ} (hm : m < 5) (hm' : m' < 5)
    (h : (m : ZMod 5) = (m' : ZMod 5)) : m = m' := by
  have := (ZMod.natCast_eq_natCast_iff' m m' 5).mp h
  simpa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hm'] using this

private lemma sol_witness_spec (a b c d : ℕ) (ha : a < 5) (hb : b < 5) (hc : c < 5)
    (hd : d < 5) :
    a + 5 * b + 25 * c + 125 * d < 625 ∧
    (a + 5 * b + 25 * c + 125 * d) % 5 = a ∧
    (a + 5 * b + 25 * c + 125 * d) / 5 % 5 = b ∧
    (a + 5 * b + 25 * c + 125 * d) / 25 % 5 = c ∧
    (a + 5 * b + 25 * c + 125 * d) / 125 % 5 = d := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma testBit_one_shiftLeft (k j : ℕ) : ((1 : ℕ) <<< k).testBit j = true ↔ j = k := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff]
  exact eq_comm

private lemma foldr_testBit (l : List ℕ) (P : ℕ → Prop) [DecidablePred P] (j : ℕ) :
    ((l.foldr (fun k acc => if P k then acc ||| (1 <<< k) else acc) 0).testBit j = true) ↔
      (j ∈ l ∧ P j) := by
  induction l with
  | nil => simp
  | cons k l ih =>
    rw [List.foldr_cons, List.mem_cons]
    by_cases hk : P k
    · rw [if_pos hk, Nat.testBit_or, Bool.or_eq_true, ih, testBit_one_shiftLeft]
      constructor
      · rintro (⟨hjl, hPj⟩ | hjk)
        · exact ⟨Or.inr hjl, hPj⟩
        · subst hjk
          exact ⟨Or.inl rfl, hk⟩
      · rintro ⟨rfl | hjl, hPj⟩
        · right; rfl
        · left; exact ⟨hjl, hPj⟩
    · rw [if_neg hk, ih]
      constructor
      · intro h
        exact ⟨Or.inr h.1, h.2⟩
      · rintro ⟨hjk | hjl, hPj⟩
        · subst hjk
          exact absurd hPj hk
        · exact ⟨hjl, hPj⟩

private lemma rts5Lit_eq :
    rts5Lit = rtsLit.map (fun l => l.map fun z => (z % (5 : ℤ)).toNat) := by
  decide +kernel

private lemma intCast_eq_toNat_emod (z : ℤ) (n : ℕ) [NeZero n] :
    ((z : ZMod n)) = (((z % (n : ℤ)).toNat : ℕ) : ZMod n) := by
  have hb : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h1 : (((z % (n : ℤ)).toNat : ℕ) : ZMod n) =
      ((((z % (n : ℤ)).toNat : ℕ) : ℤ) : ZMod n) := by
    push_cast
    rfl
  rw [h1, Int.toNat_of_nonneg (Int.emod_nonneg z hb), ← ZMod.intCast_mod z n]

private lemma rts5Lit_getD_map (k : ℕ) :
    rts5Lit.getD k [] = (rtsLit.getD k []).map (fun z => (z % (5 : ℤ)).toNat) := by
  rw [rts5Lit_eq]
  show (rtsLit.map (fun l => l.map fun z => (z % (5 : ℤ)).toNat)).getD k
      ((fun l => l.map fun z => (z % (5 : ℤ)).toNat) []) = _
  rw [List.getD_map]

private lemma getD_map_mod5 (l : List ℤ) (i : ℕ) :
    (l.map (fun z => (z % (5 : ℤ)).toNat)).getD i 0 =
      ((l.getD i 0 % (5 : ℤ)).toNat) := by
  change (l.map (fun z => (z % (5 : ℤ)).toNat)).getD i
      ((fun z => (z % (5 : ℤ)).toNat) 0) = _
  rw [List.getD_map]

private def pairNatBot (n k : ℕ) : ℕ :=
  ∑ i : Fin Tag.E6.rank,
    (e6SolCoords n).getD (i:ℕ) 0 * (rts5Lit.getD k []).getD (i:ℕ) 0

private def pairNat (n k : ℕ) : ℕ := pairNatBot n k % 5

private lemma e6Pair_eq_pairNatBot (n k : ℕ) (hk : k < 72) :
    e6Pair (e6SolVec n) (e6RootVec k) = ((pairNatBot n k : ℕ) : ZMod 5) := by
  rw [e6Pair, pairNatBot, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [e6SolVec]
  have hr : ((e6RootVec k i : ℤ) : ZMod 5) =
      (((rts5Lit.getD k []).getD (i : ℕ) 0 : ℕ) : ZMod 5) := by
    rw [e6RootVec, rts5Lit_getD_map (k := k), getD_map_mod5]
    exact intCast_eq_toNat_emod _ 5
  rw [hr, ← Nat.cast_mul]

private lemma e6Pair_eq_zero_iff_pairNat (n k : ℕ) (hk : k < 72) :
    e6Pair (e6SolVec n) (e6RootVec k) = 0 ↔ pairNat n k = 0 := by
  rw [e6Pair_eq_pairNatBot n k hk, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  simp [pairNat]

private lemma foldr_congr_list : ∀ (l : List ℕ) (f g : ℕ → ℕ → ℕ) (init : ℕ),
    (∀ k ∈ l, f k = g k) → l.foldr f init = l.foldr g init
  | [], f, g, init, _ => rfl
  | a :: l, f, g, init, h => by
      rw [List.foldr_cons, List.foldr_cons, h a (by simp),
        foldr_congr_list l f g _ (fun k hk => h k (by simp [hk]))]

private def maskNat (n : ℕ) : ℕ :=
  (List.range 72).foldr
    (fun k acc => if pairNat n k = 0 then acc ||| (1 <<< k) else acc) 0

private lemma e6SolMask_eq_maskNat (n : ℕ) :
    e6SolMask (e6SolVec n) = maskNat n := by
  rw [e6SolMask, maskNat]
  apply foldr_congr_list
  intro k hk
  have hk' : k < 72 := by simpa using hk
  funext acc
  by_cases h : e6Pair (e6SolVec n) (e6RootVec k) = 0
  · rw [if_pos h, if_pos ((e6Pair_eq_zero_iff_pairNat n k hk').mp h)]
  · rw [if_neg h, if_neg (fun hq => h ((e6Pair_eq_zero_iff_pairNat n k hk').mpr hq))]

private theorem sigsLit_eq_map_maskNat :
    sigsLit = (List.range' 1 624).map maskNat := by
  decide +kernel

theorem e6SolVec_isSol (n : ℕ) : E6FourIsSol (e6SolVec n) := by
  refine e6FourIsSol_of_zero_five _ (e6SolVec_zero n) (e6SolVec_five n)

theorem e6SolVec_ne_zero {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 624) : e6SolVec n ≠ 0 := by
  intro h
  have hd1 : n % 5 = 0 := by
    refine zmod5_natCast_eq_zero (Nat.mod_lt _ (by norm_num)) ?_
    have := congrFun h 1
    simpa [e6SolVec_one] using this
  have hd2 : n / 5 % 5 = 0 := by
    refine zmod5_natCast_eq_zero (Nat.mod_lt _ (by norm_num)) ?_
    have := congrFun h 2
    simpa [e6SolVec_two] using this
  have hd3 : n / 25 % 5 = 0 := by
    refine zmod5_natCast_eq_zero (Nat.mod_lt _ (by norm_num)) ?_
    have := congrFun h 3
    simpa [e6SolVec_three] using this
  have hd4 : n / 125 % 5 = 0 := by
    refine zmod5_natCast_eq_zero (Nat.mod_lt _ (by norm_num)) ?_
    have := congrFun h 4
    simpa [e6SolVec_four] using this
  omega

theorem e6SolVec_injOn {n n' : ℕ} (hn : n < 625) (hn' : n' < 625)
    (h : e6SolVec n = e6SolVec n') : n = n' := by
  have hd1 : n % 5 = n' % 5 := by
    refine zmod5_digit_eq (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) ?_
    have := congrFun h 1
    simpa [e6SolVec_one] using this
  have hd2 : n / 5 % 5 = n' / 5 % 5 := by
    refine zmod5_digit_eq (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) ?_
    have := congrFun h 2
    simpa [e6SolVec_two] using this
  have hd3 : n / 25 % 5 = n' / 25 % 5 := by
    refine zmod5_digit_eq (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) ?_
    have := congrFun h 3
    simpa [e6SolVec_three] using this
  have hd4 : n / 125 % 5 = n' / 125 % 5 := by
    refine zmod5_digit_eq (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) ?_
    have := congrFun h 4
    simpa [e6SolVec_four] using this
  omega

theorem exists_e6SolVec {v : Fin Tag.E6.rank → ZMod 5} (hv : E6FourIsSol v) :
    ∃ n, n < 625 ∧ e6SolVec n = v := by
  have hv6 : ∀ j : Fin 6, ∑ i : Fin 6, ((toMat 6 e6TwoMat i j : ℤ) : ZMod 5) * v i = - v j := by
    intro j
    have h := hv j
    rw [e6Two_wordMat] at h
    exact h
  have h0 := e6FourIsSol_zero v hv6
  have h5 := e6FourIsSol_five v hv6
  have hspec := sol_witness_spec (v 1).val (v 2).val (v 3).val (v 4).val
    (ZMod.val_lt (v 1)) (ZMod.val_lt (v 2)) (ZMod.val_lt (v 3)) (ZMod.val_lt (v 4))
  obtain ⟨hn, hd1, hd2, hd3, hd4⟩ := hspec
  refine ⟨(v 1).val + 5 * (v 2).val + 25 * (v 3).val + 125 * (v 4).val, hn, ?_⟩
  have h1 : e6SolVec ((v 1).val + 5 * (v 2).val + 25 * (v 3).val + 125 * (v 4).val) 1 = v 1 := by
    rw [e6SolVec_one, hd1, ZMod.natCast_zmod_val]
  have h2 : e6SolVec ((v 1).val + 5 * (v 2).val + 25 * (v 3).val + 125 * (v 4).val) 2 = v 2 := by
    rw [e6SolVec_two, hd2, ZMod.natCast_zmod_val]
  have h3 : e6SolVec ((v 1).val + 5 * (v 2).val + 25 * (v 3).val + 125 * (v 4).val) 3 = v 3 := by
    rw [e6SolVec_three, hd3, ZMod.natCast_zmod_val]
  have h4 : e6SolVec ((v 1).val + 5 * (v 2).val + 25 * (v 3).val + 125 * (v 4).val) 4 = v 4 := by
    rw [e6SolVec_four, hd4, ZMod.natCast_zmod_val]
  have hz0 : e6SolVec ((v 1).val + 5 * (v 2).val + 25 * (v 3).val + 125 * (v 4).val) 0 = v 0 := by
    rw [e6SolVec_zero, h1, h2, h3, h4]
    exact h0.symm
  have hz5 : e6SolVec ((v 1).val + 5 * (v 2).val + 25 * (v 3).val + 125 * (v 4).val) 5 = v 5 := by
    rw [e6SolVec_five, h1, h2, h3, h4]
    exact h5.symm
  funext i
  fin_cases i
  · exact hz0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact hz5

theorem testBit_e6SolMask (v : Fin Tag.E6.rank → ZMod 5) {j : ℕ} (hj : j < 72) :
    (e6SolMask v).testBit j = true ↔ e6Pair v (e6RootVec j) = 0 := by
  rw [e6SolMask, foldr_testBit]
  simp [List.mem_range, hj]

theorem e6SolMask_lt (v : Fin Tag.E6.rank → ZMod 5) : e6SolMask v < 2 ^ 72 := by
  refine Nat.lt_pow_two_of_testBit (e6SolMask v) (fun i hi => ?_)
  have hb : (e6SolMask v).testBit i ≠ true := by
    intro h
    rw [e6SolMask, foldr_testBit] at h
    simp only [List.mem_range] at h
    omega
  cases hbit : (e6SolMask v).testBit i with
  | false => rfl
  | true => exact absurd hbit hb

theorem e6MaskRoots_solMask (v : Fin Tag.E6.rank → ZMod 5) :
    e6MaskRoots (e6SolMask v) = {γ | IsRoot Tag.E6 γ ∧ e6Pair v γ = 0} := by
  ext γ
  constructor
  · rintro ⟨k, hk, hbit, rfl⟩
    exact ⟨isRoot_e6RootVec hk, (testBit_e6SolMask v hk).mp hbit⟩
  · rintro ⟨hroot, hpair⟩
    obtain ⟨k, hk, rfl⟩ := exists_e6RootVec hroot
    exact ⟨k, hk, (testBit_e6SolMask v hk).mpr hpair, rfl⟩

theorem sigsLit_eq :
    sigsLit = (List.range' 1 624).map fun n => e6SolMask (e6SolVec n) := by
  rw [sigsLit_eq_map_maskNat]
  apply List.map_congr_left
  intro n _
  exact (e6SolMask_eq_maskNat n).symm

end CFSG.Assembly

end
