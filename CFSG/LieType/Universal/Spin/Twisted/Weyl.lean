module

public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LieType.Universal.Spin.PlusCT.Basic

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CoxeterSystem

section Signs

variable {m : ℕ}

theorem longWeylBool_true_false (i j k : Fin m) (r : Bool) :
    longWeylBool i j true false k r = r := by
  unfold longWeylBool
  split_ifs <;> cases r <;> rfl

theorem boolSign_shortWeylBool (i k : Fin m) (r : Bool) :
    boolSign (shortWeylBool i k r) = (if k = i then -1 else 1) * boolSign r := by
  unfold shortWeylBool
  split_ifs <;> simp

theorem stdReflB_add' (k : Fin m) (e e' : Fin m → ℤ) :
    stdReflB m k (e + e') = stdReflB m k e + stdReflB m k e' := by
  by_cases h : k.val + 1 < m
  · rw [stdReflB_of_lt m h, stdReflB_of_lt m h, stdReflB_of_lt m h]
    rfl
  · rw [stdReflB_of_not_lt m h, stdReflB_of_not_lt m h, stdReflB_of_not_lt m h]
    funext a
    simp only [Pi.add_apply]
    ring

theorem stdReflB_single_of_lt {k : Fin m} (h : k.val + 1 < m) (i : Fin m) (x : ℤ) :
    stdReflB m k (Pi.single i x) = Pi.single (Equiv.swap k ⟨k.val + 1, h⟩ i) x := by
  rw [stdReflB_of_lt m h, Pi.single_comp_equiv, Equiv.symm_swap]

theorem stdReflB_single_of_not_lt {k : Fin m} (h : ¬k.val + 1 < m) (i : Fin m) (s : Bool) :
    stdReflB m k (Pi.single i (boolSign s)) = Pi.single i (boolSign (shortWeylBool k i s)) := by
  rw [stdReflB_of_not_lt m h, boolSign_shortWeylBool]
  funext a
  by_cases ha : a = i
  · subst ha
    simp
  · simp [ha]

end Signs

variable (n : ℕ) {K : Type*} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem toStdB_reflection_long_of_lt {k : Fin (n - 1)} (hk : k.val + 1 < n - 1)
    {γ : Fin (n - 1) → ℤ} {i j : Fin (n - 1)} {s t : Bool}
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    toStdB (n - 1) (reflection (cartanB (n - 1)) k γ) =
      Pi.single (Equiv.swap k ⟨k.val + 1, hk⟩ i)
          (boolSign (longWeylBool k ⟨k.val + 1, hk⟩ true false i s)) +
        Pi.single (Equiv.swap k ⟨k.val + 1, hk⟩ j)
          (boolSign (longWeylBool k ⟨k.val + 1, hk⟩ true false j t)) := by
  rw [toStdB_reflection, h, stdReflB_add', stdReflB_single_of_lt hk,
    stdReflB_single_of_lt hk, longWeylBool_true_false, longWeylBool_true_false]

theorem toStdB_reflection_long_of_not_lt {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1)
    {γ : Fin (n - 1) → ℤ} {i j : Fin (n - 1)} {s t : Bool}
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    toStdB (n - 1) (reflection (cartanB (n - 1)) k γ) =
      Pi.single i (boolSign (shortWeylBool k i s)) +
        Pi.single j (boolSign (shortWeylBool k j t)) := by
  rw [toStdB_reflection, h, stdReflB_add', stdReflB_single_of_not_lt hk,
    stdReflB_single_of_not_lt hk]

theorem toStdB_reflection_short_of_lt {k : Fin (n - 1)} (hk : k.val + 1 < n - 1)
    {γ : Fin (n - 1) → ℤ} {i : Fin (n - 1)} {s : Bool}
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s)) :
    toStdB (n - 1) (reflection (cartanB (n - 1)) k γ) =
      Pi.single (Equiv.swap k ⟨k.val + 1, hk⟩ i)
        (boolSign (longWeylBool k ⟨k.val + 1, hk⟩ true false i s)) := by
  rw [toStdB_reflection, h, stdReflB_single_of_lt hk, longWeylBool_true_false]

theorem toStdB_reflection_short_of_not_lt {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1)
    {γ : Fin (n - 1) → ℤ} {i : Fin (n - 1)} {s : Bool}
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s)) :
    toStdB (n - 1) (reflection (cartanB (n - 1)) k γ) =
      Pi.single i (boolSign (shortWeylBool k i s)) := by
  rw [toStdB_reflection, h, stdReflB_single_of_not_lt hk]

theorem minusDatum_n_mem (i : Fin (n - 1)) :
    minusWeyl n hirr i ∈ rankOne (minusRootGroup n hirr) i := by
  by_cases hi : i.val + 1 < n - 1
  · rw [minusWeyl_of_lt n hirr hi, rankOne_minusRootGroup_of_lt n hirr hi]
    exact ⟨weylSL2 1, rfl⟩
  · rw [minusWeyl_of_not_lt n hirr hi, rankOne_minusRootGroup_of_not_lt n hirr hi]
    exact shortWeyl_mem n hirr i

theorem minusDatum_H_le (i : Fin (n - 1)) :
    minusTorus n hirr i ≤ rankOne (minusRootGroup n hirr) i := by
  by_cases hi : i.val + 1 < n - 1
  · rw [minusTorus_of_lt n hirr hi, rankOne_minusRootGroup_of_lt n hirr hi]
    rintro _ ⟨τ, rfl⟩
    exact ⟨diagSL2 τ, rfl⟩
  · rw [minusTorus_of_not_lt n hirr hi, rankOne_minusRootGroup_of_not_lt n hirr hi]
    exact shortTorus_le n hirr i

theorem minusDatum_sq_mem (i : Fin (n - 1)) : minusWeyl n hirr i ^ 2 ∈ minusTorus n hirr i := by
  by_cases hi : i.val + 1 < n - 1
  · rw [minusWeyl_of_lt n hirr hi, minusTorus_of_lt n hirr hi]
    exact ⟨-1, by rw [pow_two, HypFrame.longWeyl_mul_self]⟩
  · rw [minusWeyl_of_not_lt n hirr hi, minusTorus_of_not_lt n hirr hi]
    exact shortWeyl_sq_mem n hirr i

theorem minusDatum_conj_mem (k : Fin (n - 1)) (γ : Fin (n - 1) → ℤ)
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (x : spinGroup (quadMinus n K b c))
    (hx : x ∈ minusRootGroup n hirr γ) :
    minusWeyl n hirr k * x * (minusWeyl n hirr k)⁻¹ ∈ minusRootGroup n hirr
      (weylAction (isFiniteType_cartanB (n - 1))
        ((coxeterMatrix (isFiniteType_cartanB (n - 1))).toCoxeterSystem.simple k) γ) := by
  rw [weylAction_simple]
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
  · obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ').mp hx
    by_cases hk : k.val + 1 < n - 1
    · rw [minusWeyl_of_lt n hirr hk, HypFrame.longWeyl_conj_longRoot]
      exact longRoot_mem_minusRootGroup n hirr _ _ _ (toStdB_reflection_long_of_lt n hk hγ') _
    · rw [minusWeyl_of_not_lt n hirr hk, shortWeyl_conj_longRoot]
      exact longRoot_mem_minusRootGroup n hirr _ _ _ (toStdB_reflection_long_of_not_lt n hk hγ') _
  · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ').mp hx
    by_cases hk : k.val + 1 < n - 1
    · rw [minusWeyl_of_lt n hirr hk, longWeyl_conj_twShortRoot]
      exact twShortRoot_mem_minusRootGroup n hirr _ _ (toStdB_reflection_short_of_lt n hk hγ') _
    · rw [minusWeyl_of_not_lt n hirr hk, shortWeyl_conj_twShortRoot]
      exact twShortRoot_mem_minusRootGroup n hirr _ _ (toStdB_reflection_short_of_not_lt n hk hγ') _

private theorem coxeterMatrix_cartanB_apply (i j : Fin (n - 1)) :
    coxeterMatrix (isFiniteType_cartanB (n - 1)) i j =
      TauCeti.coxeterOrder (cartanB (n - 1) i j * cartanB (n - 1) j i) :=
  TauCeti.coxeterMatrixOfCartanMatrix_apply _ _ _ i j

private def LongAdj (i j : Fin (n - 1)) : Prop :=
  (i.val + 1 = j.val ∧ j.val + 1 < n - 1) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n - 1)

private def ShortAdj (i j : Fin (n - 1)) : Prop :=
  (i.val + 2 = n - 1 ∧ j.val + 1 = n - 1) ∨ (j.val + 2 = n - 1 ∧ i.val + 1 = n - 1)

private theorem coxeterMatrix_cartanB_of_longAdj {i j : Fin (n - 1)} (hij : i ≠ j)
    (h : LongAdj n i j) : coxeterMatrix (isFiniteType_cartanB (n - 1)) i j = 3 := by
  have h1 : cartanB (n - 1) i j = -1 := by
    simp only [cartanB, Matrix.of_apply, ite_eq_right hij]
    unfold LongAdj at h
    split_ifs <;> omega
  have h2 : cartanB (n - 1) j i = -1 := by
    simp only [cartanB, Matrix.of_apply, ite_eq_right (Ne.symm hij)]
    unfold LongAdj at h
    split_ifs <;> omega
  rw [coxeterMatrix_cartanB_apply, h1, h2, show (-1 : ℤ) * -1 = 1 by norm_num,
    TauCeti.coxeterOrder_one]

private theorem coxeterMatrix_cartanB_of_shortAdj {i j : Fin (n - 1)} (hij : i ≠ j)
    (h : ShortAdj n i j) : coxeterMatrix (isFiniteType_cartanB (n - 1)) i j = 4 := by
  have h12 : cartanB (n - 1) i j * cartanB (n - 1) j i = 2 := by
    simp only [cartanB, Matrix.of_apply, ite_eq_right hij, ite_eq_right (Ne.symm hij)]
    unfold ShortAdj at h
    split_ifs <;> omega
  rw [coxeterMatrix_cartanB_apply, h12, TauCeti.coxeterOrder_two]

private theorem coxeterMatrix_cartanB_of_not_adj {i j : Fin (n - 1)} (hij : i ≠ j)
    (h1 : ¬LongAdj n i j) (h2 : ¬ShortAdj n i j) :
    coxeterMatrix (isFiniteType_cartanB (n - 1)) i j = 2 := by
  have h0 : cartanB (n - 1) i j = 0 := by
    simp only [cartanB, Matrix.of_apply, ite_eq_right hij]
    unfold LongAdj at h1
    unfold ShortAdj at h2
    split_ifs <;> omega
  rw [coxeterMatrix_cartanB_apply, h0, zero_mul, TauCeti.coxeterOrder_zero]

private theorem minusWeyl_braid_long {k l : Fin (n - 1)} (hkl : k.val + 1 = l.val)
    (hl : l.val + 1 < n - 1) :
    minusWeyl n hirr k * minusWeyl n hirr l * minusWeyl n hirr k =
      minusWeyl n hirr l * minusWeyl n hirr k * minusWeyl n hirr l := by
  have hk : k.val + 1 < n - 1 := by omega
  have h1 : k ≠ l := Fin.ne_of_val_ne (by omega)
  have h3 : k ≠ (⟨l.val + 1, hl⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp; omega)
  obtain rfl : l = ⟨k.val + 1, hk⟩ := Fin.ext hkl.symm
  rw [minusWeyl_of_lt n hirr hk, minusWeyl_of_lt n hirr hl]
  exact (minusFrame n b c).longWeyl_braid' (succ_ne_of_lt n hk) (succ_ne_of_lt n hl) h3 true false
    false

private theorem minusWeyl_braid_short {k l : Fin (n - 1)} (hk : k.val + 2 = n - 1)
    (hl : l.val + 1 = n - 1) :
    minusWeyl n hirr k * minusWeyl n hirr l * minusWeyl n hirr k * minusWeyl n hirr l =
      minusWeyl n hirr l * minusWeyl n hirr k * minusWeyl n hirr l * minusWeyl n hirr k := by
  have hk' : k.val + 1 < n - 1 := by omega
  obtain rfl : l = ⟨k.val + 1, hk'⟩ := Fin.ext (by simp only; omega)
  rw [minusWeyl_of_lt n hirr hk', minusWeyl_of_not_lt n hirr (by simp only; omega),
    shortWeyl_eq_minusFrame n hirr]
  exact (minusFrame n b c).longWeyl_shortWeyl_braid (succ_ne_of_lt n hk') true false

private theorem minusWeyl_commute {k l : Fin (n - 1)} (hkl : k ≠ l) (h1 : ¬LongAdj n k l)
    (h2 : ¬ShortAdj n k l) : Commute (minusWeyl n hirr k) (minusWeyl n hirr l) := by
  unfold LongAdj at h1
  unfold ShortAdj at h2
  have hkl' : k.val ≠ l.val := fun h => hkl (Fin.ext h)
  have mixed : ∀ {a d : Fin (n - 1)} (ha : a.val + 1 < n - 1) (hd : ¬d.val + 1 < n - 1),
      a.val + 1 ≠ d.val → Commute (minusWeyl n hirr a) (minusWeyl n hirr d) := by
    intro a d ha hb hab
    rw [minusWeyl_of_lt n hirr ha, minusWeyl_of_not_lt n hirr hb, shortWeyl_eq_minusFrame n hirr]
    exact (minusFrame n b c).commute_longWeyl_shortWeyl_of_ne (succ_ne_of_lt n ha)
      (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by simp; omega)) true false true
  by_cases hk : k.val + 1 < n - 1
  · by_cases hl : l.val + 1 < n - 1
    · rw [minusWeyl_of_lt n hirr hk, minusWeyl_of_lt n hirr hl]
      exact (minusFrame n b c).commute_longWeyl_longWeyl_of_disjoint (succ_ne_of_lt n hk)
        (succ_ne_of_lt n hl) hkl (Fin.ne_of_val_ne (by simp; omega))
        (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega)) true false true
        false
    · exact mixed hk hl (by omega)
  · by_cases hl : l.val + 1 < n - 1
    · exact (mixed hl hk (by omega)).symm
    · exact absurd (Fin.ext (by omega)) hkl

theorem minusDatum_braid (i j : Fin (n - 1)) :
    ((braidWord (coxeterMatrix (isFiniteType_cartanB (n - 1))) i j).map
        (minusWeyl n hirr)).prod =
      ((braidWord (coxeterMatrix (isFiniteType_cartanB (n - 1))) j i).map
        (minusWeyl n hirr)).prod := by
  by_cases hij : i = j
  · rw [hij]
  have hsymm := (coxeterMatrix (isFiniteType_cartanB (n - 1))).symmetric j i
  rw [braidWord, braidWord, hsymm]
  by_cases hL : LongAdj n i j
  · rw [show (coxeterMatrix (isFiniteType_cartanB (n - 1))).M i j = 3 from
      coxeterMatrix_cartanB_of_longAdj n hij hL]
    show ([j, i, j].map (minusWeyl n hirr)).prod = ([i, j, i].map (minusWeyl n hirr)).prod
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc]
    rcases hL with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (minusWeyl_braid_long n hirr h1 h2).symm
    · exact minusWeyl_braid_long n hirr h1 h2
  by_cases hS : ShortAdj n i j
  · rw [show (coxeterMatrix (isFiniteType_cartanB (n - 1))).M i j = 4 from
      coxeterMatrix_cartanB_of_shortAdj n hij hS]
    show ([i, j, i, j].map (minusWeyl n hirr)).prod = ([j, i, j, i].map (minusWeyl n hirr)).prod
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc]
    rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact minusWeyl_braid_short n hirr h1 h2
    · exact (minusWeyl_braid_short n hirr h1 h2).symm
  · rw [show (coxeterMatrix (isFiniteType_cartanB (n - 1))).M i j = 2 from
      coxeterMatrix_cartanB_of_not_adj n hij hL hS]
    show ([i, j].map (minusWeyl n hirr)).prod = ([j, i].map (minusWeyl n hirr)).prod
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (minusWeyl_commute n hirr hij hL hS).eq

theorem shortTorusElt_conj_twShortRoot (k : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0)
    (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) :
    shortTorusElt n hirr k a * twShortRoot n hirr i s (.ofAdd p) * (shortTorusElt n hirr k a)⁻¹ =
      twShortRoot n hirr i s
        (.ofAdd (shortTorusScalar n b c k a i s • planeRefl b c a (planeRefl b c planeOne p))) :=
  conj_twShortRoot n hirr _ i s (spinAction_shortTorusElt_minusVec n hirr k ha i s)
    (spinAction_shortTorusElt_planeVec n hirr k ha p)

theorem minusDatum_H_conj_mem [Finite K] (k : Fin (n - 1)) (γ : Fin (n - 1) → ℤ)
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (h : spinGroup (quadMinus n K b c))
    (hh : h ∈ minusTorus n hirr k) (x : spinGroup (quadMinus n K b c))
    (hx : x ∈ minusRootGroup n hirr γ) : h * x * h⁻¹ ∈ minusRootGroup n hirr γ := by
  by_cases hk : k.val + 1 < n - 1
  · rw [minusTorus_of_lt n hirr hk] at hh
    obtain ⟨τ, rfl⟩ := hh
    rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
    · obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ').mp hx
      rw [HypFrame.longTorus_conj_longRoot]
      exact longRoot_mem_minusRootGroup n hirr hij s t hγ' _
    · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ').mp hx
      rw [longTorus_conj_twShortRoot]
      exact twShortRoot_mem_minusRootGroup n hirr i s hγ' _
  · rw [minusTorus_of_not_lt n hirr hk] at hh
    obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr k).mp hh
    rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
    · obtain ⟨y, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ').mp hx
      rw [shortTorusElt_conj_longRoot n hirr k ha]
      exact longRoot_mem_minusRootGroup n hirr hij s t hγ' _
    · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ').mp hx
      rw [shortTorusElt_conj_twShortRoot n hirr k ha]
      exact twShortRoot_mem_minusRootGroup n hirr i s hγ' _

theorem shortTorusScalar_not (k : Fin (n - 1)) (a : Fin 2 → K) (m : Fin (n - 1)) (r : Bool) :
    shortTorusScalar n b c k a m (!r) = (shortTorusScalar n b c k a m r)⁻¹ := by
  unfold shortTorusScalar
  split_ifs <;> cases r <;> simp_all

include hirr in
theorem shortTorusScalar_ne_zero (k : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) (m : Fin (n - 1))
    (r : Bool) : shortTorusScalar n b c k a m r ≠ 0 := by
  have hN := planeNorm_ne_zero hirr ha
  unfold shortTorusScalar
  split_ifs <;> simp [hN]

private theorem minusWeyl_conj_of_lt {j : Fin (n - 1)} (hj : j.val + 1 < n - 1)
    (h : spinGroup (quadMinus n K b c)) (l : Kˣ)
    (hU : ∀ x : K, h * (minusFrame n b c).longRoot (succ_ne_of_lt n hj) true false (.ofAdd x) *
      h⁻¹ = (minusFrame n b c).longRoot (succ_ne_of_lt n hj) true false (.ofAdd ((l : K) * x)))
    (hL : ∀ x : K, h * (minusFrame n b c).longRoot (succ_ne_of_lt n hj).symm true false
      (.ofAdd x) * h⁻¹ = (minusFrame n b c).longRoot (succ_ne_of_lt n hj).symm true false
        (.ofAdd (((l⁻¹ : Kˣ) : K) * x))) :
    minusWeyl n hirr j * h * (minusWeyl n hirr j)⁻¹ ∈ minusTorus n hirr j ⊔ Subgroup.zpowers h := by
  rw [minusWeyl_of_lt n hirr hj, minusTorus_of_lt n hirr hj, HypFrame.longWeyl,
    weylSL2_conj_of_conj ((minusFrame n b c).longSL2 (succ_ne_of_lt n hj) true false) h l
      (fun x => by rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2, hU])
      (fun x => by rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_lowerSL2]; exact hL x)]
  exact mul_mem (Subgroup.mem_sup_left ⟨l⁻¹, rfl⟩) (Subgroup.mem_sup_right
    (Subgroup.mem_zpowers h))

theorem minusDatum_conj_H_mem [Finite K] (j k : Fin (n - 1)) (h : spinGroup (quadMinus n K b c))
    (hh : h ∈ minusTorus n hirr k) :
    minusWeyl n hirr j * h * (minusWeyl n hirr j)⁻¹ ∈
      minusTorus n hirr j ⊔ minusTorus n hirr k := by
  have hzp : Subgroup.zpowers h ≤ minusTorus n hirr k := (Subgroup.zpowers_le).mpr hh
  by_cases hj : j.val + 1 < n - 1
  · refine (sup_le_sup_left hzp _) ?_
    by_cases hk : k.val + 1 < n - 1
    · rw [minusTorus_of_lt n hirr hk] at hh
      obtain ⟨τ, rfl⟩ := hh
      have hjj : (⟨j.val + 1, hj⟩ : Fin (n - 1)) ≠ j := (succ_ne_of_lt n hj).symm
      refine minusWeyl_conj_of_lt n hirr hj _
        (τ ^ (longCoroot k ⟨k.val + 1, hk⟩ true false j true +
          longCoroot k ⟨k.val + 1, hk⟩ true false ⟨j.val + 1, hj⟩ false)) (fun x => ?_)
        (fun x => ?_)
      · rw [HypFrame.longTorus_conj_longRoot]
      · rw [HypFrame.longTorus_conj_longRoot, ← zpow_neg]
        congr 4
        rw [neg_add, ← longCoroot_not, ← longCoroot_not, Bool.not_true, Bool.not_false,
          add_comm]
    · rw [minusTorus_of_not_lt n hirr hk] at hh
      obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr k).mp hh
      set l := shortTorusScalar n b c k a j true *
        shortTorusScalar n b c k a ⟨j.val + 1, hj⟩ false
      have hl : l ≠ 0 := mul_ne_zero (shortTorusScalar_ne_zero n hirr k ha _ _)
        (shortTorusScalar_ne_zero n hirr k ha _ _)
      refine minusWeyl_conj_of_lt n hirr hj _ (Units.mk0 l hl) (fun x => ?_) (fun x => ?_)
      · rw [shortTorusElt_conj_longRoot n hirr k ha]
        rfl
      · rw [shortTorusElt_conj_longRoot n hirr k ha]
        congr 2
        rw [Units.val_inv_eq_inv_val, Units.val_mk0]
        have h1 := shortTorusScalar_not n (b := b) (c := c) k a ⟨j.val + 1, hj⟩ false
        have h2 := shortTorusScalar_not n (b := b) (c := c) k a j true
        rw [Bool.not_false] at h1
        rw [Bool.not_true] at h2
        rw [h1, h2, mul_inv, mul_comm (shortTorusScalar n b c k a ⟨j.val + 1, hj⟩ false)⁻¹]
  · rw [minusWeyl_of_not_lt n hirr hj, minusTorus_of_not_lt n hirr hj]
    by_cases hk : k.val + 1 < n - 1
    · rw [minusTorus_of_lt n hirr hk] at hh ⊢
      obtain ⟨τ, rfl⟩ := hh
      set e := longCoroot k ⟨k.val + 1, hk⟩ true false j true
      rw [shortWeyl_eq_minusFrame n hirr, OddFrame.shortWeyl,
        weylSL2_conj_of_conj ((minusFrame n b c).shortSL2 j true) _ (τ ^ e)
          (fun x => by rw [OddFrame.shortSL2_upperSL2, OddFrame.shortSL2_upperSL2,
            OddFrame.longTorus_conj_shortRoot])
          (fun x => by
            rw [OddFrame.shortSL2_lowerSL2, OddFrame.shortSL2_lowerSL2,
              OddFrame.longTorus_conj_shortRoot, longCoroot_not, zpow_neg, mul_neg]),
        ← OddFrame.shortTorus_apply, minusFrame_shortTorus_eq n hirr]
      refine mul_mem (Subgroup.mem_sup_left (shortTorusElt_mem n hirr j ?_))
        (Subgroup.mem_sup_right ⟨τ, rfl⟩)
      exact smul_ne_zero (Units.ne_zero _) planeOne_ne_zero
    · have hjk : j = k := Fin.ext (by omega)
      subst hjk
      rw [minusTorus_of_not_lt n hirr hk] at hh
      exact Subgroup.mem_sup_left (shortWeyl_conj_mem_shortTorus n hirr j hh)

theorem minusDatum_le_rankOne (i : Fin (n - 1)) (γ : Fin (n - 1) → ℤ)
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (hsupp : ∀ k, k ≠ i → γ k = 0) :
    minusRootGroup n hirr γ ≤ rankOne (minusRootGroup n hirr) i := by
  obtain ⟨x, rfl⟩ : ∃ x : ℤ, γ = x • Pi.single i 1 := by
    refine ⟨γ i, funext fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hsupp k hk, hk]
  have hval : toStdB (n - 1) (x • Pi.single i 1) i = x := by
    rw [toStdB_smul, Pi.smul_apply]
    by_cases hi : i.val + 1 < n - 1
    · rw [toStdB_single_of_lt' n hi, PlusCT.single_add_single_apply_left (succ_ne_of_lt n hi),
        boolSign_true, smul_eq_mul, mul_one]
    · rw [toStdB_single_of_not_lt' n hi, Pi.single_eq_same, boolSign_true, smul_eq_mul, mul_one]
  have hmem : x = 0 ∨ x = 1 ∨ x = -1 := by
    rw [← hval]
    rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨p, q, hpq, s, t, hγ'⟩ | ⟨p, s, hγ'⟩
    · rw [hγ']
      exact PlusCT.single_add_single_apply_mem hpq s t i
    · rw [hγ', Pi.single_apply]
      split_ifs
      · rcases boolSign_eq_one_or_eq_neg_one s with h | h <;> simp [h]
      · simp
  have hne : x ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hγ
    rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨p, q, hpq, s, t, hγ'⟩ | ⟨p, s, hγ'⟩
    · have h1 := congrFun hγ' p
      rw [toStdB_zero, Pi.zero_apply, PlusCT.single_add_single_apply_left hpq] at h1
      exact boolSign_ne_zero s h1.symm
    · have h1 := congrFun hγ' p
      rw [toStdB_zero, Pi.zero_apply, Pi.single_eq_same] at h1
      exact boolSign_ne_zero s h1.symm
  rcases hmem with h | h | h
  · exact absurd h hne
  · rw [h, one_smul]
    exact le_sup_left
  · rw [h, neg_one_zsmul]
    exact le_sup_right

end CFSG.LieType.Universal.Spin.Twisted
