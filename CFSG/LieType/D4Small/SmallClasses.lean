module

public import CFSG.LieType.D4Small.Orbits
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LieType.D4Small

open Matrix

attribute [local instance] Classical.propDecidable

private theorem isUnit_two_zmod {N : ℕ} (hN : Odd N) : IsUnit (2 : ZMod N) := by
  rw [show (2 : ZMod N) = ((2 : ℕ) : ZMod N) by norm_num, ZMod.isUnit_iff_coprime 2 N]
  exact Nat.coprime_two_left.mpr hN
private theorem two_mul_ne_zero {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b) : (2
    : ZMod N) * b ≠ 0 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  exact ((isUnit_two_zmod hN).mul hb).ne_zero
private theorem four_mul_ne_zero {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b) :
    (4 : ZMod N) * b ≠ 0 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have h : (4 : ZMod N) * b = ((2 : ZMod N) * 2) * b := by norm_num
  rw [h]
  exact ((isUnit_two_zmod hN).mul (isUnit_two_zmod hN)).mul hb |>.ne_zero
private theorem three_mul_ne_pm {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b) : (3
    : ZMod N) * b ≠ b ∧ (3 : ZMod N) * b ≠ -b := by
  constructor
  · intro h
    apply two_mul_ne_zero hN3 hN hb
    have h' : (2 : ZMod N) * b = (3 : ZMod N) * b - (1 : ZMod N) * b := by ring
    rw [h', h, one_mul, sub_self]
  · intro h
    apply four_mul_ne_zero hN3 hN hb
    have h' : (4 : ZMod N) * b = (3 : ZMod N) * b + b := by ring
    rw [h', h, neg_add_cancel]
private theorem add_sign_mul_ne_zero {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b)
    {s u : ℤ} (hs : s = 1 ∨ s = -1) (hu : u = 1 ∨ u = -1) (hsu : s + u ≠ 0) : ((s + u : ℤ) : ZMod N)
    * b ≠ 0 := by
  rcases hs with rfl | rfl
  · rcases hu with rfl | rfl
    · simpa using two_mul_ne_zero hN3 hN hb
    · exact absurd rfl hsu
  · rcases hu with rfl | rfl
    · exact absurd rfl hsu
    · simpa using two_mul_ne_zero hN3 hN hb
private theorem eq_neg_of_sign_add_eq_zero {s u : ℤ} (hs : s = 1 ∨ s = -1) (hu : u = 1 ∨ u = -1) (h
    : s + u = 0) : u = -s := by
  rcases hs with rfl | rfl <;> rcases hu with rfl | rfl <;> omega
private theorem sign_mul_ne_zero {N : ℕ} {b : ZMod N} (hb : b ≠ 0) {t : ℤ} (ht : t = 1 ∨ t = -1) :
    (t : ZMod N) * b ≠ 0 := by
  rcases ht with rfl | rfl <;> simpa using hb
private theorem mul_sign_ne_zero {N : ℕ} {b : ZMod N} (hb : b ≠ 0) {t : ℤ} (ht : t = 1 ∨ t = -1) : b
    * (t : ZMod N) ≠ 0 := by
  rcases ht with rfl | rfl <;> simpa using hb
private theorem neg_sign {t : ℤ} (ht : t = 1 ∨ t = -1) : -t = 1 ∨ -t = -1 := by
  rcases ht with rfl | rfl <;> norm_num
private theorem not_isVWt_of_two {N : ℕ} {b : ZMod N} (hb : b ≠ 0)
    {x : Fin 4 → ZMod N} {r₁ r₂ : Fin 4} (h₁₂ : r₁ ≠ r₂) (h₁ : x r₁ ≠ 0)
    (h₂ : x r₂ ≠ 0) : ¬ IsVWt b x :=
  fun hx => h₁₂ (isVWt_apply_ne_zero hb hx h₁ h₂)
private theorem mul_two_sign_ne_zero {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b)
    {t : ℤ} (ht : t = 1 ∨ t = -1) : b * ((2 * t : ℤ) : ZMod N) ≠ 0 := by
  have h2b : (2 : ZMod N) * b ≠ 0 := two_mul_ne_zero hN3 hN hb
  have h : b * ((2 * t : ℤ) : ZMod N) = (t : ZMod N) * ((2 : ZMod N) * b) := by
    push_cast
    ring
  rw [h]
  exact sign_mul_ne_zero h2b ht
private theorem three_sign_mul_ne_pm {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b)
    {u : ℤ} (hu : u = 1 ∨ u = -1) : (3 : ZMod N) * (u : ZMod N) * b ≠ b ∧ (3 : ZMod N) * (u : ZMod
    N) * b ≠ -b := by
  rcases hu with rfl | rfl
  · simpa using three_mul_ne_pm hN3 hN hb
  · constructor
    · intro h
      apply (three_mul_ne_pm hN3 hN hb).2
      linear_combination -h
    · intro h
      apply (three_mul_ne_pm hN3 hN hb).1
      linear_combination -h
private theorem sWt_key_coord {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b) {x :
    ZMod N} (hx : x = b ∨ x = -b) {u : ℤ} (hu : u = 1 ∨ u = -1) (hy : x + (2 * b) * (u : ZMod N) = b
    ∨ x + (2 * b) * (u : ZMod N) = -b) : x = ((-u : ℤ) : ZMod N) * b := by
  rcases hu with rfl | rfl
  · rcases hx with rfl | rfl
    · exfalso
      simp only [Int.cast_one, mul_one] at hy
      rcases hy with h | h
      · apply (three_mul_ne_pm hN3 hN hb).1
        linear_combination h
      · apply (three_mul_ne_pm hN3 hN hb).2
        linear_combination h
    · simp
  · rcases hx with rfl | rfl
    · simp
    · exfalso
      simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one] at hy
      rcases hy with h | h
      · apply (three_mul_ne_pm hN3 hN hb).2
        linear_combination -h
      · apply (three_mul_ne_pm hN3 hN hb).1
        linear_combination -h
private theorem sWt_sub_two_coord {N : ℕ} (b : ZMod N) (a : Fin 4 → ZMod N) {p q : Fin 4} (hpq : p ≠
    q) (r : Fin 4) (u v : ℤ) : (a - (2 * b) • castW N (Pi.single p u + Pi.single q v)) r = (if r = p
    then a p - (2 * b) * (u : ZMod N) else if r = q then a q - (2 * b) * (v : ZMod N) else a r)
    := by
  rw [castW_add, castW_single, castW_single]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Pi.sub_apply]
  split_ifs <;> simp_all <;> ring
private theorem sWt_add_two_coord {N : ℕ} (b : ZMod N) (a : Fin 4 → ZMod N) {p q : Fin 4} (hpq : p ≠
    q) (r : Fin 4) (u v : ℤ) : (a + (2 * b) • castW N (Pi.single p u + Pi.single q v)) r = (if r = p
    then a p + (2 * b) * (u : ZMod N) else if r = q then a q + (2 * b) * (v : ZMod N) else a r)
    := by
  rw [castW_add, castW_single, castW_single]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all <;> ring
private theorem root_apply_left {r t : Fin 4} (hrt : r ≠ t) (s w : ℤ) : (Pi.single r s + Pi.single t
    w : Fin 4 → ℤ) r = s := by
  simp [hrt]
private theorem root_apply_right {r t : Fin 4} (hrt : r ≠ t) (s w : ℤ) : (Pi.single r s + Pi.single
    t w : Fin 4 → ℤ) t = w := by
  simp [Ne.symm hrt]
private theorem root_apply_of_ne {r t k : Fin 4} (hkr : k ≠ r) (hkt : k ≠ t) (s w : ℤ) : (Pi.single
    r s + Pi.single t w : Fin 4 → ℤ) k = 0 := by
  simp [hkr, hkt]
private theorem root_coord_trichotomy {α : Fin 4 → ℤ} (hα : IsD4Root α) (k : Fin 4) : α k = -1 ∨ α k
    = 0 ∨ α k = 1 := by
  have h := hα.abs_apply_le_one k
  rw [abs_le] at h
  omega
private theorem exists_sign_eq {N : ℕ} {b x : ZMod N} (h : x = b ∨ x = -b) : ∃ s : ℤ, (s = 1 ∨ s =
    -1) ∧ x = (s : ZMod N) * b := by
  rcases h with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simp⟩
  · exact ⟨-1, Or.inr rfl, by simp⟩
private theorem eq_neg_of_ne_of_sign {N : ℕ} (hN : Odd N) {b x y : ZMod N} (hb : b ≠ 0) (hx : x = b
    ∨ x = -b) (hy : y = b ∨ y = -b) (hne : x ≠ y) : y = -x := by
  have hbne : b ≠ -b := ZMod.ne_neg_self hN hb
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
private theorem sWt_flip_self_ne {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0) {u : ℤ} (hu : u = 1
    ∨ u = -1) : ((-u : ℤ) : ZMod N) * b ≠ ((-u : ℤ) : ZMod N) * b + (2 * b) * (u : ZMod N) := by
  rcases hu with rfl | rfl
  · change ((-1 : ℤ) : ZMod N) * b ≠
      ((-1 : ℤ) : ZMod N) * b + (2 * b) * ((1 : ℤ) : ZMod N)
    rw [show ((-1 : ℤ) : ZMod N) * b + (2 * b) * ((1 : ℤ) : ZMod N) = b by
      norm_num
      ring]
    simpa using (ZMod.ne_neg_self hN hb).symm
  · change ((1 : ℤ) : ZMod N) * b ≠
      ((1 : ℤ) : ZMod N) * b + (2 * b) * ((-1 : ℤ) : ZMod N)
    rw [show ((1 : ℤ) : ZMod N) * b + (2 * b) * ((-1 : ℤ) : ZMod N) = -b by
      norm_num
      ring]
    simpa using ZMod.ne_neg_self hN hb

private def vWt (N : ℕ) (b : ZMod N) (i : Fin 4) (s : ℤ) : Fin 4 → ZMod N :=
  Pi.single i ((s : ZMod N) * b)
private theorem isVWt_iff_exists_vWt {N : ℕ} {b : ZMod N} {a : Fin 4 → ZMod N} : IsVWt b a ↔ ∃ i s,
    (s = 1 ∨ s = -1) ∧ a = vWt N b i s := by
  constructor
  · rintro ⟨i, h | h⟩
    · exact ⟨i, 1, Or.inl rfl, by rw [h]; simp [vWt]⟩
    · exact ⟨i, -1, Or.inr rfl, by rw [h]; simp [vWt]⟩
  · rintro ⟨i, s, hs, rfl⟩
    rcases hs with rfl | rfl
    · exact ⟨i, Or.inl (by simp [vWt])⟩
    · exact ⟨i, Or.inr (by simp [vWt])⟩
private theorem vWt_add_coord3 {N : ℕ} (b : ZMod N) (i p q c r : Fin 4) (s u v w : ℤ) : (vWt N b i s
    + b • castW N (Pi.single p u + Pi.single q v + Pi.single c w)) r = (if r = i then (s : ZMod N) *
    b else 0) + (if r = p then b * (u : ZMod N) else 0) + (if r = q then b * (v : ZMod N) else 0) +
    (if r = c then b * (w : ZMod N) else 0) := by
  rw [vWt, castW_add, castW_add, castW_single, castW_single, castW_single]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring
private theorem vWt_neg {N : ℕ} (b : ZMod N) (i : Fin 4) (s : ℤ) : vWt N b i (-s) = -vWt N b i s
    := by
  rw [vWt, vWt, show ((-s : ℤ) : ZMod N) = -((s : ℤ) : ZMod N) by simp, neg_mul]
  exact Pi.single_neg (f := fun _ : Fin 4 => ZMod N) i ((s : ZMod N) * b)
private theorem vWt_add_single {N : ℕ} (b : ZMod N) (i : Fin 4) (s u : ℤ) : vWt N b i s + b • castW
    N (Pi.single i u) = Pi.single i (((s + u : ℤ) : ZMod N) * b) := by
  rw [castW_single, vWt]
  funext r
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring
private theorem vWt_add_coord {N : ℕ} (b : ZMod N) (i p q r : Fin 4) (s u v : ℤ) : (vWt N b i s + b
    • castW N (Pi.single p u + Pi.single q v)) r = (if r = i then (s : ZMod N) * b else 0) + (if r =
    p then b * (u : ZMod N) else 0) + (if r = q then b * (v : ZMod N) else 0) := by
  rw [vWt, castW_add, castW_single, castW_single]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring
private theorem vWt_add_eq_single {N : ℕ} {b : ZMod N} {i k : Fin 4} (hki : k ≠ i) {s t : ℤ} : vWt N
    b i s + b • castW N (Pi.single i (-s) + Pi.single k t) = Pi.single k ((t : ZMod N) * b) := by
  funext r
  rw [vWt_add_coord]
  by_cases hri : r = i
  · subst r
    rw [if_pos rfl, if_pos rfl, if_neg (Ne.symm hki), Pi.single_apply]
    simp [Ne.symm hki]
    ring
  · by_cases hrk : r = k
    · subst r
      rw [if_neg hri, if_neg hri, if_pos rfl, Pi.single_eq_same]
      ring
    · rw [if_neg hri, if_neg hri, if_neg hrk, Pi.single_apply]
      simp [hri, hrk]

private noncomputable def vClass (N : ℕ) [NeZero N] (b : ZMod N) : Finset (Fin 4 → ZMod N) :=
  Finset.univ.filter fun a => IsVWt b a
private theorem mem_vClass {N : ℕ} [NeZero N] {b : ZMod N} {a : Fin 4 → ZMod N} : a ∈ vClass N b ↔
    IsVWt b a := by
  simp [vClass]
private theorem mem_vClass_iff {N : ℕ} [NeZero N] {b : ZMod N} {a : Fin 4 → ZMod N} : a ∈ vClass N b
    ↔ ∃ i s, (s = 1 ∨ s = -1) ∧ a = vWt N b i s := by
  rw [mem_vClass, isVWt_iff_exists_vWt]

private noncomputable def sClass (N : ℕ) [NeZero N] (b : ZMod N) (e : ℕ) :
    Finset (Fin 4 → ZMod N) :=
  Finset.univ.filter fun a => IsSWt b a ∧ negCount b a % 2 = e
private theorem mem_sClass {N : ℕ} [NeZero N] {b : ZMod N} {e : ℕ} {a : Fin 4 → ZMod N} : a ∈ sClass
    N b e ↔ IsSWt b a ∧ negCount b a % 2 = e := by
  simp [sClass]
private theorem isVWt_vWt_add_p {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {i q : Fin 4} (hiq : i ≠ q) {s u v : ℤ} (hs : s = 1 ∨ s = -1) (hu : u = 1 ∨ u = -1)
    (hv : v = 1 ∨ v = -1) (hw : IsVWt b (vWt N b i s + b • castW N (Pi.single i u + Pi.single q v)))
    : ∃ k : Fin 4, k ≠ i ∧ ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ Pi.single i u + Pi.single q v = Pi.single i
    (-s) + (Pi.single k t : Fin 4 → ℤ) := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hb0 : b ≠ 0 := hb.ne_zero
  by_cases hsu : s + u = 0
  · exact ⟨q, Ne.symm hiq, v, hv, by rw [eq_neg_of_sign_add_eq_zero hs hu hsu]⟩
  · exfalso
    have hwi : (vWt N b i s + b • castW N (Pi.single i u + Pi.single q v)) i =
        ((s + u : ℤ) : ZMod N) * b := by
      rw [vWt_add_coord]
      simp [hiq]
      push_cast
      ring
    have hwq : (vWt N b i s + b • castW N (Pi.single i u + Pi.single q v)) q =
        (v : ZMod N) * b := by
      rw [vWt_add_coord]
      simp [hiq, Ne.symm hiq]
      ring
    have hwi_ne :
        (vWt N b i s + b • castW N (Pi.single i u + Pi.single q v)) i ≠ 0 := by
      rw [hwi]
      exact add_sign_mul_ne_zero hN3 hN hb hs hu hsu
    have hwq_ne :
        (vWt N b i s + b • castW N (Pi.single i u + Pi.single q v)) q ≠ 0 := by
      rw [hwq]
      exact sign_mul_ne_zero hb0 hv
    exact hiq (isVWt_apply_ne_zero hb0 hw hwi_ne hwq_ne)
private theorem isVWt_vWt_add_q {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {p i : Fin 4} (hpi : p ≠ i) {s u v : ℤ} (hs : s = 1 ∨ s = -1) (hu : u = 1 ∨ u = -1)
    (hv : v = 1 ∨ v = -1) (hw : IsVWt b (vWt N b i s + b • castW N (Pi.single p u + Pi.single i v)))
    : ∃ k : Fin 4, k ≠ i ∧ ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ Pi.single p u + Pi.single i v = Pi.single i
    (-s) + (Pi.single k t : Fin 4 → ℤ) := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hb0 : b ≠ 0 := hb.ne_zero
  by_cases hsv : s + v = 0
  · exact ⟨p, hpi, u, hu, by rw [eq_neg_of_sign_add_eq_zero hs hv hsv, add_comm]⟩
  · exfalso
    have hwi : (vWt N b i s + b • castW N (Pi.single p u + Pi.single i v)) i =
        ((s + v : ℤ) : ZMod N) * b := by
      rw [vWt_add_coord]
      simp [Ne.symm hpi]
      push_cast
      ring
    have hwp : (vWt N b i s + b • castW N (Pi.single p u + Pi.single i v)) p =
        (u : ZMod N) * b := by
      rw [vWt_add_coord]
      simp [hpi]
      ring
    have hwi_ne :
        (vWt N b i s + b • castW N (Pi.single p u + Pi.single i v)) i ≠ 0 := by
      rw [hwi]
      exact add_sign_mul_ne_zero hN3 hN hb hs hv hsv
    have hwp_ne :
        (vWt N b i s + b • castW N (Pi.single p u + Pi.single i v)) p ≠ 0 := by
      rw [hwp]
      exact sign_mul_ne_zero hb0 hu
    exact hpi (isVWt_apply_ne_zero hb0 hw hwp_ne hwi_ne)
private theorem isVWt_vWt_add_ne {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {p q i : Fin 4} (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q) {s u v : ℤ} (hs : s = 1 ∨ s
    = -1) (hu : u = 1 ∨ u = -1) (hw : IsVWt b (vWt N b i s + b • castW N (Pi.single p u + Pi.single
    q v))) : False := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hb0 : b ≠ 0 := hb.ne_zero
  have hwi : (vWt N b i s + b • castW N (Pi.single p u + Pi.single q v)) i =
      (s : ZMod N) * b := by
    rw [vWt_add_coord]
    simp [hip, hiq]
  have hwp : (vWt N b i s + b • castW N (Pi.single p u + Pi.single q v)) p =
      b * (u : ZMod N) := by
    rw [vWt_add_coord]
    simp [Ne.symm hip, hpq]
  have hwi_ne :
      (vWt N b i s + b • castW N (Pi.single p u + Pi.single q v)) i ≠ 0 := by
    rw [hwi]
    exact sign_mul_ne_zero hb0 hs
  have hwp_ne :
      (vWt N b i s + b • castW N (Pi.single p u + Pi.single q v)) p ≠ 0 := by
    rw [hwp]
    exact mul_sign_ne_zero hb0 hu
  exact hip (isVWt_apply_ne_zero hb0 hw hwi_ne hwp_ne)
private theorem isVWt_vWt_add {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {i : Fin 4} {s : ℤ} (hs : s = 1 ∨ s = -1) {γ : Fin 4 → ℤ} (hγ : IsD4Root γ) : IsVWt b
    (vWt N b i s + b • castW N γ) ↔ ∃ k : Fin 4, k ≠ i ∧ ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ γ = Pi.single i
    (-s) + Pi.single k t := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  constructor
  · intro hw
    obtain ⟨p, q, hpq, hup, hvp, hγeq⟩ := isD4Root_iff.mp hγ
    let u : ℤ := γ p
    let v : ℤ := γ q
    have hu : u = 1 ∨ u = -1 := by simpa [u] using hup
    have hv : v = 1 ∨ v = -1 := by simpa [v] using hvp
    have hγeq' : γ = Pi.single p u + Pi.single q v := by rw [hγeq]
    rw [hγeq'] at hw ⊢
    by_cases hip : i = p
    · subst p
      exact isVWt_vWt_add_p hN3 hN hb hpq hs hu hv hw
    · by_cases hiq : i = q
      · subst q
        exact isVWt_vWt_add_q hN3 hN hb hpq hs hu hv hw
      · exfalso
        exact isVWt_vWt_add_ne hN3 hN hb hip hiq hpq hs hu hw
  · rintro ⟨k, hki, t, ht, rfl⟩
    rw [vWt_add_eq_single hki]
    rcases ht with rfl | rfl
    · exact ⟨k, Or.inl (by simp)⟩
    · exact ⟨k, Or.inr (by simp)⟩
private theorem vClass_card_eq {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) : (vClass N b).card = 8 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  exact card_filter_isVWt hN hb.ne_zero
private theorem vClass_neg_mem {N : ℕ} [NeZero N] {b : ZMod N} {a : Fin 4 → ZMod N} (ha : a ∈ vClass
    N b) : -a ∈ vClass N b := by
  rw [mem_vClass] at ha ⊢
  rcases ha with ⟨i, h | h⟩
  · refine ⟨i, Or.inr ?_⟩
    rw [h]
    simpa using (Pi.single_neg (f := fun _ : Fin 4 => ZMod N) i b).symm
  · refine ⟨i, Or.inl ?_⟩
    rw [h]
    simpa using (Pi.single_neg (f := fun _ : Fin 4 => ZMod N) i (-b)).symm
private theorem vClass_reflW_mem {N : ℕ} [NeZero N] {b : ZMod N} {β : Fin 4 → ℤ} (hβ : IsD4Root β)
    {a : Fin 4 → ZMod N} (ha : a ∈ vClass N b) : reflW β a ∈ vClass N b := by
  rw [mem_vClass] at ha ⊢
  exact isVWt_reflW hβ ha
private theorem vClass_step {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) {b : ZMod N} (hb : IsUnit b) {a : Fin 4
    → ZMod N} (ha : a ∈ vClass N b) {α : Fin 4 → ℤ} (hα : IsD4Root α) {k : ZMod N} (hk : k ≠ 0) (hC
    : a + k • castW N α ∈ vClass N b) : k = b ∨ k = -b := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_vClass] at ha hC
  exact step_eq_of_isVWt hα hk hb.ne_zero ha rfl hC
private theorem vClass_sub_not_mem {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {a : Fin 4 → ZMod N} (ha : a ∈ vClass N b) {α : Fin 4 → ℤ} (hα : IsD4Root α) (hC : a +
    b • castW N α ∈ vClass N b) : a - b • castW N α ∉ vClass N b := by
  obtain ⟨i, s, hs, rfl⟩ := mem_vClass_iff.mp ha
  rw [mem_vClass] at hC
  obtain ⟨k, hki, t, ht, hαeq⟩ := (isVWt_vWt_add hN3 hN hb hs hα).mp hC
  rw [mem_vClass]
  intro hsub
  have hsub' : IsVWt b (vWt N b i s + b • castW N (-α)) := by
    simpa [sub_eq_add_neg, ← smul_neg, ← castW_neg] using hsub
  obtain ⟨k', hk'i, t', ht', hα'⟩ :=
    (isVWt_vWt_add hN3 hN hb hs hα.neg).mp hsub'
  have h1 : (-α) i = -s := by rw [hα']; simp [Ne.symm hk'i]
  have h2 : α i = -s := by rw [hαeq]; simp [Ne.symm hki]
  have hseq : s = -s := by
    calc s = -(-s) := by ring
      _ = -(α i) := by rw [h2]
      _ = (-α) i := by simp
      _ = -s := h1
  rcases hs with rfl | rfl <;> norm_num at hseq
private theorem vClass_reflW_eq {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {a : Fin 4 → ZMod N} (ha : a ∈ vClass N b) {α : Fin 4 → ℤ} (hα : IsD4Root α) (hC : a +
    b • castW N α ∈ vClass N b) : reflW α a = a + b • castW N α := by
  obtain ⟨i, s, hs, rfl⟩ := mem_vClass_iff.mp ha
  rw [mem_vClass] at hC
  obtain ⟨k, hki, t, ht, hαeq⟩ := (isVWt_vWt_add hN3 hN hb hs hα).mp hC
  have hdot : vWt N b i s ⬝ᵥ castW N α = -b := by
    rw [hαeq, castW_add, castW_single, castW_single, vWt, dotProduct_add,
      dotProduct_single, dotProduct_single]
    simp only [Pi.single_apply]
    simp [hki]
    rcases hs with rfl | rfl <;> ring
  rw [reflW, hdot, neg_smul, sub_neg_eq_add]
private theorem vClass_adj {N : ℕ} [NeZero N] {b : ZMod N} {a a' : Fin 4 → ZMod N} (ha : a ∈ vClass
    N b) (ha' : a' ∈ vClass N b) (hne : a' ≠ a) (hneg : a' ≠ -a) : ∃ γ, IsD4Root γ ∧ a' = a + b •
    castW N γ := by
  obtain ⟨i, s, hs, rfl⟩ := mem_vClass_iff.mp ha
  obtain ⟨k, t, ht, rfl⟩ := mem_vClass_iff.mp ha'
  have hki : k ≠ i := by
    intro h
    subst k
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact hne rfl
    · exact hneg (by simpa using vWt_neg b i 1)
    · exact hneg (by simpa using vWt_neg b i (-1))
    · exact hne rfl
  refine ⟨Pi.single i (-s) + Pi.single k t, ?_, ?_⟩
  · exact isD4Root_single_add_single (i := i) (j := k) (Ne.symm hki)
      (by rcases hs with rfl | rfl <;> norm_num) ht
  · rw [vWt_add_eq_single hki]
    rfl
private theorem vClass_ne_neg {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) {b : ZMod N} (hb : IsUnit b) {a : Fin
    4 → ZMod N} (ha : a ∈ vClass N b) {γ : Fin 4 → ℤ} (hγ : IsD4Root γ) : a + b • castW N γ ≠ -a
    := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨i, s, hs, rfl⟩ := mem_vClass_iff.mp ha
  obtain ⟨p, q, hpq, hp, hq, hγeq⟩ := isD4Root_iff.mp hγ
  have hb0 : b ≠ 0 := hb.ne_zero
  have hex : p ≠ i ∨ q ≠ i := by
    by_cases hp : p = i
    · right
      intro hq
      exact hpq (hp.trans hq.symm)
    · left
      exact hp
  intro heq
  rcases hex with hpi | hqi
  · have hcoord : (vWt N b i s + b • castW N γ) p = b * (γ p : ZMod N) := by
      rw [hγeq, vWt_add_coord]
      simp [hpi, hpq]
    have hzero : (-vWt N b i s) p = 0 := by simp [vWt, hpi]
    apply mul_sign_ne_zero hb0 hp
    rw [← hcoord, heq, hzero]
  · have hcoord : (vWt N b i s + b • castW N γ) q = b * (γ q : ZMod N) := by
      rw [hγeq, vWt_add_coord]
      simp [hqi, Ne.symm hpq]
    have hzero : (-vWt N b i s) q = 0 := by simp [vWt, hqi]
    apply mul_sign_ne_zero hb0 hq
    rw [← hcoord, heq, hzero]
private theorem vClass_triangle_l_ne {N : ℕ} {b : ZMod N} {i k l : Fin 4} {s t u : ℤ} (hki : k ≠ i)
    {γ β : Fin 4 → ℤ} (hγeq : γ = Pi.single i (-s) + Pi.single k t) (hβeq : β = Pi.single k (-t) +
    Pi.single l u) (hs : s = 1 ∨ s = -1) (hu : u = 1 ∨ u = -1) (h3 : vWt N b i s + b • castW N (γ +
    β) ≠ vWt N b i s) (h4 : vWt N b i s + b • castW N (γ + β) ≠ -vWt N b i s) : l ≠ i := by
  intro hli
  subst l
  have hsum : γ + β = Pi.single i (u - s) := by
    rw [hγeq, hβeq]
    funext r
    simp only [Pi.add_apply, Pi.single_apply]
    by_cases hri : r = i
    · subst r
      simp [hki, Ne.symm hki]
      ring
    · by_cases hrk : r = k
      · subst r
        simp [hri]
      · simp [hri, hrk]
  have hval : vWt N b i s + b • castW N (γ + β) = Pi.single i ((u : ZMod N) * b) := by
    rw [hsum, vWt_add_single]
    congr 1
    push_cast
    ring
  rcases hs with rfl | rfl <;> rcases hu with rfl | rfl
  · exact h3 (by rw [hval, vWt])
  · exact h4 (by rw [hval, vWt]; norm_num; rw [Pi.single_neg])
  · exact h4 (by rw [hval, vWt]; norm_num; rw [Pi.single_neg, neg_neg])
  · exact h3 (by rw [hval, vWt])
private theorem vClass_triangle_dot {i k l : Fin 4} (hki : k ≠ i) (hlk : l ≠ k) (hli : l ≠ i) {s t u
    : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (hu : u = 1 ∨ u = -1) {γ β : Fin 4 → ℤ} (hγeq :
    γ = Pi.single i (-s) + Pi.single k t) (hβeq : β = Pi.single k (-t) + Pi.single l u) : γ ⬝ᵥ β =
    -1 := by
  rw [hγeq, hβeq]
  simp only [dotProduct_add, add_dotProduct, single_dotProduct, dotProduct_single]
  simp [Pi.single_apply, Ne.symm hki, hlk, Ne.symm hli]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    norm_num
private theorem vClass_triangle_two_gamma_add {i k l : Fin 4} {s t u : ℤ} {γ β : Fin 4 → ℤ} (hγeq :
    γ = Pi.single i (-s) + Pi.single k t) (hβeq : β = Pi.single k (-t) + Pi.single l u) : 2 • γ + β
    = Pi.single i (-2 * s) + Pi.single k t + Pi.single l u := by
  rw [hγeq, hβeq]
  funext r
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring
private theorem vClass_triangle_not_mem_beta {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) {b : ZMod N} (hb :
    IsUnit b) {i k l : Fin 4} (hki : k ≠ i) (hlk : l ≠ k) (hli : l ≠ i) {s t u : ℤ} (hs : s = 1 ∨ s
    = -1) (ht : t = 1 ∨ t = -1) {β : Fin 4 → ℤ} (hβeq : β = Pi.single k (-t) + Pi.single l u) : vWt
    N b i s + b • castW N β ∉ vClass N b := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_vClass]
  apply not_isVWt_of_two hb.ne_zero (Ne.symm hki)
  · have hcoi : (vWt N b i s + b • castW N β) i = (s : ZMod N) * b := by
      rw [hβeq, vWt_add_coord]
      simp [Ne.symm hki, Ne.symm hli]
    rw [hcoi]
    exact sign_mul_ne_zero hb.ne_zero hs
  · have hcok : (vWt N b i s + b • castW N β) k = b * ((-t : ℤ) : ZMod N) := by
      rw [hβeq, vWt_add_coord]
      simp [hki, Ne.symm hlk]
    rw [hcok]
    exact mul_sign_ne_zero hb.ne_zero (neg_sign ht)
private theorem vClass_triangle_not_mem_gamma_beta {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) {b : ZMod N} (hb
    : IsUnit b) {i k l : Fin 4} (hki : k ≠ i) (hlk : l ≠ k) (hli : l ≠ i) {s t u : ℤ} (hs : s = 1 ∨
    s = -1) (ht : t = 1 ∨ t = -1) {γ β : Fin 4 → ℤ} (hγeq : γ = Pi.single i (-s) + Pi.single k t)
    (hβeq : β = Pi.single k (-t) + Pi.single l u) : vWt N b i s + b • castW N (2 • γ + β) ∉ vClass N
    b := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_vClass]
  apply not_isVWt_of_two hb.ne_zero (Ne.symm hki)
  · have hcoi : (vWt N b i s + b • castW N (2 • γ + β)) i = -((s : ZMod N) * b) := by
      rw [vClass_triangle_two_gamma_add hγeq hβeq, vWt_add_coord3]
      simp [Ne.symm hki, Ne.symm hli]
      ring
    rw [hcoi]
    intro hzero
    exact sign_mul_ne_zero hb.ne_zero hs (neg_eq_zero.mp hzero)
  · have hcok : (vWt N b i s + b • castW N (2 • γ + β)) k = (t : ZMod N) * b := by
      rw [vClass_triangle_two_gamma_add hγeq hβeq, vWt_add_coord3]
      simp [hki, Ne.symm hlk]
      ring
    rw [hcok]
    exact sign_mul_ne_zero hb.ne_zero ht
private theorem vClass_triangle {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {a : Fin 4 → ZMod N} (ha : a ∈ vClass N b) {γ β : Fin 4 → ℤ} (hγ : IsD4Root γ) (hβ :
    IsD4Root β) (h1 : a + b • castW N γ ∈ vClass N b) (h2 : a + b • castW N (γ + β) ∈ vClass N b)
    (h3 : a + b • castW N (γ + β) ≠ a) (h4 : a + b • castW N (γ + β) ≠ -a) : γ ⬝ᵥ β = -1 ∧ a + b •
    castW N β ∉ vClass N b ∧ a + b • castW N (2 • γ + β) ∉ vClass N b := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨i, s, hs, rfl⟩ := mem_vClass_iff.mp ha
  rw [mem_vClass] at h1 h2
  obtain ⟨k, hki, t, ht, hγeq⟩ := (isVWt_vWt_add hN3 hN hb hs hγ).mp h1
  have h1eq : vWt N b i s + b • castW N γ = Pi.single k ((t : ZMod N) * b) := by
    rw [hγeq]
    exact vWt_add_eq_single hki
  have h2v : IsVWt b (Pi.single k ((t : ZMod N) * b) + b • castW N β) := by
    rw [← h1eq, add_assoc, ← smul_add, ← castW_add]
    exact h2
  obtain ⟨l, hlk, u, hu, hβeq⟩ := (isVWt_vWt_add hN3 hN hb ht hβ).mp h2v
  have hli : l ≠ i := vClass_triangle_l_ne hki hγeq hβeq hs hu h3 h4
  have hdot : γ ⬝ᵥ β = -1 := vClass_triangle_dot hki hlk hli hs ht hu hγeq hβeq
  exact ⟨hdot, vClass_triangle_not_mem_beta hN3 hb hki hlk hli hs ht hβeq,
    vClass_triangle_not_mem_gamma_beta hN3 hb hki hlk hli hs ht hγeq hβeq⟩
private theorem vRoot_eq_iff_forward {p q i : Fin 4} (hpq : p ≠ q) {u v s : ℤ} (hu : u = 1 ∨ u = -1)
    (hv : v = 1 ∨ v = -1) (h : ∃ k : Fin 4, k ≠ i ∧ ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ Pi.single p u +
    Pi.single q v = Pi.single i (-s) + (Pi.single k t : Fin 4 → ℤ)) : (i = p ∧ s = -u) ∨ (i = q ∧ s
    = -v) := by
  obtain ⟨k, hki, t, _, heq⟩ := h
  have hp : (Pi.single p u + Pi.single q v : Fin 4 → ℤ) p = u := root_apply_left hpq u v
  have hq : (Pi.single p u + Pi.single q v : Fin 4 → ℤ) q = v := root_apply_right hpq u v
  by_cases hip : i = p
  · left
    refine ⟨hip, ?_⟩
    have hpkey : (Pi.single i (-s) + Pi.single k t : Fin 4 → ℤ) p = -s := by
      rw [← hip]
      exact root_apply_left hki.symm (-s) t
    have h : u = -s := by rw [← hp, heq, hpkey]
    omega
  · by_cases hiq : i = q
    · right
      refine ⟨hiq, ?_⟩
      have hqkey : (Pi.single i (-s) + Pi.single k t : Fin 4 → ℤ) q = -s := by
        rw [← hiq]
        exact root_apply_left hki.symm (-s) t
      have h : v = -s := by rw [← hq, heq, hqkey]
      omega
    · exfalso
      have hkp : k = p := by
        by_contra hkp
        have hpkey : (Pi.single i (-s) + Pi.single k t : Fin 4 → ℤ) p = 0 :=
          root_apply_of_ne (fun h => hip h.symm) (fun h => hkp h.symm) (-s) t
        have h : u = 0 := by rw [← hp, heq, hpkey]
        rcases hu with rfl | rfl <;> norm_num at h
      have hkq : k = q := by
        by_contra hkq
        have hqkey : (Pi.single i (-s) + Pi.single k t : Fin 4 → ℤ) q = 0 :=
          root_apply_of_ne (fun h => hiq h.symm) (fun h => hkq h.symm) (-s) t
        have h : v = 0 := by rw [← hq, heq, hqkey]
        rcases hv with rfl | rfl <;> norm_num at h
      exact hpq (hkp.symm.trans hkq)
private theorem vRoot_eq_iff_reverse {p q i : Fin 4} (hpq : p ≠ q) {u v s : ℤ} (hu : u = 1 ∨ u = -1)
    (hv : v = 1 ∨ v = -1) (h : (i = p ∧ s = -u) ∨ (i = q ∧ s = -v)) : ∃ k : Fin 4, k ≠ i ∧ ∃ t : ℤ,
    (t = 1 ∨ t = -1) ∧ Pi.single p u + Pi.single q v = Pi.single i (-s) + (Pi.single k t : Fin 4 →
    ℤ) := by
  rcases h with ⟨hip, hs'⟩ | ⟨hiq, hs'⟩
  · subst i
    refine ⟨q, Ne.symm hpq, v, hv, ?_⟩
    rw [hs']
    simp
  · subst i
    refine ⟨p, hpq, u, hu, ?_⟩
    rw [hs']
    rw [show -(-v) = v by ring, add_comm]
private theorem vRoot_eq_iff {p q i : Fin 4} (hpq : p ≠ q) {u v s : ℤ}
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) :
    (∃ k : Fin 4, k ≠ i ∧ ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
        Pi.single p u + Pi.single q v = Pi.single i (-s) + (Pi.single k t : Fin 4 → ℤ)) ↔
      (i = p ∧ s = -u) ∨ (i = q ∧ s = -v) :=
  ⟨vRoot_eq_iff_forward hpq hu hv, vRoot_eq_iff_reverse hpq hu hv⟩
private theorem vClass_two_mem_fwd {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {p q : Fin 4} (hpq : p ≠ q) {u v : ℤ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) {a :
    Fin 4 → ZMod N} (ha : a ∈ vClass N b) : a + b • castW N (Pi.single p u + Pi.single q v) ∈ vClass
    N b → a = vWt N b p (-u) ∨ a = vWt N b q (-v) := by
  intro hmem
  obtain ⟨i, s, hs, rfl⟩ := mem_vClass_iff.mp ha
  rw [mem_vClass] at hmem
  have hkey := (isVWt_vWt_add hN3 hN hb hs
    (isD4Root_single_add_single hpq hu hv)).mp hmem
  rcases (vRoot_eq_iff hpq hu hv).mp hkey with ⟨hip, hs'⟩ | ⟨hiq, hs'⟩
  · left
    rw [hip, hs']
  · right
    rw [hiq, hs']
private theorem vClass_two_mem_bwd {N : ℕ} [NeZero N] {b : ZMod N} {p q : Fin 4} (hpq : p ≠ q) {u v
    : ℤ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) {a : Fin 4 → ZMod N} (h : a = vWt N b p (-u) ∨
    a = vWt N b q (-v)) : a + b • castW N (Pi.single p u + Pi.single q v) ∈ vClass N b := by
  rcases h with rfl | rfl
  · rw [mem_vClass_iff]
    refine ⟨q, v, hv, ?_⟩
    have hcalc := vWt_add_eq_single (N := N) (b := b) (i := p) (k := q)
      (s := -u) (t := v) (Ne.symm hpq)
    rw [show -(-u) = u by ring] at hcalc
    exact hcalc
  · rw [mem_vClass_iff]
    refine ⟨p, u, hu, ?_⟩
    have hcalc := vWt_add_eq_single (N := N) (b := b) (i := q) (k := p)
      (s := -v) (t := u) hpq
    rw [show -(-v) = v by ring] at hcalc
    rw [add_comm (Pi.single p u : Fin 4 → ℤ) (Pi.single q v)]
    exact hcalc
private theorem vClass_two_mem {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {α : Fin 4 → ℤ} (hα : IsD4Root α) : ∃ a₁ ∈ vClass N b, ∃ a₂ ∈ vClass N b, a₁ ≠ a₂ ∧ ∀
    a ∈ vClass N b, (a + b • castW N α ∈ vClass N b ↔ a = a₁ ∨ a = a₂) := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨p, q, hpq, hup, hvp, hαeq⟩ := isD4Root_iff.mp hα
  let u : ℤ := α p
  let v : ℤ := α q
  have hu : u = 1 ∨ u = -1 := by simpa [u] using hup
  have hv : v = 1 ∨ v = -1 := by simpa [v] using hvp
  have hαeq' : α = Pi.single p u + Pi.single q v := by rw [hαeq]
  refine ⟨vWt N b p (-u), ?_, vWt N b q (-v), ?_, ?_, ?_⟩
  · rw [mem_vClass_iff]
    exact ⟨p, -u, neg_sign hu, rfl⟩
  · rw [mem_vClass_iff]
    exact ⟨q, -v, neg_sign hv, rfl⟩
  · intro h
    have hp1 : vWt N b p (-u) p = ((-u : ℤ) : ZMod N) * b := by simp [vWt]
    have hp2 : vWt N b q (-v) p = 0 := by simp [vWt, Ne.symm hpq]
    apply sign_mul_ne_zero hb.ne_zero (neg_sign hu)
    rw [← hp1, h, hp2]
  · intro a ha
    refine ⟨?_, ?_⟩
    · simpa [hαeq'] using vClass_two_mem_fwd hN3 hN hb hpq hu hv ha
    · intro h
      simpa [hαeq'] using vClass_two_mem_bwd hpq hu hv h
private theorem vClass_raise_adj {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {a : Fin 4 → ZMod N} (ha : a ∈ vClass N b) {γ γ' : Fin 4 → ℤ} (hγ : IsD4Root γ) (hγ' :
    IsD4Root γ') (h1 : a + b • castW N γ ∈ vClass N b) (h2 : a + b • castW N γ' ∈ vClass N b) (hne :
    γ ≠ γ') : γ ⬝ᵥ γ' = 1 ∨ ∃ γ'', IsD4Root γ'' ∧ a + b • castW N γ'' ∈ vClass N b ∧ γ ⬝ᵥ γ'' = 1 ∧
    γ' ⬝ᵥ γ'' = 1 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨i, s, hs, rfl⟩ := mem_vClass_iff.mp ha
  rw [mem_vClass] at h1 h2
  obtain ⟨k, hki, t, ht, hγeq⟩ := (isVWt_vWt_add hN3 hN hb hs hγ).mp h1
  obtain ⟨k', hk'i, t', ht', hγ'eq⟩ := (isVWt_vWt_add hN3 hN hb hs hγ').mp h2
  by_cases hkk' : k = k'
  · subst k'
    have htt' : t ≠ t' := by
      intro htt
      exact hne (by rw [hγeq, hγ'eq, htt])
    right
    obtain ⟨l, hli, hlk⟩ := Fin.exists_ne_and_ne_of_two_lt i k (by norm_num : 2 < 4)
    have hlk' : l ≠ k := hlk
    have hli' : l ≠ i := hli
    refine ⟨Pi.single i (-s) + Pi.single l 1, ?_, ?_, ?_, ?_⟩
    · exact isD4Root_single_add_single (i := i) (j := l) (Ne.symm hli)
        (by rcases hs with rfl | rfl <;> norm_num) (Or.inl rfl)
    · rw [mem_vClass_iff]
      refine ⟨l, 1, Or.inl rfl, ?_⟩
      exact vWt_add_eq_single (N := N) (b := b) (i := i) (k := l) (s := s) (t := 1) hli
    · rw [hγeq]
      simp only [dotProduct_add, add_dotProduct, single_dotProduct, dotProduct_single]
      simp [Pi.single_apply, Ne.symm hki, Ne.symm hli, Ne.symm hlk]
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num
    · rw [hγ'eq]
      simp only [dotProduct_add, add_dotProduct, single_dotProduct, dotProduct_single]
      simp [Pi.single_apply, Ne.symm hki, Ne.symm hli, Ne.symm hlk]
      rcases hs with rfl | rfl <;> rcases ht' with rfl | rfl <;> norm_num
  · left
    rw [hγeq, hγ'eq]
    simp only [dotProduct_add, add_dotProduct, single_dotProduct, dotProduct_single]
    simp [Pi.single_apply, Ne.symm hki, Ne.symm hk'i, hkk']
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl <;>
      norm_num
private theorem vClass_raise_edge_ne {i k k' : Fin 4} (hki : k ≠ i) {s t t' : ℤ} (hs : s = 1 ∨ s =
    -1) (ht : t = 1 ∨ t = -1) (ht' : t' = 1 ∨ t' = -1) (hdot : (Pi.single i (-s) + Pi.single k t :
    Fin 4 → ℤ) ⬝ᵥ (Pi.single i (-s) + Pi.single k' t') = 1) : k ≠ k' := by
  intro h
  subst k'
  simp only [dotProduct_add, add_dotProduct, single_dotProduct, dotProduct_single] at hdot
  simp [Pi.single_apply, Ne.symm hki] at hdot
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl <;>
    norm_num at hdot
private theorem vClass_raise_edge_delta {i k k' : Fin 4} (hki : k ≠ i) (hk'i : k' ≠ i) (hkk' : k ≠
    k') {s t t' : ℤ} {γ γ' : Fin 4 → ℤ} (hγeq : γ = Pi.single i (-s) + Pi.single k t) (hγ'eq : γ' =
    Pi.single i (-s) + Pi.single k' t') : (γ' - γ = Pi.single k' t' + Pi.single k (-t)) ∧ (-(γ' - γ)
    = Pi.single k t + Pi.single k' (-t')) ∧ (γ - (γ' - γ) = Pi.single i (-s) + Pi.single k (2 * t) +
    Pi.single k' (-t')) ∧ (γ + γ' = Pi.single i (-2 * s) + Pi.single k t + Pi.single k' t') := by
  have hδ : γ' - γ = Pi.single k' t' + Pi.single k (-t) := by
    rw [hγeq, hγ'eq]
    funext r
    simp only [Pi.sub_apply, Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp_all <;> ring
  have hδneg : -(γ' - γ) = Pi.single k t + Pi.single k' (-t') := by
    rw [hδ]
    funext r
    simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply]
    split_ifs <;> simp_all <;> ring
  have hγδ : γ - (γ' - γ) = Pi.single i (-s) + Pi.single k (2 * t) + Pi.single k' (-t') := by
    rw [hγeq, hγ'eq]
    funext r
    simp only [Pi.sub_apply, Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp_all <;> ring
  have hγγ' : γ + γ' = Pi.single i (-2 * s) + Pi.single k t + Pi.single k' t' := by
    rw [hγeq, hγ'eq]
    funext r
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp_all <;> ring
  exact ⟨hδ, hδneg, hγδ, hγγ'⟩
private theorem vClass_raise_edge_add {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) {b : ZMod N} (hb : IsUnit b)
    {i k k' : Fin 4} (hki : k ≠ i) (hk'i : k' ≠ i) (hkk' : k ≠ k') {s t t' : ℤ} (hs : s = 1 ∨ s =
    -1) (ht : t = 1 ∨ t = -1) {δ : Fin 4 → ℤ} (hδ : δ = Pi.single k' t' + (Pi.single k (-t) : Fin 4
    → ℤ)) : vWt N b i s + b • castW N δ ∉ vClass N b := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_vClass]
  apply not_isVWt_of_two hb.ne_zero (Ne.symm hki)
  · have hcoi : (vWt N b i s + b • castW N δ) i = (s : ZMod N) * b := by
      rw [hδ, vWt_add_coord]
      simp [Ne.symm hki, Ne.symm hk'i]
    rw [hcoi]
    exact sign_mul_ne_zero hb.ne_zero hs
  · have hcok : (vWt N b i s + b • castW N δ) k = b * ((-t : ℤ) : ZMod N) := by
      rw [hδ, vWt_add_coord]
      simp [hki, hkk', Ne.symm hkk']
    rw [hcok]
    exact mul_sign_ne_zero hb.ne_zero (neg_sign ht)
private theorem vClass_raise_edge_sub {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) {b : ZMod N} (hb : IsUnit b)
    {i k k' : Fin 4} (hki : k ≠ i) (hk'i : k' ≠ i) (hkk' : k ≠ k') {s t t' : ℤ} (hs : s = 1 ∨ s =
    -1) (ht : t = 1 ∨ t = -1) {δ : Fin 4 → ℤ} (hδ : δ = Pi.single k t + (Pi.single k' (-t') : Fin 4
    → ℤ)) : vWt N b i s + b • castW N δ ∉ vClass N b := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_vClass]
  apply not_isVWt_of_two hb.ne_zero (Ne.symm hki)
  · have hcoi : (vWt N b i s + b • castW N δ) i = (s : ZMod N) * b := by
      rw [hδ, vWt_add_coord]
      simp [Ne.symm hki, Ne.symm hk'i]
    rw [hcoi]
    exact sign_mul_ne_zero hb.ne_zero hs
  · have hcok : (vWt N b i s + b • castW N δ) k = b * (t : ZMod N) := by
      rw [hδ, vWt_add_coord]
      simp [hki, hkk', Ne.symm hkk']
    rw [hcok]
    exact mul_sign_ne_zero hb.ne_zero ht
private theorem vClass_raise_edge_gamma_sub {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod
    N} (hb : IsUnit b) {i k k' : Fin 4} (hki : k ≠ i) (hk'i : k' ≠ i) (hkk' : k ≠ k') {s t t' : ℤ}
    (ht : t = 1 ∨ t = -1) (ht' : t' = 1 ∨ t' = -1) {δ : Fin 4 → ℤ} (hδ : δ = Pi.single i (-s) +
    Pi.single k (2 * t) + (Pi.single k' (-t') : Fin 4 → ℤ)) : vWt N b i s + b • castW N δ ∉ vClass N
    b := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_vClass]
  apply not_isVWt_of_two hb.ne_zero hkk'
  · have hcok : (vWt N b i s + b • castW N δ) k = b * ((2 * t : ℤ) : ZMod N) := by
      rw [hδ, vWt_add_coord3]
      simp [hki, hkk', Ne.symm hkk']
    rw [hcok]
    exact mul_two_sign_ne_zero hN3 hN hb ht
  · have hcok' : (vWt N b i s + b • castW N δ) k' = b * ((-t' : ℤ) : ZMod N) := by
      rw [hδ, vWt_add_coord3]
      simp [hk'i, hkk', Ne.symm hkk']
    rw [hcok']
    exact mul_sign_ne_zero hb.ne_zero (neg_sign ht')
private theorem vClass_raise_edge_gamma_add {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) {b : ZMod N} (hb :
    IsUnit b) {i k k' : Fin 4} (hki : k ≠ i) (hk'i : k' ≠ i) (hkk' : k ≠ k') {s t t' : ℤ} (hs : s =
    1 ∨ s = -1) (ht : t = 1 ∨ t = -1) {δ : Fin 4 → ℤ} (hδ : δ = Pi.single i (-2 * s) + Pi.single k t
    + (Pi.single k' t' : Fin 4 → ℤ)) : vWt N b i s + b • castW N δ ∉ vClass N b := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_vClass]
  apply not_isVWt_of_two hb.ne_zero (Ne.symm hki)
  · have hcoi : (vWt N b i s + b • castW N δ) i = -((s : ZMod N) * b) := by
      rw [hδ, vWt_add_coord3]
      simp [Ne.symm hki, Ne.symm hk'i]
      ring
    rw [hcoi]
    intro hzero
    exact sign_mul_ne_zero hb.ne_zero hs (neg_eq_zero.mp hzero)
  · have hcok : (vWt N b i s + b • castW N δ) k = b * (t : ZMod N) := by
      rw [hδ, vWt_add_coord3]
      simp [hki, hkk', Ne.symm hkk']
    rw [hcok]
    exact mul_sign_ne_zero hb.ne_zero ht
private theorem vClass_raise_edge {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {a : Fin 4 → ZMod N} (ha : a ∈ vClass N b) {γ γ' : Fin 4 → ℤ} (hγ : IsD4Root γ) (hγ' :
    IsD4Root γ') (h1 : a + b • castW N γ ∈ vClass N b) (h2 : a + b • castW N γ' ∈ vClass N b) (hdot
    : γ ⬝ᵥ γ' = 1) : a + b • castW N (γ' - γ) ∉ vClass N b ∧ a - b • castW N (γ' - γ) ∉ vClass N b ∧
    a + b • castW N γ - b • castW N (γ' - γ) ∉ vClass N b ∧ a + b • castW N γ' + b • castW N γ ∉
    vClass N b := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨i, s, hs, rfl⟩ := mem_vClass_iff.mp ha
  rw [mem_vClass] at h1 h2
  obtain ⟨k, hki, t, ht, hγeq⟩ := (isVWt_vWt_add hN3 hN hb hs hγ).mp h1
  obtain ⟨k', hk'i, t', ht', hγ'eq⟩ := (isVWt_vWt_add hN3 hN hb hs hγ').mp h2
  have hdot' := hdot
  rw [hγeq, hγ'eq] at hdot'
  have hkk' : k ≠ k' := vClass_raise_edge_ne hki hs ht ht' hdot'
  obtain ⟨hδ, hδneg, hγδ, hγγ'⟩ := vClass_raise_edge_delta hki hk'i hkk' hγeq hγ'eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact vClass_raise_edge_add hN3 hb hki hk'i hkk' hs ht hδ
  · have heq : vWt N b i s - b • castW N (γ' - γ) =
        vWt N b i s + b • castW N (-(γ' - γ)) := by
      rw [castW_neg, smul_neg, sub_eq_add_neg]
    rw [heq]
    exact vClass_raise_edge_sub hN3 hb hki hk'i hkk' hs ht hδneg
  · have heq : vWt N b i s + b • castW N γ - b • castW N (γ' - γ) =
        vWt N b i s + b • castW N (γ - (γ' - γ)) := by
      rw [add_sub_assoc, ← smul_sub, ← castW_sub]
    rw [heq]
    exact vClass_raise_edge_gamma_sub hN3 hN hb hki hk'i hkk' ht ht' hγδ
  · have heq : vWt N b i s + b • castW N γ' + b • castW N γ =
        vWt N b i s + b • castW N (γ + γ') := by
      rw [add_assoc, ← smul_add, ← castW_add, add_comm (γ' : Fin 4 → ℤ) γ]
    rw [heq]
    exact vClass_raise_edge_gamma_add hN3 hb hki hk'i hkk' hs ht hγγ'
private theorem vWt_isSmallClass {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) : IsSmallClass N b (vClass N b) := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  refine ⟨hN3, hN, hb, vClass_card_eq hN3 hN hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact vClass_neg_mem ha
  · intro β hβ a ha
    exact vClass_reflW_mem hβ ha
  · intro a ha α hα k hk hC
    exact vClass_step hN3 hb ha hα hk hC
  · intro a ha α hα hC
    exact vClass_sub_not_mem hN3 hN hb ha hα hC
  · intro a ha α hα hC
    exact vClass_reflW_eq hN3 hN hb ha hα hC
  · intro a ha a' ha' hne hneg
    exact vClass_adj ha ha' hne hneg
  · intro a ha γ hγ
    exact vClass_ne_neg hN3 hb ha hγ
  · intro a ha γ β hγ hβ h1 h2 h3 h4
    exact vClass_triangle hN3 hN hb ha hγ hβ h1 h2 h3 h4
  · intro α hα
    exact vClass_two_mem hN3 hN hb hα
  · intro _ a ha γ γ' hγ hγ' h1 h2 hne
    exact vClass_raise_adj hN3 hN hb ha hγ hγ' h1 h2 hne
  · intro _ a ha γ γ' hγ hγ' h1 h2 hdot
    exact vClass_raise_edge hN3 hN hb ha hγ hγ' h1 h2 hdot

theorem isSmallClass_vWt {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b σ : ZMod N}
    (hb : IsUnit b) (hσ : σ = b ∨ σ = -b) :
    IsSmallClass N σ (Finset.univ.filter fun a => IsVWt b a) := by
  rcases hσ with rfl | rfl
  · exact vWt_isSmallClass hN3 hN hb
  · exact (vWt_isSmallClass hN3 hN hb).neg
private theorem sClass_card_eq {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} (he : e < 2) : (sClass N b e).card = 8 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have he' : e % 2 = e := Nat.mod_eq_of_lt he
  rw [show sClass N b e = Finset.univ.filter
      (fun a => IsSWt b a ∧ negCount b a % 2 = e % 2) by
    rw [sClass]
    congr 1
    ext a
    simp [he']]
  exact card_filter_isSWt hN hb.ne_zero e
private theorem sClass_neg_mem {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) : -a ∈ sClass N b e := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_sClass] at ha ⊢
  have haSWt : IsSWt b a := ha.1
  have hnegSWt : IsSWt b (-a) := by
    intro i
    rcases haSWt i with h | h <;> simp [h]
  have hcount : negCount b (-a) = negCount (-b) a := by
    rw [negCount, negCount]
    congr 1
    ext i
    simp
  have hle : negCount b a ≤ 4 := by
    rw [negCount]
    simpa using Finset.card_le_univ (Finset.univ.filter fun i => a i = -b)
  refine ⟨hnegSWt, ?_⟩
  rw [hcount, negCount_neg hN hb.ne_zero haSWt, ← ha.2]
  omega
private theorem sClass_reflW_mem {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {β : Fin 4 → ℤ} (hβ : IsD4Root β) {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e)
    : reflW β a ∈ sClass N b e := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_sClass] at ha ⊢
  obtain ⟨hSWt, hpar⟩ := isSWt_reflW hN hb.ne_zero hβ ha.1
  exact ⟨hSWt, hpar.trans ha.2⟩
private theorem sClass_step {N : ℕ} [NeZero N] {b : ZMod N} {e : ℕ} {a : Fin 4 → ZMod N} (ha : a ∈
    sClass N b e) {α : Fin 4 → ℤ} (hα : IsD4Root α) {k : ZMod N} (hk : k ≠ 0) (hC : a + k • castW N
    α ∈ sClass N b e) : k = 2 * b ∨ k = -(2 * b) := by
  rw [mem_sClass] at ha hC
  exact step_eq_of_isSWt hα hk ha.1 rfl hC.1
private theorem isSWt_add_two_iff {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b) {a
    : Fin 4 → ZMod N} (ha : IsSWt b a) {p q : Fin 4} (hpq : p ≠ q) {u v : ℤ} (hu : u = 1 ∨ u = -1)
    (hv : v = 1 ∨ v = -1) : IsSWt b (a + (2 * b) • castW N (Pi.single p u + Pi.single q v)) ↔ a p =
    ((-u : ℤ) : ZMod N) * b ∧ a q = ((-v : ℤ) : ZMod N) * b := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  constructor
  · intro hw
    constructor
    · have hwp : (a + (2 * b) • castW N (Pi.single p u + Pi.single q v)) p =
          a p + (2 * b) * (u : ZMod N) := by
        rw [sWt_add_two_coord b a hpq p u v, if_pos rfl]
      exact sWt_key_coord hN3 hN hb (ha p) hu (by simpa [hwp] using hw p)
    · have hwq : (a + (2 * b) • castW N (Pi.single p u + Pi.single q v)) q =
          a q + (2 * b) * (v : ZMod N) := by
        rw [sWt_add_two_coord b a hpq q u v, if_neg (Ne.symm hpq), if_pos rfl]
      exact sWt_key_coord hN3 hN hb (ha q) hv (by simpa [hwq] using hw q)
  · rintro ⟨hp, hq⟩ r
    rw [sWt_add_two_coord b a hpq r u v]
    by_cases hrp : r = p
    · subst r
      rw [if_pos rfl, hp]
      rcases hu with rfl | rfl
      · left
        push_cast
        ring
      · right
        push_cast
        ring
    · by_cases hrq : r = q
      · subst r
        rw [if_neg hrp, if_pos rfl, hq]
        rcases hv with rfl | rfl
        · left
          push_cast
          ring
        · right
          push_cast
          ring
      · rw [if_neg hrp, if_neg hrq]
        exact ha r
private theorem isSWt_add_two_parity {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b)
    {a : Fin 4 → ZMod N} (ha : IsSWt b a) {p q : Fin 4} (hpq : p ≠ q) {u v : ℤ} (hu : u = 1 ∨ u =
    -1) (hv : v = 1 ∨ v = -1) (hp : a p = ((-u : ℤ) : ZMod N) * b) (hq : a q = ((-v : ℤ) : ZMod N) *
    b) : negCount b (a + (2 * b) • castW N (Pi.single p u + Pi.single q v)) % 2 = negCount b a % 2
    := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hb0 : b ≠ 0 := hb.ne_zero
  set w := a + (2 * b) • castW N (Pi.single p u + Pi.single q v) with hwdef
  have hw : IsSWt b w := (isSWt_add_two_iff hN3 hN hb ha hpq hu hv).mpr ⟨hp, hq⟩
  have hdiff : (Finset.univ.filter fun r => a r ≠ w r) = {p, q} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hne
      by_contra h
      rw [not_or] at h
      exact hne (by rw [hwdef, sWt_add_two_coord b a hpq r u v, if_neg h.1, if_neg h.2])
    · rintro (hr | hr)
      · subst r
        rw [hwdef, sWt_add_two_coord b a hpq p u v, if_pos rfl, hp]
        exact sWt_flip_self_ne hN hb0 hu
      · subst r
        rw [hwdef, sWt_add_two_coord b a hpq q u v, if_neg (Ne.symm hpq), if_pos rfl, hq]
        exact sWt_flip_self_ne hN hb0 hv
  have hpar := diff_card_parity hN hb0 ha hw
  rw [hdiff, Finset.card_pair hpq] at hpar
  omega
private theorem sClass_sub_not_mem {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) {α : Fin 4 → ℤ} (hα : IsD4Root α)
    (hC : a + (2 * b) • castW N α ∈ sClass N b e) : a - (2 * b) • castW N α ∉ sClass N b e := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_sClass] at ha hC
  obtain ⟨p, q, hpq, hup, hvp, hαeq⟩ := isD4Root_iff.mp hα
  let u : ℤ := α p
  let v : ℤ := α q
  have hu : u = 1 ∨ u = -1 := by simpa [u] using hup
  have hv : v = 1 ∨ v = -1 := by simpa [v] using hvp
  have hαeq' : α = Pi.single p u + Pi.single q v := by rw [hαeq]
  have hp : a p = ((-u : ℤ) : ZMod N) * b :=
    ((isSWt_add_two_iff hN3 hN hb ha.1 hpq hu hv).mp
      (by simpa [hαeq'] using hC.1)).1
  have hcoord : (a - (2 * b) • castW N α) p = (((-3 : ℤ) * u) : ZMod N) * b := by
    rw [hαeq', sWt_sub_two_coord b a hpq p u v, if_pos rfl, hp]
    push_cast
    ring
  rw [mem_sClass]
  rintro ⟨hSWt, hpar⟩
  have hval := hSWt p
  rw [hcoord] at hval
  have h3 := three_sign_mul_ne_pm hN3 hN hb hu
  rcases hval with h | h
  · apply h3.2
    linear_combination -h
  · apply h3.1
    linear_combination -h
private theorem sClass_reflW_eq {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) {α : Fin 4 → ℤ} (hα : IsD4Root α)
    (hC : a + (2 * b) • castW N α ∈ sClass N b e) : reflW α a = a + (2 * b) • castW N α := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_sClass] at ha hC
  obtain ⟨p, q, hpq, hup, hvp, hαeq⟩ := isD4Root_iff.mp hα
  let u : ℤ := α p
  let v : ℤ := α q
  have hu : u = 1 ∨ u = -1 := by simpa [u] using hup
  have hv : v = 1 ∨ v = -1 := by simpa [v] using hvp
  have hαeq' : α = Pi.single p u + Pi.single q v := by rw [hαeq]
  obtain ⟨hp, hq⟩ := (isSWt_add_two_iff hN3 hN hb ha.1 hpq hu hv).mp
    (by simpa [hαeq'] using hC.1)
  have hdot : a ⬝ᵥ castW N α = -(2 * b) := by
    rw [hαeq', castW_add, castW_single, castW_single, dotProduct_add, dotProduct_single,
      dotProduct_single, hp, hq]
    push_cast
    rcases hu with h | h <;> rw [h] <;> rcases hv with h' | h' <;> rw [h'] <;> ring
  rw [reflW, hdot, neg_smul, sub_neg_eq_add]
private theorem sClass_ne_neg {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) {γ : Fin 4 → ℤ} (hγ : IsD4Root γ)
    : a + (2 * b) • castW N γ ≠ -a := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_sClass] at ha
  obtain ⟨p, q, hpq, hup, hvp, hγeq⟩ := isD4Root_iff.mp hγ
  let u : ℤ := γ p
  let v : ℤ := γ q
  have hu : u = 1 ∨ u = -1 := by simpa [u] using hup
  have hv : v = 1 ∨ v = -1 := by simpa [v] using hvp
  have hγeq' : γ = Pi.single p u + Pi.single q v := by rw [hγeq]
  obtain ⟨r, hrp, hrq⟩ := Fin.exists_ne_and_ne_of_two_lt p q (by norm_num : 2 < 4)
  have hr : (a + (2 * b) • castW N γ) r = a r := by
    rw [hγeq', sWt_add_two_coord b a hpq r u v, if_neg hrp, if_neg hrq]
  intro heq
  have har_ne : a r ≠ 0 := by
    rcases ha.1 r with h | h <;> simp [h, hb.ne_zero]
  have hneg : a r = -a r := by
    have h := congrFun heq r
    rwa [hr] at h
  exact ZMod.ne_neg_self hN har_ne hneg
private theorem sClass_adj_even {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a a' : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) (ha' : a' ∈ sClass N b e) :
    (Finset.univ.filter fun r => a r ≠ a' r).card % 2 = 0 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_sClass] at ha ha'
  have h := diff_card_parity hN hb.ne_zero ha.1 ha'.1
  rw [Nat.add_mod, ha.2, ha'.2] at h
  have hee : (e + e) % 2 = 0 := by omega
  rwa [hee] at h
private theorem sClass_adj_two {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {a a' : Fin 4 → ZMod N} (ha : IsSWt b a) (ha' : IsSWt b a') {p q : Fin 4} (hpq : p ≠
    q) (hD : (Finset.univ.filter fun r => a r ≠ a' r) = {p, q}) : ∃ γ, IsD4Root γ ∧ a' = a + (2 * b)
    • castW N γ := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨sp, hsp⟩ := exists_sign_eq (ha p)
  obtain ⟨sq, hsq⟩ := exists_sign_eq (ha q)
  have hpD : p ∈ Finset.univ.filter fun r => a r ≠ a' r := by rw [hD]; simp
  have hqD : q ∈ Finset.univ.filter fun r => a r ≠ a' r := by rw [hD]; simp
  have ha'p : a' p = -a p :=
    eq_neg_of_ne_of_sign hN hb.ne_zero (ha p) (ha' p) (Finset.mem_filter.mp hpD).2
  have ha'q : a' q = -a q :=
    eq_neg_of_ne_of_sign hN hb.ne_zero (ha q) (ha' q) (Finset.mem_filter.mp hqD).2
  refine ⟨Pi.single p (-sp) + Pi.single q (-sq), ?_, ?_⟩
  · exact isD4Root_single_add_single hpq (neg_sign hsp.1) (neg_sign hsq.1)
  · funext r
    rw [sWt_add_two_coord b a hpq r (-sp) (-sq)]
    by_cases hrp : r = p
    · subst r
      rw [if_pos rfl, hsp.2, ha'p, hsp.2]
      rcases hsp.1 with h | h <;> rw [h] <;> ring
    · by_cases hrq : r = q
      · subst r
        rw [if_neg hrp, if_pos rfl, hsq.2, ha'q, hsq.2]
        rcases hsq.1 with h | h <;> rw [h] <;> ring
      · rw [if_neg hrp, if_neg hrq]
        have hrD : r ∉ Finset.univ.filter fun r => a r ≠ a' r := by rw [hD]; simp [hrp, hrq]
        have heq : a r = a' r := by
          by_contra h
          exact hrD (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        exact heq.symm
private theorem sClass_adj {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit
    b) {e : ℕ} {a a' : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) (ha' : a' ∈ sClass N b e) (hne : a' ≠
    a) (hneg : a' ≠ -a) : ∃ γ, IsD4Root γ ∧ a' = a + (2 * b) • castW N γ := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  let D := Finset.univ.filter fun r => a r ≠ a' r
  have hDcard : D.card % 2 = 0 := sClass_adj_even hN3 hN hb ha ha'
  have hDle : D.card ≤ 4 := by simpa [D] using Finset.card_le_univ D
  have hcases : D.card = 0 ∨ D.card = 2 ∨ D.card = 4 := by omega
  rw [mem_sClass] at ha ha'
  rcases hcases with h0 | h2 | h4
  · exfalso
    have hDempty : D = ∅ := Finset.card_eq_zero.mp h0
    apply hne
    funext r
    have hr : r ∉ D := by rw [hDempty]; simp
    by_contra h
    exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => h heq.symm⟩)
  · obtain ⟨p, q, hpq, hDpq⟩ := Finset.card_eq_two.mp h2
    exact sClass_adj_two hN3 hN hb ha.1 ha'.1 hpq (by simpa [D] using hDpq)
  · exfalso
    have hDuniv : D = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using h4
    apply hneg
    funext r
    have hr : r ∈ D := by rw [hDuniv]; simp
    exact eq_neg_of_ne_of_sign hN hb.ne_zero (ha.1 r) (ha'.1 r) (Finset.mem_filter.mp hr).2
private theorem add_two_smul_castW_apply {N : ℕ} (b : ZMod N) (a : Fin 4 → ZMod N) (δ : Fin 4 → ℤ)
    (k : Fin 4) : (a + (2 * b) • castW N δ) k = a k + (2 * b) * (δ k : ZMod N) := by
  simp [castW, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
private theorem add_two_eq_neg_of_coord {N : ℕ} (b : ZMod N) (a : Fin 4 → ZMod N) (δ : Fin 4 → ℤ) {k
    : Fin 4} {z : ℤ} (hδ : δ k = z) (ha : a k = ((-z : ℤ) : ZMod N) * b) : (a + (2 * b) • castW N δ)
    k = -a k := by
  rw [add_two_smul_castW_apply, hδ, ha]
  push_cast
  ring
private theorem sign_eq_of_cast_eq {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {s u : ℤ} (hs : s = 1 ∨ s =
    -1) (hu : u = 1 ∨ u = -1) (h : (s : ZMod N) = (u : ZMod N)) : s = u := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have h1 : (1 : ZMod N) ≠ -1 := by
    simpa using ZMod.ne_neg_self hN (one_ne_zero : (1 : ZMod N) ≠ 0)
  rcases hs with rfl | rfl <;> rcases hu with rfl | rfl <;> simp_all
private theorem coord_constraint {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b) {u
    z : ℤ} (hu : u = 1 ∨ u = -1) (hz : z = -1 ∨ z = 0 ∨ z = 1) (h : ((u + 2 * z : ℤ) : ZMod N) * b =
    b ∨ ((u + 2 * z : ℤ) : ZMod N) * b = -b) : z = 0 ∨ z = -u := by
  by_contra hc
  push Not at hc
  obtain ⟨hz0, hzmu⟩ := hc
  have hzu : z = u := by
    rcases hu with rfl | rfl <;> rcases hz with rfl | rfl | rfl <;> omega
  rw [hzu] at h
  have h3 := three_sign_mul_ne_pm hN3 hN hb hu
  have h' : (u + 2 * u : ℤ) = 3 * u := by ring
  rw [h'] at h
  push_cast at h
  rcases h with h | h
  · exact h3.1 (by linear_combination h)
  · exact h3.2 (by linear_combination h)
private theorem fin4_cover {p q r t : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠ r)
    (hqt : q ≠ t) (hrt : r ≠ t) : ∀ k : Fin 4, k = p ∨ k = q ∨ k = r ∨ k = t := by
  have hcov : ({p, q, r, t} : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr, hpt]),
      Finset.card_insert_of_notMem (by simp [hqr, hqt]),
      Finset.card_insert_of_notMem (by simp [hrt]), Finset.card_singleton]
    norm_num
  intro k
  have hk : k ∈ ({p, q, r, t} : Finset (Fin 4)) := by
    rw [hcov]
    exact Finset.mem_univ k
  simpa using hk
private theorem negCount_four {N : ℕ} {b : ZMod N} {a : Fin 4 → ZMod N} {p q r t : Fin 4} (hpq : p ≠
    q) (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t) : negCount b a = (if a
    p = -b then 1 else 0) + (if a q = -b then 1 else 0) + (if a r = -b then 1 else 0) + (if a t = -b
    then 1 else 0) := by
  have hcov : ({p, q, r, t} : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr, hpt]),
      Finset.card_insert_of_notMem (by simp [hqr, hqt]),
      Finset.card_insert_of_notMem (by simp [hrt]), Finset.card_singleton]
    norm_num
  rw [negCount, ← hcov, Finset.card_filter]
  rw [Finset.sum_insert (by simp [hpq, hpr, hpt]),
    Finset.sum_insert (by simp [hqr, hqt]),
    Finset.sum_insert (by simp [hrt]), Finset.sum_singleton]
  ring
private theorem root_add_neg {p q : Fin 4} (u v : ℤ) : (Pi.single p u + Pi.single q v : Fin 4 → ℤ) +
    (Pi.single p (-u) + Pi.single q (-v)) = 0 := by
  funext k
  simp only [Pi.add_apply, Pi.single_apply, Pi.zero_apply]
  split_ifs <;> ring
private theorem sClass_tri_coord_sign {N : ℕ} {b : ZMod N} {a : Fin 4 → ZMod N} {γ β : Fin 4 → ℤ} {p
    : Fin 4} {u : ℤ} (hp : a p = ((-u : ℤ) : ZMod N) * b) (hγp : γ p = u) (h : IsSWt b (a + (2 * b)
    • castW N (γ + β))) : ((u + 2 * β p : ℤ) : ZMod N) * b = b ∨ ((u + 2 * β p : ℤ) : ZMod N) * b =
    -b := by
  have h' := h p
  rw [add_two_smul_castW_apply, Pi.add_apply, hp, hγp] at h'
  rcases h' with h' | h'
  · left
    push_cast at h' ⊢
    linear_combination h'
  · right
    push_cast at h' ⊢
    linear_combination h'
private theorem root_eq_zero_imp_ne {r t k : Fin 4} (hrt : r ≠ t) {s w : ℤ} (hs0 : s ≠ 0) (hw0 : w ≠
    0) (h : (Pi.single r s + Pi.single t w : Fin 4 → ℤ) k = 0) : k ≠ r ∧ k ≠ t := by
  constructor
  · intro hkr
    apply hs0
    rw [hkr, root_apply_left hrt] at h
    exact h
  · intro hkt
    apply hw0
    rw [hkt, root_apply_right hrt] at h
    exact h
private theorem root_mem_of_ne_zero {r t k : Fin 4} (hrt : r ≠ t) {s w : ℤ} (hs0 : s ≠ 0) (hw0 : w ≠
    0) (h : (Pi.single r s + Pi.single t w : Fin 4 → ℤ) k ≠ 0) : k = r ∨ k = t := by
  by_cases hkr : k = r
  · exact Or.inl hkr
  · by_cases hkt : k = t
    · exact Or.inr hkt
    · exfalso
      rw [root_apply_of_ne hkr hkt] at h
      exact h rfl
private theorem sClass_tri_disjoint {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {a : Fin 4 → ZMod N} {γ β : Fin 4 → ℤ} {p q r t : Fin 4} {u v s w : ℤ} (hpq : p ≠ q)
    (hrt : r ≠ t) (ha : IsSWt b a) (hs : s = 1 ∨ s = -1) (hw : w = 1 ∨ w = -1) (hγeq : γ = Pi.single
    p u + Pi.single q v) (hβeq : β = Pi.single r s + Pi.single t w) (hp : a p = ((-u : ℤ) : ZMod N)
    * b) (hq : a q = ((-v : ℤ) : ZMod N) * b) (hβp : β p = 0) (hβq : β q = 0) (h2 : IsSWt b (a + (2
    * b) • castW N (γ + β))) : a + (2 * b) • castW N (γ + β) = -a := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hs0 : s ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hw0 : w ≠ 0 := by rcases hw with h | h <;> rw [h] <;> norm_num
  have hβp' : (Pi.single r s + Pi.single t w : Fin 4 → ℤ) p = 0 := by
    rwa [hβeq] at hβp
  have hβq' : (Pi.single r s + Pi.single t w : Fin 4 → ℤ) q = 0 := by
    rwa [hβeq] at hβq
  obtain ⟨hpr, hpt⟩ := root_eq_zero_imp_ne hrt hs0 hw0 hβp'
  obtain ⟨hqr, hqt⟩ := root_eq_zero_imp_ne hrt hs0 hw0 hβq'
  have hr : a r = ((-s : ℤ) : ZMod N) * b := by
    refine sWt_key_coord hN3 hN hb (ha r) hs ?_
    have h := h2 r
    rwa [add_two_smul_castW_apply, Pi.add_apply, hγeq, hβeq,
      root_apply_of_ne (Ne.symm hpr) (Ne.symm hqr), root_apply_left hrt, zero_add] at h
  have ht : a t = ((-w : ℤ) : ZMod N) * b := by
    refine sWt_key_coord hN3 hN hb (ha t) hw ?_
    have h := h2 t
    rwa [add_two_smul_castW_apply, Pi.add_apply, hγeq, hβeq,
      root_apply_of_ne (Ne.symm hpt) (Ne.symm hqt), root_apply_right hrt, zero_add] at h
  funext k
  rcases fin4_cover hpq hpr hpt hqr hqt hrt k with hk | hk | hk | hk
  · subst k
    have hsum : (γ + β) p = u := by
      simp [Pi.add_apply, hγeq, hβp, Pi.single_apply, hpq]
    exact add_two_eq_neg_of_coord b a (γ + β) hsum hp
  · subst k
    have hsum : (γ + β) q = v := by
      simp [Pi.add_apply, hγeq, hβq, Pi.single_apply, Ne.symm hpq]
    exact add_two_eq_neg_of_coord b a (γ + β) hsum hq
  · subst k
    have hsum : (γ + β) r = s := by
      simp [Pi.add_apply, hγeq, hβeq, Pi.single_apply, hpr, hqr, hrt]
    exact add_two_eq_neg_of_coord b a (γ + β) hsum hr
  · subst k
    have hsum : (γ + β) t = w := by
      simp [Pi.add_apply, hγeq, hβeq, Pi.single_apply, hpt, hqt, hrt]
    exact add_two_eq_neg_of_coord b a (γ + β) hsum ht
private theorem sClass_tri_share_q {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ β : Fin 4 → ℤ} {p q : Fin 4} {u v : ℤ} (hpq : p ≠ q)
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) (hγeq : γ = Pi.single p u + Pi.single q v) (hp : a p
    = ((-u : ℤ) : ZMod N) * b) (hq : a q = ((-v : ℤ) : ZMod N) * b) (hβp : β p = 0) (hβq : β q = -v)
    : γ ⬝ᵥ β = -1 ∧ a + (2 * b) • castW N β ∉ sClass N b e ∧ a + (2 * b) • castW N (2 • γ + β) ∉
    sClass N b e := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hdot : γ ⬝ᵥ β = -1 := by
    rw [hγeq, add_dotProduct, single_dotProduct, single_dotProduct, hβp, hβq]
    rcases hv with h | h <;> rw [h] <;> norm_num
  have hγp : γ p = u := by rw [hγeq]; simp [Pi.single_apply, hpq]
  refine ⟨hdot, ?_, ?_⟩
  · rw [mem_sClass]
    rintro ⟨hSWt, -⟩
    have hcoord := hSWt q
    rw [add_two_smul_castW_apply, hq, hβq] at hcoord
    rcases hcoord with h | h
    · exact (three_sign_mul_ne_pm hN3 hN hb (neg_sign hv)).1 (by
        push_cast at h ⊢
        linear_combination h)
    · exact (three_sign_mul_ne_pm hN3 hN hb (neg_sign hv)).2 (by
        push_cast at h ⊢
        linear_combination h)
  · rw [mem_sClass]
    rintro ⟨hSWt, -⟩
    have hcoord := hSWt p
    rw [add_two_smul_castW_apply, hp] at hcoord
    have hcoef : ((2 • γ + β) p : ℤ) = 2 * u := by
      simp [Pi.add_apply, Pi.smul_apply, hγp, hβp]
    rw [hcoef] at hcoord
    rcases hcoord with h | h
    · exact (three_sign_mul_ne_pm hN3 hN hb hu).1 (by
        push_cast at h ⊢
        linear_combination h)
    · exact (three_sign_mul_ne_pm hN3 hN hb hu).2 (by
        push_cast at h ⊢
        linear_combination h)
private theorem sClass_tri_share_p {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ β : Fin 4 → ℤ} {p q : Fin 4} {u v : ℤ} (hpq : p ≠ q)
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) (hγeq : γ = Pi.single p u + Pi.single q v) (hp : a p
    = ((-u : ℤ) : ZMod N) * b) (hq : a q = ((-v : ℤ) : ZMod N) * b) (hβp : β p = -u) (hβq : β q = 0)
    : γ ⬝ᵥ β = -1 ∧ a + (2 * b) • castW N β ∉ sClass N b e ∧ a + (2 * b) • castW N (2 • γ + β) ∉
    sClass N b e := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hdot : γ ⬝ᵥ β = -1 := by
    rw [hγeq, add_dotProduct, single_dotProduct, single_dotProduct, hβp, hβq]
    rcases hu with h | h <;> rw [h] <;> norm_num
  have hγq : γ q = v := by rw [hγeq]; simp [Pi.single_apply, Ne.symm hpq]
  refine ⟨hdot, ?_, ?_⟩
  · rw [mem_sClass]
    rintro ⟨hSWt, -⟩
    have hcoord := hSWt p
    rw [add_two_smul_castW_apply, hp, hβp] at hcoord
    rcases hcoord with h | h
    · exact (three_sign_mul_ne_pm hN3 hN hb (neg_sign hu)).1 (by
        push_cast at h ⊢
        linear_combination h)
    · exact (three_sign_mul_ne_pm hN3 hN hb (neg_sign hu)).2 (by
        push_cast at h ⊢
        linear_combination h)
  · rw [mem_sClass]
    rintro ⟨hSWt, -⟩
    have hcoord := hSWt q
    rw [add_two_smul_castW_apply, hq] at hcoord
    have hcoef : ((2 • γ + β) q : ℤ) = 2 * v := by
      simp [Pi.add_apply, Pi.smul_apply, hγq, hβq]
    rw [hcoef] at hcoord
    rcases hcoord with h | h
    · exact (three_sign_mul_ne_pm hN3 hN hb hv).1 (by
        push_cast at h ⊢
        linear_combination h)
    · exact (three_sign_mul_ne_pm hN3 hN hb hv).2 (by
        push_cast at h ⊢
        linear_combination h)
private theorem sClass_tri_same {N : ℕ} {b : ZMod N} {a : Fin 4 → ZMod N} {γ β : Fin 4 → ℤ} {p q r t
    : Fin 4} {u v s w : ℤ} (hpq : p ≠ q) (hrt : r ≠ t) (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1)
    (hs : s = 1 ∨ s = -1) (hw : w = 1 ∨ w = -1) (hγeq : γ = Pi.single p u + Pi.single q v) (hβeq : β
    = Pi.single r s + Pi.single t w) (hβp : β p = -u) (hβq : β q = -v) (h3 : a + (2 * b) • castW N
    (γ + β) ≠ a) : False := by
  have hu0 : (-u : ℤ) ≠ 0 := by rcases hu with h | h <;> rw [h] <;> norm_num
  have hv0 : (-v : ℤ) ≠ 0 := by rcases hv with h | h <;> rw [h] <;> norm_num
  have hs0 : s ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hw0 : w ≠ 0 := by rcases hw with h | h <;> rw [h] <;> norm_num
  have hpmem : p = r ∨ p = t := by
    apply root_mem_of_ne_zero hrt hs0 hw0
    rw [← hβeq, hβp]
    exact hu0
  have hqmem : q = r ∨ q = t := by
    apply root_mem_of_ne_zero hrt hs0 hw0
    rw [← hβeq, hβq]
    exact hv0
  rcases hpmem with hpr | hpt <;> rcases hqmem with hqr | hqt
  · exact hpq (hpr.trans hqr.symm)
  · have hs_eq : s = -u := by
      have h0 : β p = s := by rw [hβeq, hpr]; exact root_apply_left hrt s w
      rw [hβp] at h0
      exact h0.symm
    have hw_eq : w = -v := by
      have h0 : β q = w := by rw [hβeq, hqt]; exact root_apply_right hrt s w
      rw [hβq] at h0
      exact h0.symm
    have hβeq' : β = Pi.single p (-u) + Pi.single q (-v) := by
      rw [hβeq, ← hpr, ← hqt, hs_eq, hw_eq]
    apply h3
    rw [show γ + β = 0 by rw [hγeq, hβeq', root_add_neg],
      show castW N (0 : Fin 4 → ℤ) = 0 from by funext k; simp [castW], smul_zero, add_zero]
  · have hs_eq : s = -v := by
      have h0 : β q = s := by rw [hβeq, hqr]; exact root_apply_left hrt s w
      rw [hβq] at h0
      exact h0.symm
    have hw_eq : w = -u := by
      have h0 : β p = w := by rw [hβeq, hpt]; exact root_apply_right hrt s w
      rw [hβp] at h0
      exact h0.symm
    have hβeq' : β = Pi.single p (-u) + Pi.single q (-v) := by
      rw [hβeq, ← hpt, ← hqr, hs_eq, hw_eq, add_comm]
    apply h3
    rw [show γ + β = 0 by rw [hγeq, hβeq', root_add_neg],
      show castW N (0 : Fin 4 → ℤ) = 0 from by funext k; simp [castW], smul_zero, add_zero]
  · exact hpq (hpt.trans hqt.symm)
private theorem sClass_triangle {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) {γ β : Fin 4 → ℤ} (hγ : IsD4Root
    γ) (hβ : IsD4Root β) (h1 : a + (2 * b) • castW N γ ∈ sClass N b e) (h2 : a + (2 * b) • castW N
    (γ + β) ∈ sClass N b e) (h3 : a + (2 * b) • castW N (γ + β) ≠ a) (h4 : a + (2 * b) • castW N (γ
    + β) ≠ -a) : γ ⬝ᵥ β = -1 ∧ a + (2 * b) • castW N β ∉ sClass N b e ∧ a + (2 * b) • castW N (2 • γ
    + β) ∉ sClass N b e := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_sClass] at ha h1 h2
  obtain ⟨p, q, hpq, hup, hvp, hγeq⟩ := isD4Root_iff.mp hγ
  let u : ℤ := γ p
  let v : ℤ := γ q
  have hu : u = 1 ∨ u = -1 := by simpa [u] using hup
  have hv : v = 1 ∨ v = -1 := by simpa [v] using hvp
  have hγeq' : γ = Pi.single p u + Pi.single q v := by rw [hγeq]
  have hp : a p = ((-u : ℤ) : ZMod N) * b :=
    ((isSWt_add_two_iff hN3 hN hb ha.1 hpq hu hv).mp
      (by simpa [hγeq'] using h1.1)).1
  have hq : a q = ((-v : ℤ) : ZMod N) * b :=
    ((isSWt_add_two_iff hN3 hN hb ha.1 hpq hu hv).mp
      (by simpa [hγeq'] using h1.1)).2
  obtain ⟨r, t, hrt, hsr, hwt, hβeq⟩ := isD4Root_iff.mp hβ
  let s : ℤ := β r
  let w : ℤ := β t
  have hs : s = 1 ∨ s = -1 := by simpa [s] using hsr
  have hw : w = 1 ∨ w = -1 := by simpa [w] using hwt
  have hβeq' : β = Pi.single r s + Pi.single t w := by rw [hβeq]
  have hγp : γ p = u := by rw [hγeq']; simp [Pi.single_apply, hpq]
  have hγq : γ q = v := by rw [hγeq']; simp [Pi.single_apply, Ne.symm hpq]
  have hp2 := sClass_tri_coord_sign hp hγp h2.1
  have hq2 := sClass_tri_coord_sign hq hγq h2.1
  have hβp : β p = 0 ∨ β p = -u :=
    coord_constraint hN3 hN hb hu (root_coord_trichotomy hβ p) hp2
  have hβq : β q = 0 ∨ β q = -v :=
    coord_constraint hN3 hN hb hv (root_coord_trichotomy hβ q) hq2
  rcases hβp with hβp | hβp <;> rcases hβq with hβq | hβq
  · exfalso
    exact h4 (sClass_tri_disjoint hN3 hN hb hpq hrt ha.1 hs hw hγeq' hβeq' hp hq hβp hβq h2.1)
  · exact sClass_tri_share_q hN3 hN hb hpq hu hv hγeq' hp hq hβp hβq
  · exact sClass_tri_share_p hN3 hN hb hpq hu hv hγeq' hp hq hβp hβq
  · exfalso
    exact sClass_tri_same hpq hrt hu hv hs hw hγeq' hβeq' hβp hβq h3

private def sPair {N : ℕ} (p q r : Fin 4) (x y z w : ZMod N) : Fin 4 → ZMod N :=
  fun k => if k = p then x else if k = q then y else if k = r then z else w
private theorem sPair_p {N : ℕ} (p q r : Fin 4) (x y z w : ZMod N) : sPair p q r x y z w p = x := by
  simp [sPair]
private theorem sPair_q {N : ℕ} {p q r : Fin 4} (hpq : p ≠ q) (x y z w : ZMod N) : sPair p q r x y z
    w q = y := by
  simp [sPair, Ne.symm hpq]
private theorem sPair_r {N : ℕ} {p q r : Fin 4} (hpr : p ≠ r) (hqr : q ≠ r) (x y z w : ZMod N) :
    sPair p q r x y z w r = z := by
  simp [sPair, Ne.symm hpr, Ne.symm hqr]
private theorem sPair_t {N : ℕ} {p q r t : Fin 4} (htp : t ≠ p) (htq : t ≠ q) (htr : t ≠ r) (x y z w
    : ZMod N) : sPair p q r x y z w t = w := by
  simp [sPair, htp, htq, htr]
private theorem sPair_isSWt {N : ℕ} {b : ZMod N} {p q r t : Fin 4} {x y z w : ZMod N} (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (htp : t ≠ p) (htq : t ≠ q) (htr : t ≠ r) (hx : x = b ∨ x = -b) (hy
    : y = b ∨ y = -b) (hz : z = b ∨ z = -b) (hw : w = b ∨ w = -b) : IsSWt b (sPair p q r x y z w)
    := by
  intro k
  by_cases hkp : k = p
  · rw [hkp, sPair_p]
    exact hx
  · by_cases hkq : k = q
    · rw [hkq] at hkp ⊢
      rw [sPair_q (Ne.symm hkp)]
      exact hy
    · by_cases hkr : k = r
      · rw [hkr] at hkp hkq ⊢
        rw [sPair_r (Ne.symm hkp) (Ne.symm hkq)]
        exact hz
      · have hkt : k = t := by
          rcases fin4_cover hpq hpr (Ne.symm htp) hqr (Ne.symm htq) (Ne.symm htr) k with
            h | h | h | h
          · exact absurd h hkp
          · exact absurd h hkq
          · exact absurd h hkr
          · exact h
        rw [hkt, sPair_t htp htq htr]
        exact hw
private theorem parity_add_ite (c e : ℕ) : (c + (if c % 2 = e % 2 then 0 else 1)) % 2 = e % 2 := by
  have hc : c % 2 = 0 ∨ c % 2 = 1 := by omega
  have he : e % 2 = 0 ∨ e % 2 = 1 := by omega
  rcases hc with hc | hc <;> rcases he with he | he <;> simp [hc, he] <;> omega
private theorem parity_add_ite_succ (c e : ℕ) : (c + 1 + (if c % 2 = e % 2 then 1 else 0)) % 2 = e %
    2 := by
  have hc : c % 2 = 0 ∨ c % 2 = 1 := by omega
  have he : e % 2 = 0 ∨ e % 2 = 1 := by omega
  rcases hc with hc | hc <;> rcases he with he | he <;> simp [hc, he] <;> omega
private theorem sClass_two_mem_eq_empty {N : ℕ} {a a₁ : Fin 4 → ZMod N} (hD : (Finset.univ.filter
    fun k => a k ≠ a₁ k) = ∅) : a = a₁ := by
  funext k
  by_contra hne
  have hkD : k ∈ Finset.univ.filter fun k => a k ≠ a₁ k :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ k, hne⟩
  rw [hD] at hkD
  exact Finset.notMem_empty k hkD
private theorem sClass_two_mem_eq_pair {N : ℕ} [NeZero N] (hN : Odd N) {b : ZMod N} (hb0 : b ≠ 0) {p
    q r t : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠ r) (hqt : q ≠ t) (hrt : r ≠
    t) {u v : ℤ} {x y w₁ w₂ : ZMod N} (hx' : x = ((-u : ℤ) : ZMod N) * b) (hy' : y = ((-v : ℤ) :
    ZMod N) * b) (hw₁ : w₁ = b ∨ w₁ = -b) (hw₂ : w₂ = -w₁) {a : Fin 4 → ZMod N} (ha : IsSWt b a)
    (hap : a p = ((-u : ℤ) : ZMod N) * b) (haq : a q = ((-v : ℤ) : ZMod N) * b) (hD :
    (Finset.univ.filter fun k => a k ≠ sPair p q r x y b w₁ k) = {r, t}) : a = sPair p q r x y (-b)
    w₂ := by
  funext k
  rcases fin4_cover hpq hpr hpt hqr hqt hrt k with hk | hk | hk | hk
  · rw [hk, hap, hx', sPair_p]
  · rw [hk, haq, sPair_q hpq x y (-b) w₂, hy']
  · rw [hk]
    have hrD : r ∈ Finset.univ.filter fun k => a k ≠ sPair p q r x y b w₁ k := by
      rw [hD]; simp
    have hne : a r ≠ sPair p q r x y b w₁ r := (Finset.mem_filter.mp hrD).2
    have har : a r = -sPair p q r x y b w₁ r :=
      eq_neg_of_ne_of_sign hN hb0 (Or.inl (sPair_r hpr hqr x y b w₁)) (ha r)
        (Ne.symm hne)
    rw [har, sPair_r hpr hqr x y b w₁, sPair_r hpr hqr x y (-b) w₂]
  · rw [hk]
    have htD : t ∈ Finset.univ.filter fun k => a k ≠ sPair p q r x y b w₁ k := by
      rw [hD]; simp
    have hne : a t ≠ sPair p q r x y b w₁ t := (Finset.mem_filter.mp htD).2
    have hxt : sPair p q r x y b w₁ t = b ∨ sPair p q r x y b w₁ t = -b := by
      rw [sPair_t (Ne.symm hpt) (Ne.symm hqt) (Ne.symm hrt) x y b w₁]
      exact hw₁
    have hat : a t = -sPair p q r x y b w₁ t :=
      eq_neg_of_ne_of_sign hN hb0 hxt (ha t) (Ne.symm hne)
    rw [hat, sPair_t (Ne.symm hpt) (Ne.symm hqt) (Ne.symm hrt) x y b w₁,
      sPair_t (Ne.symm hpt) (Ne.symm hqt) (Ne.symm hrt) x y (-b) w₂, hw₂]
private theorem sClass_two_mem_diff {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} (he : e < 2) {p q r t : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r) (hpt : p ≠ t) (hqr
    : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t) {u v : ℤ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) {a a₁
    : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) (ha₁_swt : IsSWt b a₁) (ha₁_p : a₁ p = ((-u : ℤ) :
    ZMod N) * b) (ha₁_q : a₁ q = ((-v : ℤ) : ZMod N) * b) (hpar₁ : negCount b a₁ % 2 = e % 2) (hap :
    a p = ((-u : ℤ) : ZMod N) * b) (haq : a q = ((-v : ℤ) : ZMod N) * b) : (Finset.univ.filter fun k
    => a k ≠ a₁ k) = ∅ ∨ (Finset.univ.filter fun k => a k ≠ a₁ k) = {r, t} := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_sClass] at ha
  let D := Finset.univ.filter fun k => a k ≠ a₁ k
  have hDsub : D ⊆ {r, t} := by
    intro k hk
    rw [Finset.mem_filter] at hk
    by_contra h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    rcases fin4_cover hpq hpr hpt hqr hqt hrt k with hk' | hk' | hk' | hk'
    · rw [hk'] at hk
      exact hk.2 (by rw [hap, ha₁_p])
    · rw [hk'] at hk
      exact hk.2 (by rw [haq, ha₁_q])
    · exact h.1 hk'
    · exact h.2 hk'
  have hDcard : D.card % 2 = 0 := by
    have h := diff_card_parity hN hb.ne_zero ha.1 ha₁_swt
    rw [Nat.add_mod, ha.2, hpar₁] at h
    have he' : e % 2 = e := Nat.mod_eq_of_lt he
    rw [he'] at h
    have hee : (e + e) % 2 = 0 := by omega
    rwa [hee] at h
  have hDle : D.card ≤ 2 := by
    calc D.card ≤ ({r, t} : Finset (Fin 4)).card := Finset.card_le_card hDsub
      _ = 2 := Finset.card_pair hrt
  have hcases : D.card = 0 ∨ D.card = 2 := by omega
  rcases hcases with h0 | h2
  · left
    exact Finset.card_eq_zero.mp h0
  · right
    apply Finset.eq_of_subset_of_card_le hDsub
    rw [Finset.card_pair hrt, h2]
private theorem sClass_two_mem_par {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {p q r t : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠ r) (hqt
    : q ≠ t) (hrt : r ≠ t) {x y : ZMod N} {c : ℕ} (hc : c = (if x = -b then 1 else 0) + (if y = -b
    then 1 else 0)) {w₁ w₂ : ZMod N} (hw₁def : w₁ = if c % 2 = e % 2 then b else -b) (hw₂def : w₂ =
    if c % 2 = e % 2 then -b else b) : negCount b (sPair p q r x y b w₁) % 2 = e % 2 ∧ negCount b
    (sPair p q r x y (-b) w₂) % 2 = e % 2 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hbne : b ≠ -b := ZMod.ne_neg_self hN hb.ne_zero
  have hbterm : (if b = -b then 1 else 0) = 0 := by simp [hbne]
  have hlast₁ : (if w₁ = -b then 1 else 0) = (if c % 2 = e % 2 then 0 else 1) := by
    rw [hw₁def]
    by_cases hc' : c % 2 = e % 2
    · rw [if_pos hc', if_pos hc']
      simp [hbne]
    · rw [if_neg hc', if_neg hc']
      simp
  have hbb : (if (-b) = -b then 1 else 0) = 1 := by simp
  have hlast₂ : (if w₂ = -b then 1 else 0) = (if c % 2 = e % 2 then 1 else 0) := by
    rw [hw₂def]
    by_cases hc' : c % 2 = e % 2
    · rw [if_pos hc', if_pos hc']
      simp
    · rw [if_neg hc', if_neg hc']
      simp [hbne]
  constructor
  · rw [negCount_four hpq hpr hpt hqr hqt hrt, sPair_p, sPair_q hpq,
      sPair_r hpr hqr, sPair_t (Ne.symm hpt) (Ne.symm hqt) (Ne.symm hrt),
      hbterm, hlast₁, ← hc]
    simp only [Nat.add_zero]
    change (c + (if c % 2 = e % 2 then 0 else 1)) % 2 = e % 2
    exact parity_add_ite c e
  · rw [negCount_four hpq hpr hpt hqr hqt hrt, sPair_p, sPair_q hpq,
      sPair_r hpr hqr, sPair_t (Ne.symm hpt) (Ne.symm hqt) (Ne.symm hrt),
      hbb, hlast₂, ← hc]
    change (c + 1 + (if c % 2 = e % 2 then 1 else 0)) % 2 = e % 2
    exact parity_add_ite_succ c e
private theorem sClass_two_mem_wit {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} (he : e < 2) {p q r t : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r) (hpt : p ≠ t) (hqr
    : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t) {x y : ZMod N} (hx : x = b ∨ x = -b) (hy : y = b ∨ y = -b)
    {c : ℕ} (hc : c = (if x = -b then 1 else 0) + (if y = -b then 1 else 0)) {w₁ w₂ : ZMod N}
    (hw₁def : w₁ = if c % 2 = e % 2 then b else -b) (hw₂def : w₂ = if c % 2 = e % 2 then -b else b)
    : sPair p q r x y b w₁ ∈ sClass N b e ∧ sPair p q r x y (-b) w₂ ∈ sClass N b e ∧ sPair p q r x y
    b w₁ ≠ sPair p q r x y (-b) w₂ ∧ IsSWt b (sPair p q r x y b w₁) ∧ negCount b (sPair p q r x y b
    w₁) % 2 = e % 2 ∧ IsSWt b (sPair p q r x y (-b) w₂) ∧ negCount b (sPair p q r x y (-b) w₂) % 2 =
    e % 2 ∧ (w₁ = b ∨ w₁ = -b) ∧ (w₂ = b ∨ w₂ = -b) ∧ w₂ = -w₁ := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hbne : b ≠ -b := ZMod.ne_neg_self hN hb.ne_zero
  have hw₁ : w₁ = b ∨ w₁ = -b := by rw [hw₁def]; split_ifs <;> simp
  have hw₂ : w₂ = b ∨ w₂ = -b := by rw [hw₂def]; split_ifs <;> simp
  have hw₂neg : w₂ = -w₁ := by
    rw [hw₁def, hw₂def]
    by_cases hc' : c % 2 = e % 2 <;> simp [hc']
  have ha₁_swt : IsSWt b (sPair p q r x y b w₁) :=
    sPair_isSWt hpq hpr hqr (Ne.symm hpt) (Ne.symm hqt) (Ne.symm hrt) hx hy
      (Or.inl rfl) hw₁
  have ha₂_swt : IsSWt b (sPair p q r x y (-b) w₂) :=
    sPair_isSWt hpq hpr hqr (Ne.symm hpt) (Ne.symm hqt) (Ne.symm hrt) hx hy
      (Or.inr rfl) hw₂
  obtain ⟨ha₁_par, ha₂_par⟩ := sClass_two_mem_par hN3 hN hb hpq hpr hpt hqr hqt hrt
    hc hw₁def hw₂def
  have ha₁_mem : sPair p q r x y b w₁ ∈ sClass N b e := by
    rw [mem_sClass]
    exact ⟨ha₁_swt, by rw [ha₁_par, Nat.mod_eq_of_lt he]⟩
  have ha₂_mem : sPair p q r x y (-b) w₂ ∈ sClass N b e := by
    rw [mem_sClass]
    exact ⟨ha₂_swt, by rw [ha₂_par, Nat.mod_eq_of_lt he]⟩
  have ha₁_ne : sPair p q r x y b w₁ ≠ sPair p q r x y (-b) w₂ := by
    intro h
    have hr := congrFun h r
    rw [sPair_r hpr hqr x y b w₁, sPair_r hpr hqr x y (-b) w₂] at hr
    exact hbne hr
  exact ⟨ha₁_mem, ha₂_mem, ha₁_ne, ha₁_swt, ha₁_par, ha₂_swt, ha₂_par, hw₁, hw₂, hw₂neg⟩
private theorem sClass_two_mem_root {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} {α :
    Fin 4 → ℤ} (hα : IsD4Root α) : ∃ (p q r t : Fin 4) (u v : ℤ) (x y : ZMod N), p ≠ q ∧ p ≠ r ∧ p ≠
    t ∧ q ≠ r ∧ q ≠ t ∧ r ≠ t ∧ (u = 1 ∨ u = -1) ∧ (v = 1 ∨ v = -1) ∧ α = Pi.single p u + Pi.single
    q v ∧ x = ((-u : ℤ) : ZMod N) * b ∧ y = ((-v : ℤ) : ZMod N) * b ∧ (x = b ∨ x = -b) ∧ (y = b ∨ y
    = -b) := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨p, q, hpq, hup, hvp, hαeq⟩ := isD4Root_iff.mp hα
  let u : ℤ := α p
  let v : ℤ := α q
  have hu : u = 1 ∨ u = -1 := by simpa [u] using hup
  have hv : v = 1 ∨ v = -1 := by simpa [v] using hvp
  have hαeq' : α = Pi.single p u + Pi.single q v := by rw [hαeq]
  obtain ⟨r, hrp, hrq⟩ := Fin.exists_ne_and_ne_of_two_lt p q (by norm_num : 2 < 4)
  have hpr : p ≠ r := Ne.symm hrp
  have hqr : q ≠ r := Ne.symm hrq
  have hlt : ({p, q, r} : Finset (Fin 4)).card < (Finset.univ : Finset (Fin 4)).card := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
      Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton,
      Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨t, -, htnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at htnot
  obtain ⟨htp, htq, htr⟩ := htnot
  refine ⟨p, q, r, t, u, v, ((-u : ℤ) : ZMod N) * b, ((-v : ℤ) : ZMod N) * b,
    hpq, hpr, Ne.symm htp, hqr, Ne.symm htq, Ne.symm htr, hu, hv, hαeq', rfl, rfl,
    ?_, ?_⟩
  · rcases hu with h | h
    · right
      change ((-u : ℤ) : ZMod N) * b = -b
      rw [h]
      simp
    · left
      change ((-u : ℤ) : ZMod N) * b = b
      rw [h]
      simp
  · rcases hv with h | h
    · right
      change ((-v : ℤ) : ZMod N) * b = -b
      rw [h]
      simp
    · left
      change ((-v : ℤ) : ZMod N) * b = b
      rw [h]
      simp
private theorem sClass_two_mem_fwd {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} (he : e < 2) {p q r t : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r) (hpt : p ≠ t) (hqr
    : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t) {u v : ℤ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) {x y
    w₁ w₂ : ZMod N} (hx : x = b ∨ x = -b) (hy : y = b ∨ y = -b) (hx' : x = ((-u : ℤ) : ZMod N) * b)
    (hy' : y = ((-v : ℤ) : ZMod N) * b) (hw₁ : w₁ = b ∨ w₁ = -b) (hw₂ : w₂ = -w₁) (hpar₁ : negCount
    b (sPair p q r x y b w₁) % 2 = e % 2) {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) (hC : a + (2
    * b) • castW N (Pi.single p u + Pi.single q v) ∈ sClass N b e) : a = sPair p q r x y b w₁ ∨ a =
    sPair p q r x y (-b) w₂ := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_sClass] at ha hC
  obtain ⟨hap, haq⟩ := (isSWt_add_two_iff hN3 hN hb ha.1 hpq hu hv).mp hC.1
  have hcases := sClass_two_mem_diff hN3 hN hb he hpq hpr hpt hqr hqt hrt hu hv
    (mem_sClass.mpr ha)
    (sPair_isSWt hpq hpr hqr (Ne.symm hpt) (Ne.symm hqt) (Ne.symm hrt) hx hy
      (Or.inl rfl) hw₁)
    (by rw [sPair_p, hx']) (by rw [sPair_q hpq, hy']) hpar₁ hap haq
  rcases hcases with h0 | h2
  · left
    exact sClass_two_mem_eq_empty h0
  · right
    exact sClass_two_mem_eq_pair hN hb.ne_zero hpq hpr hpt hqr hqt hrt hx' hy' hw₁ hw₂
      ha.1 hap haq h2
private theorem sClass_two_mem_bwd {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {p q r t : Fin 4} (hpq : p ≠ q) {u v : ℤ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨
    v = -1) {x y w₁ w₂ : ZMod N} (hx' : x = ((-u : ℤ) : ZMod N) * b) (hy' : y = ((-v : ℤ) : ZMod N)
    * b) {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) (h : a = sPair p q r x y b w₁ ∨ a = sPair p q
    r x y (-b) w₂) : a + (2 * b) • castW N (Pi.single p u + Pi.single q v) ∈ sClass N b e := by
  rcases h with rfl | rfl
  · rw [mem_sClass] at ha ⊢
    refine ⟨(isSWt_add_two_iff hN3 hN hb ha.1 hpq hu hv).mpr
      ⟨by rw [sPair_p, hx'], by rw [sPair_q hpq, hy']⟩, ?_⟩
    have hpar := isSWt_add_two_parity hN3 hN hb ha.1 hpq hu hv
      (by rw [sPair_p, hx']) (by rw [sPair_q hpq, hy'])
    rw [hpar, ha.2]
  · rw [mem_sClass] at ha ⊢
    refine ⟨(isSWt_add_two_iff hN3 hN hb ha.1 hpq hu hv).mpr
      ⟨by rw [sPair_p, hx'], by rw [sPair_q hpq, hy']⟩, ?_⟩
    have hpar := isSWt_add_two_parity hN3 hN hb ha.1 hpq hu hv
      (by rw [sPair_p, hx']) (by rw [sPair_q hpq, hy'])
    rw [hpar, ha.2]
private theorem sClass_two_mem {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} (he : e < 2) {α : Fin 4 → ℤ} (hα : IsD4Root α) : ∃ a₁ ∈ sClass N b e, ∃ a₂ ∈
    sClass N b e, a₁ ≠ a₂ ∧ ∀ a ∈ sClass N b e, (a + (2 * b) • castW N α ∈ sClass N b e ↔ a = a₁ ∨ a
    = a₂) := by
  obtain ⟨p, q, r, t, u, v, x, y, hpq, hpr, hpt, hqr, hqt, hrt, hu, hv, hαeq', hx', hy',
    hx, hy⟩ := sClass_two_mem_root hN3 hN hα
  let c : ℕ := (if x = -b then 1 else 0) + (if y = -b then 1 else 0)
  let w₁ : ZMod N := if c % 2 = e % 2 then b else -b
  let w₂ : ZMod N := if c % 2 = e % 2 then -b else b
  obtain ⟨ha₁_mem, ha₂_mem, ha₁_ne, ha₁_swt, ha₁_par, ha₂_swt, ha₂_par, hw₁, hw₂,
    hw₂neg⟩ := sClass_two_mem_wit (p := p) (q := q) (r := r) (t := t) (x := x) (y := y)
      (w₁ := w₁) (w₂ := w₂) (c := c) hN3 hN hb he hpq hpr hpt hqr hqt hrt hx hy rfl rfl rfl
  refine ⟨sPair p q r x y b w₁, ha₁_mem, sPair p q r x y (-b) w₂, ha₂_mem, ha₁_ne, ?_⟩
  intro a ha
  constructor
  · intro hC
    exact sClass_two_mem_fwd (p := p) (q := q) (r := r) (t := t) (x := x) (y := y)
      (w₁ := w₁) (w₂ := w₂) hN3 hN hb he hpq hpr hpt hqr hqt hrt hu hv hx hy hx' hy'
      hw₁ hw₂neg ha₁_par ha (by simpa [hαeq'] using hC)
  · intro h
    exact by
      simpa [hαeq'] using sClass_two_mem_bwd (p := p) (q := q) (r := r) (t := t)
        (x := x) (y := y) (w₁ := w₁) (w₂ := w₂) hN3 hN hb hpq hu hv hx' hy' ha h
private theorem dot_single_pair {p q r t : Fin 4} (u v s w : ℤ) : (Pi.single p u + Pi.single q v :
    Fin 4 → ℤ) ⬝ᵥ (Pi.single r s + Pi.single t w : Fin 4 → ℤ) = (if p = r then u * s else 0) + (if p
    = t then u * w else 0) + (if q = r then v * s else 0) + (if q = t then v * w else 0) := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add]
  simp only [single_dotProduct, Pi.single_apply, mul_ite, mul_zero, mul_one]
  ring
private theorem coeff_eq_of_coord_eq {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b)
    {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) (h : ((-x : ℤ) : ZMod N) * b = ((-y : ℤ) :
    ZMod N) * b) : x = y := by
  have hc : ((-x : ℤ) : ZMod N) = ((-y : ℤ) : ZMod N) := hb.mul_right_cancel h
  push_cast at hc
  exact sign_eq_of_cast_eq hN3 hN hx hy (neg_inj.mp hc)
private theorem sClass_raise_adj_same_pq {p q r t : Fin 4} (hpr : p = r) (hqt : q = t) {u v s w : ℤ}
    (hus : u = s) (hvw : v = w) {γ γ' : Fin 4 → ℤ} (hγeq : γ = Pi.single p u + Pi.single q v) (hγ'eq
    : γ' = Pi.single r s + Pi.single t w) : γ = γ' := by
  funext k
  rw [hγeq, hγ'eq, hpr, hqt, hus, hvw]
private theorem sClass_raise_adj_same_pt {p q r t : Fin 4} (hpt : p = t) (hqr : q = r) {u v s w : ℤ}
    (huw : u = w) (hvs : v = s) {γ γ' : Fin 4 → ℤ} (hγeq : γ = Pi.single p u + Pi.single q v) (hγ'eq
    : γ' = Pi.single r s + Pi.single t w) : γ = γ' := by
  funext k
  rw [hγeq, hγ'eq, hpt, hqr, huw, hvs]
  simp [Pi.add_apply, add_comm]
private theorem sClass_raise_adj_share_p {p q r t : Fin 4} (hpr : p = r) (hpt : p ≠ t) (hqr : q ≠ r)
    (hqt : q ≠ t) {u v s w : ℤ} (hs : s = 1 ∨ s = -1) (hus : u = s) {γ γ' : Fin 4 → ℤ} (hγeq : γ =
    Pi.single p u + Pi.single q v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) : γ ⬝ᵥ γ' = 1 := by
  rw [hγeq, hγ'eq, dot_single_pair, if_pos hpr, if_neg hpt, if_neg hqr, if_neg hqt, hus]
  rcases hs with h | h <;> rw [h] <;> norm_num
private theorem sClass_raise_adj_share_pt {p q r t : Fin 4} (hpt : p = t) (hpr : p ≠ r) (hqr : q ≠
    r) (hqt : q ≠ t) {u v s w : ℤ} (hw : w = 1 ∨ w = -1) (huw : u = w) {γ γ' : Fin 4 → ℤ} (hγeq : γ
    = Pi.single p u + Pi.single q v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) : γ ⬝ᵥ γ' = 1
    := by
  rw [hγeq, hγ'eq, dot_single_pair, if_neg hpr, if_pos hpt, if_neg hqr, if_neg hqt, huw]
  rcases hw with h | h <;> rw [h] <;> norm_num
private theorem sClass_raise_adj_share_qr {p q r t : Fin 4} (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q =
    r) (hqt : q ≠ t) {u v s w : ℤ} (hs : s = 1 ∨ s = -1) (hvs : v = s) {γ γ' : Fin 4 → ℤ} (hγeq : γ
    = Pi.single p u + Pi.single q v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) : γ ⬝ᵥ γ' = 1
    := by
  rw [hγeq, hγ'eq, dot_single_pair, if_neg hpr, if_neg hpt, if_pos hqr, if_neg hqt, hvs]
  rcases hs with h | h <;> rw [h] <;> norm_num
private theorem sClass_raise_adj_share_qt {p q r t : Fin 4} (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠
    r) (hqt : q = t) {u v s w : ℤ} (hw : w = 1 ∨ w = -1) (hvw : v = w) {γ γ' : Fin 4 → ℤ} (hγeq : γ
    = Pi.single p u + Pi.single q v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) : γ ⬝ᵥ γ' = 1
    := by
  rw [hγeq, hγ'eq, dot_single_pair, if_neg hpr, if_neg hpt, if_neg hqr, if_pos hqt, hvw]
  rcases hw with h | h <;> rw [h] <;> norm_num
private theorem sClass_raise_adj_disjoint {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N}
    (hb : IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) {p q r t : Fin 4} (hpq : p
    ≠ q) (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠ r) (hrt : r ≠ t) {u v s w : ℤ} (hu : u = 1 ∨ u = -1)
    (hs : s = 1 ∨ s = -1) {γ γ' : Fin 4 → ℤ} (hγeq : γ = Pi.single p u + Pi.single q v) (hγ'eq : γ'
    = Pi.single r s + Pi.single t w) (hp : a p = ((-u : ℤ) : ZMod N) * b) (hr : a r = ((-s : ℤ) :
    ZMod N) * b) : ∃ γ'', IsD4Root γ'' ∧ a + (2 * b) • castW N γ'' ∈ sClass N b e ∧ γ ⬝ᵥ γ'' = 1 ∧
    γ' ⬝ᵥ γ'' = 1 := by
  rw [mem_sClass] at ha
  refine ⟨Pi.single p u + Pi.single r s, ?_, ?_, ?_, ?_⟩
  · exact isD4Root_single_add_single hpr hu hs
  · rw [mem_sClass]
    exact ⟨(isSWt_add_two_iff hN3 hN hb ha.1 hpr hu hs).mpr ⟨hp, hr⟩, by
      have hpar := isSWt_add_two_parity hN3 hN hb ha.1 hpr hu hs hp hr
      rw [hpar, ha.2]⟩
  · rw [hγeq, dot_single_pair, if_pos rfl, if_neg hpr, if_neg (Ne.symm hpq), if_neg hqr]
    rcases hu with h | h <;> rw [h] <;> norm_num
  · rw [hγ'eq, dot_single_pair, if_neg (Ne.symm hpr), if_pos rfl,
      if_neg (Ne.symm hpt), if_neg (Ne.symm hrt)]
    rcases hs with h | h <;> rw [h] <;> norm_num
private theorem sClass_raise_adj_p_eq_r {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N}
    (hb : IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) {γ γ' : Fin 4 → ℤ} {p q r t
    : Fin 4} (hpq : p ≠ q) (hpr : p = r) (hrt : r ≠ t) {u v s w : ℤ} (hu : u = 1 ∨ u = -1) (hv : v =
    1 ∨ v = -1) (hs : s = 1 ∨ s = -1) (hw : w = 1 ∨ w = -1) (hγeq : γ = Pi.single p u + Pi.single q
    v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) (hp : a p = ((-u : ℤ) : ZMod N) * b) (hq : a q =
    ((-v : ℤ) : ZMod N) * b) (hr : a r = ((-s : ℤ) : ZMod N) * b) (ht : a t = ((-w : ℤ) : ZMod N) *
    b) (hne : γ ≠ γ') : γ ⬝ᵥ γ' = 1 ∨ ∃ γ'', IsD4Root γ'' ∧ a + (2 * b) • castW N γ'' ∈ sClass N b e
    ∧ γ ⬝ᵥ γ'' = 1 ∧ γ' ⬝ᵥ γ'' = 1 := by
  by_cases hqt : q = t
  · exfalso
    apply hne
    have hus : u = s := coeff_eq_of_coord_eq hN3 hN hb hu hs (by rw [← hp, ← hr, hpr])
    have hvw : v = w := coeff_eq_of_coord_eq hN3 hN hb hv hw (by rw [← hq, ← ht, hqt])
    exact sClass_raise_adj_same_pq hpr hqt hus hvw hγeq hγ'eq
  · left
    have hpt : p ≠ t := by rw [hpr]; exact hrt
    have hqr : q ≠ r := by rw [← hpr]; exact Ne.symm hpq
    have hus : u = s := coeff_eq_of_coord_eq hN3 hN hb hu hs (by rw [← hp, ← hr, hpr])
    exact sClass_raise_adj_share_p hpr hpt hqr hqt hs hus hγeq hγ'eq
private theorem sClass_raise_adj_p_ne_r {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N}
    (hb : IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) {γ γ' : Fin 4 → ℤ} {p q r t
    : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r) (hrt : r ≠ t) {u v s w : ℤ} (hu : u = 1 ∨ u = -1) (hv : v =
    1 ∨ v = -1) (hs : s = 1 ∨ s = -1) (hw : w = 1 ∨ w = -1) (hγeq : γ = Pi.single p u + Pi.single q
    v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) (hp : a p = ((-u : ℤ) : ZMod N) * b) (hq : a q =
    ((-v : ℤ) : ZMod N) * b) (hr : a r = ((-s : ℤ) : ZMod N) * b) (ht : a t = ((-w : ℤ) : ZMod N) *
    b) (hne : γ ≠ γ') : γ ⬝ᵥ γ' = 1 ∨ ∃ γ'', IsD4Root γ'' ∧ a + (2 * b) • castW N γ'' ∈ sClass N b e
    ∧ γ ⬝ᵥ γ'' = 1 ∧ γ' ⬝ᵥ γ'' = 1 := by
  by_cases hpt : p = t
  · by_cases hqr : q = r
    · exfalso
      apply hne
      have huw : u = w := coeff_eq_of_coord_eq hN3 hN hb hu hw (by rw [← hp, ← ht, hpt])
      have hvs : v = s := coeff_eq_of_coord_eq hN3 hN hb hv hs (by rw [← hq, ← hr, hqr])
      exact sClass_raise_adj_same_pt hpt hqr huw hvs hγeq hγ'eq
    · left
      have hqt : q ≠ t := by rw [← hpt]; exact Ne.symm hpq
      have huw : u = w := coeff_eq_of_coord_eq hN3 hN hb hu hw (by rw [← hp, ← ht, hpt])
      exact sClass_raise_adj_share_pt hpt hpr hqr hqt hw huw hγeq hγ'eq
  · by_cases hqr : q = r
    · left
      have hqt : q ≠ t := fun h => hrt (hqr.symm.trans h)
      have hvs : v = s := coeff_eq_of_coord_eq hN3 hN hb hv hs (by rw [← hq, ← hr, hqr])
      exact sClass_raise_adj_share_qr hpr hpt hqr hqt hs hvs hγeq hγ'eq
    · by_cases hqt : q = t
      · left
        have hvw : v = w := coeff_eq_of_coord_eq hN3 hN hb hv hw (by rw [← hq, ← ht, hqt])
        exact sClass_raise_adj_share_qt hpr hpt hqr hqt hw hvw hγeq hγ'eq
      · right
        exact sClass_raise_adj_disjoint hN3 hN hb ha hpq hpr hpt hqr hrt hu hs
          hγeq hγ'eq hp hr
private theorem sClass_raise_adj {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) {γ γ' : Fin 4 → ℤ} (hγ : IsD4Root
    γ) (hγ' : IsD4Root γ') (h1 : a + (2 * b) • castW N γ ∈ sClass N b e) (h2 : a + (2 * b) • castW N
    γ' ∈ sClass N b e) (hne : γ ≠ γ') : γ ⬝ᵥ γ' = 1 ∨ ∃ γ'', IsD4Root γ'' ∧ a + (2 * b) • castW N
    γ'' ∈ sClass N b e ∧ γ ⬝ᵥ γ'' = 1 ∧ γ' ⬝ᵥ γ'' = 1 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_sClass] at ha h1 h2
  obtain ⟨p, q, hpq, hup, hvp, hγeq⟩ := isD4Root_iff.mp hγ
  let u : ℤ := γ p
  let v : ℤ := γ q
  have hu : u = 1 ∨ u = -1 := by simpa [u] using hup
  have hv : v = 1 ∨ v = -1 := by simpa [v] using hvp
  have hγeq' : γ = Pi.single p u + Pi.single q v := by rw [hγeq]
  obtain ⟨hp, hq⟩ := (isSWt_add_two_iff hN3 hN hb ha.1 hpq hu hv).mp
    (by simpa [hγeq'] using h1.1)
  obtain ⟨r, t, hrt, hsr, hwt, hγ'eq⟩ := isD4Root_iff.mp hγ'
  let s : ℤ := γ' r
  let w : ℤ := γ' t
  have hs : s = 1 ∨ s = -1 := by simpa [s] using hsr
  have hw : w = 1 ∨ w = -1 := by simpa [w] using hwt
  have hγ'eq' : γ' = Pi.single r s + Pi.single t w := by rw [hγ'eq]
  obtain ⟨hr, ht⟩ := (isSWt_add_two_iff hN3 hN hb ha.1 hrt hs hw).mp
    (by simpa [hγ'eq'] using h2.1)
  by_cases hpr : p = r
  · exact sClass_raise_adj_p_eq_r hN3 hN hb (mem_sClass.mpr ha) hpq hpr hrt hu hv hs hw
      hγeq' hγ'eq' hp hq hr ht hne
  · exact sClass_raise_adj_p_ne_r hN3 hN hb (mem_sClass.mpr ha) hpq hpr hrt hu hv hs hw
      hγeq' hγ'eq' hp hq hr ht hne
private theorem not_isSWt_of_three {N : ℕ} (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb : IsUnit b)
    {x : Fin 4 → ZMod N} {k : Fin 4} {t : ℤ} (ht : t = 1 ∨ t = -1) (hx : x k = (3 : ZMod N) * (t :
    ZMod N) * b) : ¬ IsSWt b x := by
  intro h
  have hk := h k
  rw [hx] at hk
  rcases hk with hk | hk
  · exact (three_sign_mul_ne_pm hN3 hN hb ht).1 hk
  · exact (three_sign_mul_ne_pm hN3 hN hb ht).2 hk
private theorem sub_two_smul_castW_apply {N : ℕ} (b : ZMod N) (a : Fin 4 → ZMod N) (δ : Fin 4 → ℤ)
    (k : Fin 4) : (a - (2 * b) • castW N δ) k = a k - (2 * b) * (δ k : ZMod N) := by
  simp [castW, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
private theorem add_two_sub_two_apply {N : ℕ} (b : ZMod N) (a : Fin 4 → ZMod N) (γ δ : Fin 4 → ℤ) (k
    : Fin 4) : (a + (2 * b) • castW N γ - (2 * b) • castW N δ) k = a k + (2 * b) * (γ k : ZMod N) -
    (2 * b) * (δ k : ZMod N) := by
  simp [castW, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
private theorem add_two_add_two_apply {N : ℕ} (b : ZMod N) (a : Fin 4 → ZMod N) (γ γ' : Fin 4 → ℤ)
    (k : Fin 4) : (a + (2 * b) • castW N γ' + (2 * b) • castW N γ) k = a k + (2 * b) * (γ' k : ZMod
    N) + (2 * b) * (γ k : ZMod N) := by
  simp [castW, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
private theorem not_mem_add_two_sub {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ γ' : Fin 4 → ℤ} {p : Fin 4} {u : ℤ} (hu : u = 1 ∨ u =
    -1) (hpγ : γ p = u) (hpγ' : γ' p = 0) (hap : a p = ((-u : ℤ) : ZMod N) * b) : a + (2 * b) •
    castW N (γ' - γ) ∉ sClass N b e := by
  rw [mem_sClass]
  rintro ⟨hSWt, -⟩
  have hcoef : ((γ' - γ) p : ℤ) = -u := by
    rw [Pi.sub_apply, hpγ', hpγ]
    ring
  exact not_isSWt_of_three hN3 hN hb (neg_sign hu) (by
    rw [add_two_smul_castW_apply, hcoef, hap]
    push_cast
    ring) hSWt
private theorem not_mem_sub_two_sub {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ γ' : Fin 4 → ℤ} {q : Fin 4} {s : ℤ} (hs : s = 1 ∨ s =
    -1) (hqγ : γ q = 0) (hqγ' : γ' q = s) (haq : a q = ((-s : ℤ) : ZMod N) * b) : a - (2 * b) •
    castW N (γ' - γ) ∉ sClass N b e := by
  rw [mem_sClass]
  rintro ⟨hSWt, -⟩
  have hcoef : ((γ' - γ) q : ℤ) = s := by
    rw [Pi.sub_apply, hqγ', hqγ]
    ring
  exact not_isSWt_of_three hN3 hN hb (neg_sign hs) (by
    rw [sub_two_smul_castW_apply, hcoef, haq]
    push_cast
    ring) hSWt
private theorem not_mem_add_two_gamma_sub {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N}
    (hb : IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ γ' : Fin 4 → ℤ} {p : Fin 4} {u : ℤ} (hu : u = 1
    ∨ u = -1) (hpγ : γ p = u) (hpγ' : γ' p = 0) (hap : a p = ((-u : ℤ) : ZMod N) * b) : a + (2 * b)
    • castW N γ - (2 * b) • castW N (γ' - γ) ∉ sClass N b e := by
  rw [mem_sClass]
  rintro ⟨hSWt, -⟩
  have hcoef : ((γ' - γ) p : ℤ) = -u := by
    rw [Pi.sub_apply, hpγ', hpγ]
    ring
  exact not_isSWt_of_three hN3 hN hb hu (by
    rw [add_two_sub_two_apply, hpγ, hcoef, hap]
    push_cast
    ring) hSWt
private theorem not_mem_add_two_gamma'_add {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod
    N} (hb : IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ γ' : Fin 4 → ℤ} {k : Fin 4} {t : ℤ} (ht : t =
    1 ∨ t = -1) (hkγ : γ k = t) (hkγ' : γ' k = t) (hak : a k = ((-t : ℤ) : ZMod N) * b) : a + (2 *
    b) • castW N γ' + (2 * b) • castW N γ ∉ sClass N b e := by
  rw [mem_sClass]
  rintro ⟨hSWt, -⟩
  exact not_isSWt_of_three hN3 hN hb ht (by
    rw [add_two_add_two_apply, hkγ, hkγ', hak]
    push_cast
    ring) hSWt
private theorem sClass_raise_edge_same_pq {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N}
    (hb : IsUnit b) {p q r t : Fin 4} (hpq : p ≠ q) (hpr : p = r) (hqt : q = t) (hrt : r ≠ t) {u v s
    w : ℤ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) (hus : u = s) (hvw : v = w) {γ γ' : Fin 4 →
    ℤ} (hγeq : γ = Pi.single p u + Pi.single q v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) (hdot
    : γ ⬝ᵥ γ' = 1) : False := by
  have hpt : p ≠ t := by rw [hpr]; exact hrt
  have hqr : q ≠ r := by rw [← hpr]; exact Ne.symm hpq
  have h2 : γ ⬝ᵥ γ' = 2 := by
    rw [hγeq, hγ'eq, dot_single_pair, if_pos hpr, if_neg hpt, if_neg hqr, if_pos hqt,
      ← hus, ← hvw]
    rcases hu with h | h <;> rcases hv with h' | h' <;> rw [h, h'] <;> norm_num
  rw [hdot] at h2
  omega
private theorem sClass_raise_edge_same_pt {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N}
    (hb : IsUnit b) {p q r t : Fin 4} (hpq : p ≠ q) (hpt : p = t) (hqr : q = r) (hrt : r ≠ t) {u v s
    w : ℤ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) (huw : u = w) (hvs : v = s) {γ γ' : Fin 4 →
    ℤ} (hγeq : γ = Pi.single p u + Pi.single q v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) (hdot
    : γ ⬝ᵥ γ' = 1) : False := by
  have hpr' : p ≠ r := by rw [hpt]; exact Ne.symm hrt
  have hqt' : q ≠ t := by rw [← hpt]; exact Ne.symm hpq
  have h2 : γ ⬝ᵥ γ' = 2 := by
    rw [hγeq, hγ'eq, dot_single_pair, if_neg hpr', if_pos hpt, if_pos hqr, if_neg hqt',
      ← huw, ← hvs]
    rcases hu with h | h <;> rcases hv with h' | h' <;> rw [h, h'] <;> norm_num
  rw [hdot] at h2
  omega
private theorem sClass_raise_edge_disjoint {p q r t : Fin 4} (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠
    r) (hqt : q ≠ t) {u v s w : ℤ} {γ γ' : Fin 4 → ℤ} (hγeq : γ = Pi.single p u + Pi.single q v)
    (hγ'eq : γ' = Pi.single r s + Pi.single t w) (hdot : γ ⬝ᵥ γ' = 1) : False := by
  have h0 : γ ⬝ᵥ γ' = 0 := by
    rw [hγeq, hγ'eq, dot_single_pair, if_neg hpr, if_neg hpt, if_neg hqr, if_neg hqt]
    ring
  rw [hdot] at h0
  omega
private theorem sClass_raise_edge_pp {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb
    : IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ γ' : Fin 4 → ℤ} {p q r t : Fin 4} (hpq : p ≠ q) (hpr
    : p = r) (hqt : q ≠ t) (hrt : r ≠ t) {u v s w : ℤ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1)
    (hs : s = 1 ∨ s = -1) (hw : w = 1 ∨ w = -1) (hus : u = s) (hγeq : γ = Pi.single p u + Pi.single
    q v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) (hp : a p = ((-u : ℤ) : ZMod N) * b) (hq : a q
    = ((-v : ℤ) : ZMod N) * b) (ht : a t = ((-w : ℤ) : ZMod N) * b) : a + (2 * b) • castW N (γ' - γ)
    ∉ sClass N b e ∧ a - (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a + (2 * b) • castW N γ - (2 *
    b) • castW N (γ' - γ) ∉ sClass N b e ∧ a + (2 * b) • castW N γ' + (2 * b) • castW N γ ∉ sClass N
    b e := by
  have hpt : p ≠ t := by rw [hpr]; exact hrt
  have hqr : q ≠ r := by rw [← hpr]; exact Ne.symm hpq
  have hqγ : γ q = v := by rw [hγeq]; simp [Ne.symm hpq]
  have hqγ' : γ' q = 0 := by rw [hγ'eq]; simp [hqr, hqt]
  have htγ : γ t = 0 := by rw [hγeq]; simp [Ne.symm hpt, Ne.symm hqt]
  have htγ' : γ' t = w := by rw [hγ'eq]; simp [Ne.symm hrt]
  have hkγ : γ p = u := by rw [hγeq]; simp [hpq]
  have hkγ' : γ' p = u := by rw [hpr, hγ'eq]; simp [hrt, hus]
  exact ⟨not_mem_add_two_sub hN3 hN hb hv hqγ hqγ' hq,
    not_mem_sub_two_sub hN3 hN hb hw htγ htγ' ht,
    not_mem_add_two_gamma_sub hN3 hN hb hv hqγ hqγ' hq,
    not_mem_add_two_gamma'_add hN3 hN hb hu hkγ hkγ' hp⟩
private theorem sClass_raise_edge_pt {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb
    : IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ γ' : Fin 4 → ℤ} {p q r t : Fin 4} (hpq : p ≠ q) (hpt
    : p = t) (hqr : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t) {u v s w : ℤ} (hu : u = 1 ∨ u = -1) (hv : v =
    1 ∨ v = -1) (hs : s = 1 ∨ s = -1) (hw : w = 1 ∨ w = -1) (huw : u = w) (hγeq : γ = Pi.single p u
    + Pi.single q v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) (hp : a p = ((-u : ℤ) : ZMod N) *
    b) (hq : a q = ((-v : ℤ) : ZMod N) * b) (hr : a r = ((-s : ℤ) : ZMod N) * b) : a + (2 * b) •
    castW N (γ' - γ) ∉ sClass N b e ∧ a - (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a + (2 * b) •
    castW N γ - (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a + (2 * b) • castW N γ' + (2 * b) •
    castW N γ ∉ sClass N b e := by
  have hpr' : p ≠ r := by rw [hpt]; exact Ne.symm hrt
  have hqγ : γ q = v := by rw [hγeq]; simp [Ne.symm hpq]
  have hqγ' : γ' q = 0 := by rw [hγ'eq]; simp [hqr, hqt]
  have hrγ : γ r = 0 := by rw [hγeq]; simp [Ne.symm hpr', Ne.symm hqr]
  have hrγ' : γ' r = s := by rw [hγ'eq]; simp [hrt]
  have hkγ : γ p = u := by rw [hγeq]; simp [hpq]
  have hkγ' : γ' p = u := by rw [hpt, hγ'eq]; simp [Ne.symm hrt, huw]
  exact ⟨not_mem_add_two_sub hN3 hN hb hv hqγ hqγ' hq,
    not_mem_sub_two_sub hN3 hN hb hs hrγ hrγ' hr,
    not_mem_add_two_gamma_sub hN3 hN hb hv hqγ hqγ' hq,
    not_mem_add_two_gamma'_add hN3 hN hb hu hkγ hkγ' hp⟩
private theorem sClass_raise_edge_qr {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb
    : IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ γ' : Fin 4 → ℤ} {p q r t : Fin 4} (hpq : p ≠ q) (hpr
    : p ≠ r) (hpt : p ≠ t) (hqr : q = r) (hrt : r ≠ t) {u v s w : ℤ} (hu : u = 1 ∨ u = -1) (hv : v =
    1 ∨ v = -1) (hs : s = 1 ∨ s = -1) (hw : w = 1 ∨ w = -1) (hvs : v = s) (hγeq : γ = Pi.single p u
    + Pi.single q v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) (hp : a p = ((-u : ℤ) : ZMod N) *
    b) (hq : a q = ((-v : ℤ) : ZMod N) * b) (ht : a t = ((-w : ℤ) : ZMod N) * b) : a + (2 * b) •
    castW N (γ' - γ) ∉ sClass N b e ∧ a - (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a + (2 * b) •
    castW N γ - (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a + (2 * b) • castW N γ' + (2 * b) •
    castW N γ ∉ sClass N b e := by
  have hqt : q ≠ t := fun h => hrt (hqr.symm.trans h)
  have hpγ : γ p = u := by rw [hγeq]; simp [hpq]
  have hpγ' : γ' p = 0 := by rw [hγ'eq]; simp [hpr, hpt]
  have htγ : γ t = 0 := by rw [hγeq]; simp [Ne.symm hpt, Ne.symm hqt]
  have htγ' : γ' t = w := by rw [hγ'eq]; simp [Ne.symm hrt]
  have hkγ : γ q = v := by rw [hγeq]; simp [Ne.symm hpq]
  have hkγ' : γ' q = v := by rw [hqr, hγ'eq]; simp [hrt, hvs]
  exact ⟨not_mem_add_two_sub hN3 hN hb hu hpγ hpγ' hp,
    not_mem_sub_two_sub hN3 hN hb hw htγ htγ' ht,
    not_mem_add_two_gamma_sub hN3 hN hb hu hpγ hpγ' hp,
    not_mem_add_two_gamma'_add hN3 hN hb hv hkγ hkγ' hq⟩
private theorem sClass_raise_edge_qt {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb
    : IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ γ' : Fin 4 → ℤ} {p q r t : Fin 4} (hpq : p ≠ q) (hpr
    : p ≠ r) (hpt : p ≠ t) (hqt : q = t) (hrt : r ≠ t) {u v s w : ℤ} (hu : u = 1 ∨ u = -1) (hv : v =
    1 ∨ v = -1) (hs : s = 1 ∨ s = -1) (hw : w = 1 ∨ w = -1) (hvw : v = w) (hγeq : γ = Pi.single p u
    + Pi.single q v) (hγ'eq : γ' = Pi.single r s + Pi.single t w) (hp : a p = ((-u : ℤ) : ZMod N) *
    b) (hq : a q = ((-v : ℤ) : ZMod N) * b) (hr : a r = ((-s : ℤ) : ZMod N) * b) : a + (2 * b) •
    castW N (γ' - γ) ∉ sClass N b e ∧ a - (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a + (2 * b) •
    castW N γ - (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a + (2 * b) • castW N γ' + (2 * b) •
    castW N γ ∉ sClass N b e := by
  have hqr : q ≠ r := fun h => hrt (h.symm.trans hqt)
  have hpγ : γ p = u := by rw [hγeq]; simp [hpq]
  have hpγ' : γ' p = 0 := by rw [hγ'eq]; simp [hpr, hpt]
  have hrγ : γ r = 0 := by rw [hγeq]; simp [Ne.symm hpr, Ne.symm hqr]
  have hrγ' : γ' r = s := by rw [hγ'eq]; simp [hrt]
  have hkγ : γ q = v := by rw [hγeq]; simp [Ne.symm hpq]
  have hkγ' : γ' q = v := by rw [hqt, hγ'eq]; simp [Ne.symm hrt, hvw]
  exact ⟨not_mem_add_two_sub hN3 hN hb hu hpγ hpγ' hp,
    not_mem_sub_two_sub hN3 hN hb hs hrγ hrγ' hr,
    not_mem_add_two_gamma_sub hN3 hN hb hu hpγ hpγ' hp,
    not_mem_add_two_gamma'_add hN3 hN hb hv hkγ hkγ' hq⟩
private theorem sClass_raise_edge_p_eq_r {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N}
    (hb : IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ γ' : Fin 4 → ℤ} {p q r t : Fin 4} (hpq : p ≠ q)
    (hpr : p = r) (hrt : r ≠ t) {u v s w : ℤ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) (hs : s =
    1 ∨ s = -1) (hw : w = 1 ∨ w = -1) (hγeq : γ = Pi.single p u + Pi.single q v) (hγ'eq : γ' =
    Pi.single r s + Pi.single t w) (hp : a p = ((-u : ℤ) : ZMod N) * b) (hq : a q = ((-v : ℤ) : ZMod
    N) * b) (hr : a r = ((-s : ℤ) : ZMod N) * b) (ht : a t = ((-w : ℤ) : ZMod N) * b) (hdot : γ ⬝ᵥ
    γ' = 1) : a + (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a - (2 * b) • castW N (γ' - γ) ∉
    sClass N b e ∧ a + (2 * b) • castW N γ - (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a + (2 * b)
    • castW N γ' + (2 * b) • castW N γ ∉ sClass N b e := by
  by_cases hqt : q = t
  · exfalso
    have hus : u = s := coeff_eq_of_coord_eq hN3 hN hb hu hs (by rw [← hp, ← hr, hpr])
    have hvw : v = w := coeff_eq_of_coord_eq hN3 hN hb hv hw (by rw [← hq, ← ht, hqt])
    exact sClass_raise_edge_same_pq hN3 hN hb hpq hpr hqt hrt hu hv hus hvw hγeq hγ'eq hdot
  · have hus : u = s := coeff_eq_of_coord_eq hN3 hN hb hu hs (by rw [← hp, ← hr, hpr])
    exact sClass_raise_edge_pp hN3 hN hb hpq hpr hqt hrt hu hv hs hw hus hγeq hγ'eq hp hq ht
private theorem sClass_raise_edge_p_ne_r {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N}
    (hb : IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} {γ γ' : Fin 4 → ℤ} {p q r t : Fin 4} (hpq : p ≠ q)
    (hpr : p ≠ r) (hrt : r ≠ t) {u v s w : ℤ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) (hs : s =
    1 ∨ s = -1) (hw : w = 1 ∨ w = -1) (hγeq : γ = Pi.single p u + Pi.single q v) (hγ'eq : γ' =
    Pi.single r s + Pi.single t w) (hp : a p = ((-u : ℤ) : ZMod N) * b) (hq : a q = ((-v : ℤ) : ZMod
    N) * b) (hr : a r = ((-s : ℤ) : ZMod N) * b) (ht : a t = ((-w : ℤ) : ZMod N) * b) (hdot : γ ⬝ᵥ
    γ' = 1) : a + (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a - (2 * b) • castW N (γ' - γ) ∉
    sClass N b e ∧ a + (2 * b) • castW N γ - (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a + (2 * b)
    • castW N γ' + (2 * b) • castW N γ ∉ sClass N b e := by
  by_cases hpt : p = t
  · by_cases hqr : q = r
    · exfalso
      have huw : u = w := coeff_eq_of_coord_eq hN3 hN hb hu hw (by rw [← hp, ← ht, hpt])
      have hvs : v = s := coeff_eq_of_coord_eq hN3 hN hb hv hs (by rw [← hq, ← hr, hqr])
      exact sClass_raise_edge_same_pt hN3 hN hb hpq hpt hqr hrt hu hv huw hvs hγeq hγ'eq hdot
    · have hqt : q ≠ t := by rw [← hpt]; exact Ne.symm hpq
      have huw : u = w := coeff_eq_of_coord_eq hN3 hN hb hu hw (by rw [← hp, ← ht, hpt])
      exact sClass_raise_edge_pt hN3 hN hb hpq hpt hqr hqt hrt hu hv hs hw huw
        hγeq hγ'eq hp hq hr
  · by_cases hqr : q = r
    · have hqt : q ≠ t := fun h => hrt (hqr.symm.trans h)
      have hvs : v = s := coeff_eq_of_coord_eq hN3 hN hb hv hs (by rw [← hq, ← hr, hqr])
      exact sClass_raise_edge_qr hN3 hN hb hpq hpr hpt hqr hrt hu hv hs hw hvs
        hγeq hγ'eq hp hq ht
    · by_cases hqt : q = t
      · have hvw : v = w := coeff_eq_of_coord_eq hN3 hN hb hv hw (by rw [← hq, ← ht, hqt])
        exact sClass_raise_edge_qt hN3 hN hb hpq hpr hpt hqt hrt hu hv hs hw hvw
          hγeq hγ'eq hp hq hr
      · exfalso
        exact sClass_raise_edge_disjoint hpr hpt hqr hqt hγeq hγ'eq hdot
private theorem sClass_raise_edge {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} {a : Fin 4 → ZMod N} (ha : a ∈ sClass N b e) {γ γ' : Fin 4 → ℤ} (hγ : IsD4Root
    γ) (hγ' : IsD4Root γ') (h1 : a + (2 * b) • castW N γ ∈ sClass N b e) (h2 : a + (2 * b) • castW N
    γ' ∈ sClass N b e) (hdot : γ ⬝ᵥ γ' = 1) : a + (2 * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a - (2
    * b) • castW N (γ' - γ) ∉ sClass N b e ∧ a + (2 * b) • castW N γ - (2 * b) • castW N (γ' - γ) ∉
    sClass N b e ∧ a + (2 * b) • castW N γ' + (2 * b) • castW N γ ∉ sClass N b e := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  rw [mem_sClass] at ha h1 h2
  obtain ⟨p, q, hpq, hup, hvp, hγeq⟩ := isD4Root_iff.mp hγ
  let u : ℤ := γ p
  let v : ℤ := γ q
  have hu : u = 1 ∨ u = -1 := by simpa [u] using hup
  have hv : v = 1 ∨ v = -1 := by simpa [v] using hvp
  have hγeq' : γ = Pi.single p u + Pi.single q v := by rw [hγeq]
  obtain ⟨hp, hq⟩ := (isSWt_add_two_iff hN3 hN hb ha.1 hpq hu hv).mp
    (by simpa [hγeq'] using h1.1)
  obtain ⟨r, t, hrt, hsr, hwt, hγ'eq⟩ := isD4Root_iff.mp hγ'
  let s : ℤ := γ' r
  let w : ℤ := γ' t
  have hs : s = 1 ∨ s = -1 := by simpa [s] using hsr
  have hw : w = 1 ∨ w = -1 := by simpa [w] using hwt
  have hγ'eq' : γ' = Pi.single r s + Pi.single t w := by rw [hγ'eq]
  obtain ⟨hr, ht⟩ := (isSWt_add_two_iff hN3 hN hb ha.1 hrt hs hw).mp
    (by simpa [hγ'eq'] using h2.1)
  by_cases hpr : p = r
  · exact sClass_raise_edge_p_eq_r hN3 hN hb hpq hpr hrt hu hv hs hw hγeq' hγ'eq'
      hp hq hr ht hdot
  · exact sClass_raise_edge_p_ne_r hN3 hN hb hpq hpr hrt hu hv hs hw hγeq' hγ'eq'
      hp hq hr ht hdot
private theorem sWt_isSmallClass {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b : ZMod N} (hb :
    IsUnit b) {e : ℕ} (he : e < 2) : IsSmallClass N (2 * b) (sClass N b e) := by
  refine ⟨hN3, hN, (isUnit_two_zmod hN).mul hb, sClass_card_eq hN3 hN hb he, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact sClass_neg_mem hN3 hN hb ha
  · intro β hβ a ha
    exact sClass_reflW_mem hN3 hN hb hβ ha
  · intro a ha α hα k hk hC
    exact sClass_step ha hα hk hC
  · intro a ha α hα hC
    exact sClass_sub_not_mem hN3 hN hb ha hα hC
  · intro a ha α hα hC
    exact sClass_reflW_eq hN3 hN hb ha hα hC
  · intro a ha a' ha' hne hneg
    exact sClass_adj hN3 hN hb ha ha' hne hneg
  · intro a ha γ hγ
    exact sClass_ne_neg hN3 hN hb ha hγ
  · intro a ha γ β hγ hβ h1 h2 h3 h4
    exact sClass_triangle hN3 hN hb ha hγ hβ h1 h2 h3 h4
  · intro α hα
    exact sClass_two_mem hN3 hN hb he hα
  · intro _ a ha γ γ' hγ hγ' h1 h2 hne
    exact sClass_raise_adj hN3 hN hb ha hγ hγ' h1 h2 hne
  · intro _ a ha γ γ' hγ hγ' h1 h2 hdot
    exact sClass_raise_edge hN3 hN hb ha hγ hγ' h1 h2 hdot

theorem isSmallClass_sWt {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN : Odd N) {b σ : ZMod N}
    (hb : IsUnit b) (hσ : σ = 2 * b ∨ σ = -(2 * b)) {e : ℕ} (he : e < 2) :
    IsSmallClass N σ (Finset.univ.filter fun a => IsSWt b a ∧ negCount b a % 2 = e) := by
  rcases hσ with rfl | rfl
  · exact sWt_isSmallClass hN3 hN hb he
  · exact (sWt_isSmallClass hN3 hN hb he).neg

end CFSG.LieType.D4Small
