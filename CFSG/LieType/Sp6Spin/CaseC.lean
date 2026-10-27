module

public import CFSG.LieType.Sp6Spin.RootFacts
public import CFSG.LieType.Sp6Spin.CaseAB
public import CFSG.LieType.Sp6Spin.Signs

public section

namespace CFSG.LieType.Sp6Spin

open CFSG.LieType.TorusWeights CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin
  QuadraticMap

attribute [local instance] Fintype.ofFinite Classical.propDecidable

theorem neg_spinWt {N : ℕ} (x : ZMod N) (σ : Fin 3 → Bool) :
    -spinWt x σ = spinWt x (fun i => !σ i) := by
  funext i
  cases h : σ i <;> simp [spinWt, h]

private theorem two_mul_eq_zero {N : ℕ} (hN : Odd N) {y : ZMod N}
    (h : (2 : ZMod N) * y = 0) : y = 0 := by
  have h2 : y + y = 0 := by rwa [two_mul] at h
  exact (ZMod.add_self_eq_zero_iff_eq_zero hN).mp h2

private theorem ne_neg_of_ne_zero {N : ℕ} (hN : Odd N) {x : ZMod N} (hx : x ≠ 0) :
    x ≠ -x := by
  intro h
  apply hx
  have h2 : x + x = 0 := by linear_combination h
  exact (ZMod.add_self_eq_zero_iff_eq_zero hN).mp h2

private theorem natCast_ne_zero {N : ℕ} {k : ℕ} (hk0 : 1 ≤ k) (hkN : k < N) :
    (k : ZMod N) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hk : k = 0 := Nat.eq_zero_of_dvd_of_lt h hkN
  omega

private theorem two_mul_ne_zero {N : ℕ} (hN : Odd N) {x : ZMod N} (hx : x ≠ 0) :
    (2 : ZMod N) * x ≠ 0 :=
  fun h => hx (two_mul_eq_zero hN h)

private theorem two_mul_cancel {N : ℕ} (hN : Odd N) {a b : ZMod N}
    (h : (2 : ZMod N) * a = 2 * b) : a = b := by
  have h' : (2 : ZMod N) * (a - b) = 0 := by rw [mul_sub, h, sub_self]
  exact sub_eq_zero.mp (two_mul_eq_zero hN h')

private theorem eq_pm_of_pm_add {N : ℕ} (hN : Odd N) {x : ZMod N} (hx : x ≠ 0)
    {y k : ZMod N} (hy : y = x ∨ y = -x) (h : y + k = x ∨ y + k = -x) :
    k = 0 ∨ k = 2 * x ∨ k = -(2 * x) := by
  have h2x : (2 : ZMod N) * x ≠ 0 := two_mul_ne_zero hN hx
  have h2x' : x + x ≠ 0 := by rwa [← two_mul]
  rcases hy with rfl | rfl
  · rcases h with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (Or.inr (by linear_combination h))
  · rcases h with h | h
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inl (by linear_combination h)

private theorem eq_pm_of_pm_add_int {N : ℕ} (hN : Odd N) {x : ZMod N} (hx : x ≠ 0)
    {y k : ZMod N} {c : ℤ} (hc : c = 1 ∨ c = -1) (hy : y = x ∨ y = -x)
    (h : y + k * (c : ZMod N) = x ∨ y + k * (c : ZMod N) = -x) :
    k = 0 ∨ k = 2 * x ∨ k = -(2 * x) := by
  rcases hc with rfl | rfl
  · simpa using eq_pm_of_pm_add hN hx hy h
  · rw [Int.cast_neg, Int.cast_one, mul_neg, mul_one] at h
    rcases hy with rfl | rfl
    · rcases h with h | h
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (Or.inl (by linear_combination -h))
    · rcases h with h | h
      · exact Or.inr (Or.inr (by linear_combination -h))
      · exact Or.inl (by linear_combination -h)

private theorem three_mul_ne_pm {N : ℕ} (hN : Odd N) {x : ZMod N} (hx : x ≠ 0) :
    (3 : ZMod N) * x ≠ x ∧ (3 : ZMod N) * x ≠ -x ∧
      -((3 : ZMod N) * x) ≠ x ∧ -((3 : ZMod N) * x) ≠ -x := by
  have h2x : (2 : ZMod N) * x ≠ 0 := two_mul_ne_zero hN hx
  have h4x : (4 : ZMod N) * x ≠ 0 := by
    have h : (2 : ZMod N) * (2 * x) ≠ 0 := two_mul_ne_zero hN h2x
    rwa [show (2 : ZMod N) * (2 * x) = 4 * x by ring] at h
  have h1 : (3 : ZMod N) * x ≠ x := by
    intro h
    apply h2x
    linear_combination h
  have h2 : (3 : ZMod N) * x ≠ -x := by
    intro h
    apply h4x
    linear_combination h
  exact ⟨h1, h2, fun h => h2 (by simpa using congrArg Neg.neg h),
    fun h => h1 (by simpa using congrArg Neg.neg h)⟩

theorem spinWt_add_spinWt_eq_zero_iff {N : ℕ} (hN : Odd N) {x : ZMod N} (hx : x ≠ 0)
    {σ τ : Fin 3 → Bool} : spinWt x σ + spinWt x τ = 0 ↔ τ = fun i => !σ i := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, spinWt] at hi
    by_cases hσ : σ i
    · by_cases hτ : τ i
      · exfalso
        have h2 : x + x = 0 := by simpa [hσ, hτ] using hi
        exact hx ((ZMod.add_self_eq_zero_iff_eq_zero hN).mp h2)
      · simp [hσ, hτ]
    · by_cases hτ : τ i
      · simp [hσ, hτ]
      · exfalso
        have h' : -x + -x = 0 := by simpa [hσ, hτ] using hi
        have h2 : x + x = 0 := by simpa using congrArg Neg.neg h'
        exact hx ((ZMod.add_self_eq_zero_iff_eq_zero hN).mp h2)
  · intro h
    rw [h]
    funext i
    cases hσ : σ i <;> simp [spinWt, hσ]

namespace SpinSetting

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (S : SpinSetting K V)

theorem IsSpinPattern.neg {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x) :
    S.IsSpinPattern (-x) := by
  refine ⟨?_, fun a => ?_⟩
  · intro h
    exact hP.ne_zero (neg_eq_zero.mp h)
  · rw [hP.mult_eq]
    congr 1
    simp only [neg_neg, or_comm]

theorem IsSpinPattern.mult_spinWt {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    (σ : Fin 3 → Bool) : S.mult (spinWt x σ) = 1 := by
  rw [hP.mult_eq]
  exact if_pos fun i => by cases h : σ i <;> simp [spinWt, h]

theorem IsSpinPattern.mult_eq_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {a : Fin 3 → ZMod (Nat.card Kˣ)} (ha : ∀ σ, a ≠ spinWt x σ) : S.mult a = 0 := by
  rw [hP.mult_eq, if_neg]
  rintro h
  refine ha (fun i => decide (a i = x)) ?_
  funext i
  have hi := h i
  by_cases hx : a i = x
  · simp [spinWt, hx]
  · have hnx : a i = -x := hi.resolve_left hx
    have hx' : x ≠ -x := ne_neg_of_ne_zero odd_natCard_units hP.ne_zero
    have hx'' : ¬ a i = x := hx
    simp [spinWt, hx, hnx, hx''] at hi ⊢

theorem IsSpinPattern.exists_ne_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    (σ : Fin 3 → Bool) : ∃ v ∈ S.X (spinWt x σ), v ≠ 0 := by
  have h1 : S.mult (spinWt x σ) = 1 := hP.mult_spinWt S σ
  have hne : S.X (spinWt x σ) ≠ ⊥ := by
    intro h
    rw [S.X_eq_bot_iff.mp h] at h1
    omega
  exact (Submodule.ne_bot_iff (S.X (spinWt x σ))).mp hne

theorem IsSpinPattern.eq_smul {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {σ : Fin 3 → Bool} {u v : V} (hu : u ∈ S.X (spinWt x σ)) (hu0 : u ≠ 0)
    (hv : v ∈ S.X (spinWt x σ)) : ∃ c : K, v = c • u := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := K) (V := S.X (spinWt x σ))
    ⟨u, hu⟩ (by simpa using hu0)).mp (hP.mult_spinWt S σ) ⟨v, hv⟩
  exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩

private theorem stdVec_trichotomy {r : RootSubgroupIndex 3} (hr : IsShortIndex r) (b : Fin 3) :
    stdVec r b = 0 ∨ stdVec r b = 1 ∨ stdVec r b = -1 := by
  cases r with
  | positiveLong i => simp [IsShortIndex] at hr
  | negativeLong i => simp [IsShortIndex] at hr
  | difference i j hij =>
      rw [stdVec_apply_difference hij]
      split_ifs <;> simp
  | positiveSum i j hij =>
      rw [stdVec_apply_positiveSum hij]
      split_ifs <;> simp
  | negativeSum i j hij =>
      rw [stdVec_apply_negativeSum hij]
      split_ifs <;> simp

private theorem stdVec_two_nonzero {r : RootSubgroupIndex 3} (hr : IsShortIndex r) :
    ∃ i j, i ≠ j ∧ stdVec r i ≠ 0 ∧ stdVec r j ≠ 0 := by
  cases r with
  | positiveLong i => simp [IsShortIndex] at hr
  | negativeLong i => simp [IsShortIndex] at hr
  | difference i j hij =>
      exact ⟨i, j, hij, by rw [stdVec_apply_difference hij]; simp,
        by rw [stdVec_apply_difference hij]; simp [Ne.symm hij]⟩
  | positiveSum i j hij =>
      exact ⟨i, j, hij.ne, by rw [stdVec_apply_positiveSum hij]; simp,
        by rw [stdVec_apply_positiveSum hij]; simp [hij.ne']⟩
  | negativeSum i j hij =>
      exact ⟨i, j, hij.ne, by rw [stdVec_apply_negativeSum hij]; simp,
        by rw [stdVec_apply_negativeSum hij]; simp [hij.ne']⟩

private theorem mult_eq_zero_of_coord {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {a : Fin 3 → ZMod (Nat.card Kˣ)} {i : Fin 3} (h1 : a i ≠ x) (h2 : a i ≠ -x) :
    S.mult a = 0 := by
  refine hP.mult_eq_zero S fun σ h => ?_
  have hi := congrFun h i
  cases hσ : σ i
  · simp only [spinWt, hσ, if_false] at hi
    exact h2 hi
  · simp only [spinWt, hσ, if_true] at hi
    exact h1 hi

private theorem spinWt_add_two_mul_rootWt {x : ZMod (Nat.card Kˣ)} {r : RootSubgroupIndex 3}
    (hr : IsShortIndex r) {σ : Fin 3 → Bool} (hsrc : IsSrc (stdVec r) σ) :
    spinWt x σ + (2 * x) • rootWt K r = spinWt x (flipAt (stdVec r) σ) := by
  funext b
  have hsrcb := hsrc b
  simp only [Pi.add_apply, Pi.smul_apply, spinWt, rootWt, castW, smul_eq_mul]
  rcases stdVec_trichotomy hr b with h0 | h1 | hm
  · have hflip : flipAt (stdVec r) σ b = σ b := by rw [flipAt, if_pos h0]
    rw [h0, hflip]
    simp
  · have hσ : σ b = false := hsrcb.1 h1
    have hzero : ¬ stdVec r b = 0 := by rw [h1]; norm_num
    have hflip : flipAt (stdVec r) σ b = true := by rw [flipAt, if_neg hzero, hσ]; rfl
    rw [h1, hflip]
    simp [hσ]
    ring
  · have hσ : σ b = true := hsrcb.2 hm
    have hzero : ¬ stdVec r b = 0 := by rw [hm]; norm_num
    have hflip : flipAt (stdVec r) σ b = false := by rw [flipAt, if_neg hzero, hσ]; rfl
    rw [hm, hflip]
    simp [hσ]
    ring

private theorem mult_add_smul_eq_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {r : RootSubgroupIndex 3} (hr : IsShortIndex r) {k : ℕ}
    (hk0 : (k : ZMod (Nat.card Kˣ)) ≠ 0)
    (hk2 : (k : ZMod (Nat.card Kˣ)) ≠ 2 * x)
    (hkm : (k : ZMod (Nat.card Kˣ)) ≠ -(2 * x)) (σ : Fin 3 → Bool) :
    S.mult (spinWt x σ + (k : ZMod (Nat.card Kˣ)) • rootWt K r) = 0 := by
  obtain ⟨i, -, -, hi, -⟩ := stdVec_two_nonzero hr
  have htri : stdVec r i = 1 ∨ stdVec r i = -1 := (stdVec_trichotomy hr i).resolve_left hi
  have hcoord : (spinWt x σ + (k : ZMod (Nat.card Kˣ)) • rootWt K r) i =
      (if σ i then x else -x) + (k : ZMod (Nat.card Kˣ)) * ((stdVec r i : ℤ) :
        ZMod (Nat.card Kˣ)) := by
    simp [spinWt, rootWt, castW, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hpm : (if σ i then x else -x) = x ∨ (if σ i then x else -x) = -x := by
    cases h : σ i <;> simp
  refine mult_eq_zero_of_coord S hP (i := i) ?_ ?_
  · intro h
    rw [hcoord] at h
    rcases eq_pm_of_pm_add_int odd_natCard_units hP.ne_zero htri hpm (Or.inl h) with h0 | h2 | hm
    · exact hk0 h0
    · exact hk2 h2
    · exact hkm hm
  · intro h
    rw [hcoord] at h
    rcases eq_pm_of_pm_add_int odd_natCard_units hP.ne_zero htri hpm (Or.inr h) with h0 | h2 | hm
    · exact hk0 h0
    · exact hk2 h2
    · exact hkm hm

private theorem mult_add_two_mul_eq_zero_of_not_src {x : ZMod (Nat.card Kˣ)}
    (hP : S.IsSpinPattern x) {r : RootSubgroupIndex 3} (hr : IsShortIndex r)
    {σ : Fin 3 → Bool} (h : ¬ IsSrc (stdVec r) σ) :
    S.mult (spinWt x σ + (2 * x) • rootWt K r) = 0 := by
  have h3 := three_mul_ne_pm odd_natCard_units hP.ne_zero
  have hbad : ∃ i, (stdVec r i = 1 ∧ σ i = true) ∨ (stdVec r i = -1 ∧ σ i = false) := by
    by_contra hc
    refine h fun i => ⟨fun hi => ?_, fun hi => ?_⟩
    · by_contra hσ
      exact hc ⟨i, Or.inl ⟨hi, by simpa using hσ⟩⟩
    · by_contra hσ
      exact hc ⟨i, Or.inr ⟨hi, by simpa using hσ⟩⟩
  obtain ⟨i, h1 | hm⟩ := hbad
  · have hcoord : (spinWt x σ + (2 * x) • rootWt K r) i = (3 : ZMod (Nat.card Kˣ)) * x := by
      simp [spinWt, rootWt, castW, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1.1, h1.2]
      ring
    refine mult_eq_zero_of_coord S hP (i := i) ?_ ?_
    · rw [hcoord]; exact h3.1
    · rw [hcoord]; exact h3.2.1
  · have hcoord : (spinWt x σ + (2 * x) • rootWt K r) i = -((3 : ZMod (Nat.card Kˣ)) * x) := by
      simp [spinWt, rootWt, castW, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm.1, hm.2]
      ring
    refine mult_eq_zero_of_coord S hP (i := i) ?_ ?_
    · rw [hcoord]; exact h3.2.2.1
    · rw [hcoord]; exact h3.2.2.2

private theorem mult_add_neg_two_mul_eq_zero_of_not_src {x : ZMod (Nat.card Kˣ)}
    (hP : S.IsSpinPattern x) {r : RootSubgroupIndex 3} (hr : IsShortIndex r)
    {σ : Fin 3 → Bool} (h : ¬ IsSrc (stdVec r) (fun i => !σ i)) :
    S.mult (spinWt x σ + (-(2 * x)) • rootWt K r) = 0 := by
  have h3 := three_mul_ne_pm odd_natCard_units hP.ne_zero
  have hbad : ∃ i, (stdVec r i = 1 ∧ σ i = false) ∨ (stdVec r i = -1 ∧ σ i = true) := by
    by_contra hc
    refine h fun i => ⟨fun hi => ?_, fun hi => ?_⟩
    · by_contra hσ
      exact hc ⟨i, Or.inl ⟨hi, by simpa using hσ⟩⟩
    · by_contra hσ
      exact hc ⟨i, Or.inr ⟨hi, by simpa using hσ⟩⟩
  obtain ⟨i, h1 | hm⟩ := hbad
  · have hcoord : (spinWt x σ + (-(2 * x)) • rootWt K r) i =
        -((3 : ZMod (Nat.card Kˣ)) * x) := by
      simp [spinWt, rootWt, castW, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1.1, h1.2]
      ring
    refine mult_eq_zero_of_coord S hP (i := i) ?_ ?_
    · rw [hcoord]; exact h3.2.2.1
    · rw [hcoord]; exact h3.2.2.2
  · have hcoord : (spinWt x σ + (-(2 * x)) • rootWt K r) i = (3 : ZMod (Nat.card Kˣ)) * x := by
      simp [spinWt, rootWt, castW, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm.1, hm.2]
      ring
    refine mult_eq_zero_of_coord S hP (i := i) ?_ ?_
    · rw [hcoord]; exact h3.1
    · rw [hcoord]; exact h3.2.1

private theorem exists_spinWt_of_mult_ne_zero {x : ZMod (Nat.card Kˣ)}
    (hP : S.IsSpinPattern x) {a : Fin 3 → ZMod (Nat.card Kˣ)} (ha : S.mult a ≠ 0) :
    ∃ σ, a = spinWt x σ := by
  by_contra h
  simp only [not_exists] at h
  exact ha (hP.mult_eq_zero S h)

private theorem short_A_eq_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {r : RootSubgroupIndex 3} (hr : IsShortIndex r) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k < Nat.card Kˣ) (hk2 : (k : ZMod (Nat.card Kˣ)) ≠ 2 * x)
    (hkm : (k : ZMod (Nat.card Kˣ)) ≠ -(2 * x)) : S.A r k = 0 := by
  have hk0 : (k : ZMod (Nat.card Kˣ)) ≠ 0 := natCast_ne_zero hk1 hkN
  refine S.A_eq_zero r k fun a ha => ?_
  obtain ⟨σ, rfl⟩ := exists_spinWt_of_mult_ne_zero S hP ha
  exact mult_add_smul_eq_zero S hP hr hk0 hk2 hkm σ

private theorem not_src_neg {r : RootSubgroupIndex 3} (hr : IsShortIndex r)
    {σ : Fin 3 → Bool} (h : IsSrc (stdVec r) σ) :
    ¬ IsSrc (stdVec r) (fun i => !σ i) := by
  intro hcon
  obtain ⟨i, -, -, hi, -⟩ := stdVec_two_nonzero hr
  rcases (stdVec_trichotomy hr i).resolve_left hi with h1 | h1
  · have hf : σ i = false := (h i).1 h1
    have ht : (fun j => !σ j) i = false := (hcon i).1 h1
    simp [hf] at ht
  · have ht : σ i = true := (h i).2 h1
    have hf : (fun j => !σ j) i = true := (hcon i).2 h1
    simp [ht] at hf

private theorem short_A_card_eq_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {r : RootSubgroupIndex 3} (hr : IsShortIndex r) : S.A r (Nat.card Kˣ) = 0 := by
  haveI : NeZero (Nat.card Kˣ) := ⟨Nat.card_pos.ne'⟩
  have hx' : (2 : ZMod (Nat.card Kˣ)) * x ≠ 0 := two_mul_ne_zero odd_natCard_units hP.ne_zero
  haveI : NeZero ((2 : ZMod (Nat.card Kˣ)) * x) := ⟨hx'⟩
  have hkp : (((2 * x).val : ℕ) : ZMod (Nat.card Kˣ)) = 2 * x := ZMod.natCast_zmod_val _
  have hkm : (((-(2 * x)).val : ℕ) : ZMod (Nat.card Kˣ)) = -(2 * x) :=
    ZMod.natCast_zmod_val _
  have hval : (2 * x).val < Nat.card Kˣ := ZMod.val_lt _
  have hsum : (2 * x).val + (-(2 * x)).val = Nat.card Kˣ := by
    rw [ZMod.val_neg_of_ne_zero]
    exact Nat.add_sub_cancel' (Nat.le_of_lt hval)
  have hle : (-(2 * x)).val ≤ Nat.card Kˣ := by
    rw [ZMod.val_neg_of_ne_zero]
    exact Nat.sub_le _ _
  have hsub : Nat.card Kˣ - (2 * x).val = (-(2 * x)).val :=
    Nat.sub_eq_of_eq_add (by omega : Nat.card Kˣ = (-(2 * x)).val + (2 * x).val)
  have hsub' : Nat.card Kˣ - (-(2 * x)).val = (2 * x).val :=
    Nat.sub_eq_of_eq_add (by omega : Nat.card Kˣ = (2 * x).val + (-(2 * x)).val)
  have hfac : S.A r ((2 * x).val) * S.A r ((-(2 * x)).val) = S.A r (Nat.card Kˣ) := by
    rw [← S.A_mul_card_sub r (i := (2 * x).val) hval.le, hsub]
  have hfac' : S.A r ((-(2 * x)).val) * S.A r ((2 * x).val) = S.A r (Nat.card Kˣ) := by
    rw [← S.A_mul_card_sub r (i := (-(2 * x)).val) hle, hsub']
  refine ext_of_wtSpace (diagHom 3 K) S.ρ (f := S.A r (Nat.card Kˣ)) (g := 0) fun a v hv => ?_
  change v ∈ S.X a at hv
  by_cases hm : S.mult a = 0
  · have hv0 : v = 0 := by rw [S.X_eq_bot_iff.mpr hm] at hv; simpa using hv
    rw [hv0]
    simp
  · obtain ⟨σ, rfl⟩ := exists_spinWt_of_mult_ne_zero S hP hm
    by_cases hsrc : IsSrc (stdVec r) σ
    · have hnot : ¬ IsSrc (stdVec r) (fun i => !σ i) := not_src_neg hr hsrc
      have hkill := mult_add_neg_two_mul_eq_zero_of_not_src S hP hr hnot
      have hmem : S.A r ((-(2 * x)).val) v ∈
          S.X (spinWt x σ + (((-(2 * x)).val : ℕ) : ZMod (Nat.card Kˣ)) • rootWt K r) :=
        S.A_mem r hv ((-(2 * x)).val)
      rw [hkm, S.X_eq_bot_iff.mpr hkill] at hmem
      have hkmv : S.A r ((-(2 * x)).val) v = 0 := by simpa using hmem
      rw [← hfac, Module.End.mul_apply, hkmv, map_zero]
      exact (LinearMap.zero_apply v).symm
    · have hkill := mult_add_two_mul_eq_zero_of_not_src S hP hr hsrc
      have hmem : S.A r ((2 * x).val) v ∈
          S.X (spinWt x σ + (((2 * x).val : ℕ) : ZMod (Nat.card Kˣ)) • rootWt K r) :=
        S.A_mem r hv ((2 * x).val)
      rw [hkp, S.X_eq_bot_iff.mpr hkill] at hmem
      have hkpv : S.A r ((2 * x).val) v = 0 := by simpa using hmem
      rw [← hfac', Module.End.mul_apply, hkpv, map_zero]
      exact (LinearMap.zero_apply v).symm

private theorem short_A_neg_kill_target {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {r : RootSubgroupIndex 3} (hr : IsShortIndex r) {kp km : ℕ}
    (hkp : (kp : ZMod (Nat.card Kˣ)) = 2 * x)
    (hkm : (km : ZMod (Nat.card Kˣ)) = -(2 * x))
    (hfac : S.A r km * S.A r kp = S.A r (Nat.card Kˣ))
    (hAN : S.A r (Nat.card Kˣ) = 0)
    {σ : Fin 3 → Bool} (hsrc : IsSrc (stdVec r) σ) {u₀ : V}
    (hu₀ : u₀ ∈ S.X (spinWt x σ)) (hu₀' : S.A r kp u₀ ≠ 0) :
    ∀ u ∈ S.X (spinWt x (flipAt (stdVec r) σ)), S.A r km u = 0 := by
  intro u hu
  have htgt : S.A r kp u₀ ∈ S.X (spinWt x (flipAt (stdVec r) σ)) := by
    have h := S.A_mem r hu₀ kp
    rw [hkp, spinWt_add_two_mul_rootWt hr hsrc] at h
    exact h
  by_cases hu0 : u = 0
  · rw [hu0]
    simp
  · obtain ⟨c, hc⟩ := hP.eq_smul S htgt hu₀' hu
    rw [hc, map_smul, ← Module.End.mul_apply, hfac, hAN]
    simp

private theorem short_A_neg_kill_other {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {r : RootSubgroupIndex 3} (hr : IsShortIndex r) {km : ℕ}
    (hkm : (km : ZMod (Nat.card Kˣ)) = -(2 * x)) {σ : Fin 3 → Bool}
    (h : ¬ IsSrc (stdVec r) (fun i => !σ i)) {u : V} (hu : u ∈ S.X (spinWt x σ)) :
    S.A r km u = 0 := by
  have hkill := mult_add_neg_two_mul_eq_zero_of_not_src S hP hr h
  have hmem := S.A_mem r hu km
  rw [hkm, S.X_eq_bot_iff.mpr hkill] at hmem
  simpa using hmem

private theorem eq_of_not_eq_not {σ τ : Fin 3 → Bool} (h : (fun i => !σ i) = τ) :
    σ = fun i => !τ i := by
  funext i
  have hi := congrFun h i
  cases hσ : σ i <;> cases hτ : τ i
  · simp [hσ, hτ] at hi
  · rfl
  · rfl
  · simp [hσ, hτ] at hi

private theorem short_dichotomy_witness {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {r : RootSubgroupIndex 3} (hr : IsShortIndex r) (hE : S.A r (2 * x).val ≠ 0) :
    ∃ σ₀ σ₂ : Fin 3 → Bool,
      IsSrc (stdVec r) σ₀ ∧ σ₂ = (fun i => !flipAt (stdVec r) σ₀ i) ∧
      (∀ u ∈ S.X (spinWt x (flipAt (stdVec r) σ₀)), S.A r (-(2 * x)).val u = 0) ∧
      (∀ u ∈ S.X (spinWt x (fun i => !σ₀ i)), S.A r (-(2 * x)).val u = 0) := by
  haveI : NeZero (Nat.card Kˣ) := ⟨Nat.card_pos.ne'⟩
  have hx' : (2 : ZMod (Nat.card Kˣ)) * x ≠ 0 := two_mul_ne_zero odd_natCard_units hP.ne_zero
  haveI : NeZero ((2 : ZMod (Nat.card Kˣ)) * x) := ⟨hx'⟩
  have hkp : (((2 * x).val : ℕ) : ZMod (Nat.card Kˣ)) = 2 * x := ZMod.natCast_zmod_val _
  have hkm : (((-(2 * x)).val : ℕ) : ZMod (Nat.card Kˣ)) = -(2 * x) :=
    ZMod.natCast_zmod_val _
  have hval : (2 * x).val < Nat.card Kˣ := ZMod.val_lt _
  have hsum : (2 * x).val + (-(2 * x)).val = Nat.card Kˣ := by
    rw [ZMod.val_neg_of_ne_zero]
    exact Nat.add_sub_cancel' (Nat.le_of_lt hval)
  have hle : (-(2 * x)).val ≤ Nat.card Kˣ := by
    rw [ZMod.val_neg_of_ne_zero]
    exact Nat.sub_le _ _
  have hsub' : Nat.card Kˣ - (-(2 * x)).val = (2 * x).val :=
    Nat.sub_eq_of_eq_add (by omega : Nat.card Kˣ = (2 * x).val + (-(2 * x)).val)
  have hfac : S.A r ((-(2 * x)).val) * S.A r ((2 * x).val) = S.A r (Nat.card Kˣ) := by
    rw [← S.A_mul_card_sub r (i := (-(2 * x)).val) hle, hsub']
  have hAN : S.A r (Nat.card Kˣ) = 0 := short_A_card_eq_zero S hP hr
  obtain ⟨σ₀, v, hv, hvE⟩ : ∃ σ v, v ∈ S.X (spinWt x σ) ∧ S.A r ((2 * x).val) v ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hE (by
      refine ext_of_wtSpace (diagHom 3 K) S.ρ (f := S.A r ((2 * x).val)) (g := 0)
        fun a u hu => ?_
      change u ∈ S.X a at hu
      by_cases hm : S.mult a = 0
      · have hu0 : u = 0 := by rw [S.X_eq_bot_iff.mpr hm] at hu; simpa using hu
        rw [hu0]
        simp
      · obtain ⟨σ, rfl⟩ := exists_spinWt_of_mult_ne_zero S hP hm
        exact h σ u hu)
  have hsrc₀ : IsSrc (stdVec r) σ₀ := by
    by_contra hcon
    apply hvE
    have hkill := mult_add_two_mul_eq_zero_of_not_src S hP hr hcon
    have hmem := S.A_mem r hv ((2 * x).val)
    rw [hkp, S.X_eq_bot_iff.mpr hkill] at hmem
    simpa using hmem
  set σ₂ : Fin 3 → Bool := fun i => !flipAt (stdVec r) σ₀ i with hσ₂
  have hsrc₂ : IsSrc (stdVec r) σ₂ := by
    rw [hσ₂]
    exact (isSrc_not_flipAt_iff (stdVec r) σ₀).mpr hsrc₀
  have htgt : S.A r ((2 * x).val) v ∈ S.X (spinWt x (flipAt (stdVec r) σ₀)) := by
    have h := S.A_mem r hv ((2 * x).val)
    rw [hkp, spinWt_add_two_mul_rootWt hr hsrc₀] at h
    exact h
  obtain ⟨w, hw, hpol⟩ := S.exists_polar_eq_one htgt hvE
  have hw₂ : w ∈ S.X (spinWt x σ₂) := by
    rw [hσ₂, ← neg_spinWt]
    exact hw
  have hwE : S.A r ((2 * x).val) w ≠ 0 := by
    intro h0
    have h1 : polar S.Q v (S.A r ((2 * x).val) w) = 1 := by
      rw [← S.polar_A r v w ((2 * x).val)]
      exact hpol
    rw [h0] at h1
    simp at h1
  have hkill₀ := short_A_neg_kill_target S hP hr (kp := (2 * x).val) (km := (-(2 * x)).val)
    hkp hkm hfac hAN hsrc₀ hv hvE
  have hflip₂ : flipAt (stdVec r) σ₂ = fun i => !σ₀ i := by
    rw [hσ₂, flipAt_not, flipAt_flipAt]
  have hkill₂ : ∀ u ∈ S.X (spinWt x (fun i => !σ₀ i)), S.A r ((-(2 * x)).val) u = 0 :=
    hflip₂ ▸ short_A_neg_kill_target S hP hr (kp := (2 * x).val) (km := (-(2 * x)).val)
      hkp hkm hfac hAN hsrc₂ hw₂ hwE
  exact ⟨σ₀, σ₂, hsrc₀, hσ₂, hkill₀, hkill₂⟩

private theorem short_dichotomy {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {r : RootSubgroupIndex 3} (hr : IsShortIndex r)
    (hE : S.A r (2 * x).val ≠ 0) : S.A r (-(2 * x)).val = 0 := by
  obtain ⟨σ₀, σ₂, hsrc₀, hσ₂, hkill₀, hkill₂⟩ := short_dichotomy_witness S hP hr hE
  haveI : NeZero (Nat.card Kˣ) := ⟨Nat.card_pos.ne'⟩
  have hkm : (((-(2 * x)).val : ℕ) : ZMod (Nat.card Kˣ)) = -(2 * x) :=
    ZMod.natCast_zmod_val _
  refine ext_of_wtSpace (diagHom 3 K) S.ρ (f := S.A r ((-(2 * x)).val)) (g := 0)
    fun a u hu => ?_
  change u ∈ S.X a at hu
  by_cases hm : S.mult a = 0
  · have hu0 : u = 0 := by rw [S.X_eq_bot_iff.mpr hm] at hu; simpa using hu
    rw [hu0]
    simp
  · obtain ⟨σ, rfl⟩ := exists_spinWt_of_mult_ne_zero S hP hm
    by_cases hcon : IsSrc (stdVec r) (fun i => !σ i)
    · rcases (IsSrc.eq_or_eq hr hsrc₀ hcon) with h | h
      · have hσ : σ = fun i => !σ₀ i := eq_of_not_eq_not h
        rw [hσ] at hu
        exact hkill₂ u hu
      · have h1 := eq_of_not_eq_not h
        have hσ : σ = flipAt (stdVec r) σ₀ := by
          rw [h1]
          funext i
          simp
        rw [hσ] at hu
        exact hkill₀ u hu
    · exact short_A_neg_kill_other S hP hr (km := (-(2 * x)).val) hkm hcon hu

private theorem psi_apply_of_vanishing
    {r : RootSubgroupIndex 3} {kp : ℕ} {y : ZMod (Nat.card Kˣ)}
    (hkp : (kp : ZMod (Nat.card Kˣ)) = y) (hkp1 : 1 ≤ kp)
    (hkpN : kp < Nat.card Kˣ)
    (hvan : ∀ k : ℕ, 1 ≤ k → k ≤ Nat.card Kˣ → (k : ZMod (Nat.card Kˣ)) ≠ y →
      S.A r k = 0) (c : K) (v : V) :
    S.ψ (elt r c) v = v + c ^ kp • S.A r kp v := by
  rw [ψ_elt_apply]
  have hy0 : y ≠ 0 := by
    rw [← hkp]
    exact natCast_ne_zero hkp1 hkpN
  have hsupp : ∀ k ∈ Finset.range (Nat.card Kˣ + 1), k ∉ ({0, kp} : Finset ℕ) →
      c ^ k • S.A r k v = 0 := by
    intro k hk hknot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hknot
    obtain ⟨hk0, hkkp⟩ := hknot
    have hkN : k < Nat.card Kˣ + 1 := Finset.mem_range.mp hk
    by_cases hk1 : 1 ≤ k
    · have hky : (k : ZMod (Nat.card Kˣ)) ≠ y := by
        intro hh
        by_cases hlt : k < Nat.card Kˣ
        · apply hkkp
          rw [← ZMod.val_natCast_of_lt hlt, hh, ← hkp, ZMod.val_natCast_of_lt hkpN]
        · have hkeq : k = Nat.card Kˣ := by omega
          rw [hkeq, ZMod.natCast_self] at hh
          exact hy0 hh.symm
      rw [hvan k hk1 (by omega) hky]
      simp
    · exact absurd (by omega : k = 0) hk0
  have hmem : ({0, kp} : Finset ℕ) ⊆ Finset.range (Nat.card Kˣ + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · simp
    · rw [Finset.mem_range]
      omega
  rw [← Finset.sum_subset hmem hsupp]
  rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton,
    A_zero]
  simp

private theorem short_vanishing {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    (hE : S.A (.difference 0 1 (by decide)) (2 * x).val ≠ 0)
    (hkm : S.A (.difference 0 1 (by decide)) (-(2 * x)).val = 0) :
    ∀ r, IsShortIndex r → ∀ k, 1 ≤ k → k ≤ Nat.card Kˣ →
      (k : ZMod (Nat.card Kˣ)) ≠ 2 * x → S.A r k = 0 := by
  intro r hr k hk1 hkN hk2
  obtain ⟨g, hg⟩ := exists_conj_eq_elt (K := K) r hr
  rw [S.A_eq_zero_iff_of_conj hg k]
  by_cases hlt : k < Nat.card Kˣ
  · by_cases hkmk : (k : ZMod (Nat.card Kˣ)) = -(2 * x)
    · have hkeq : k = (-(2 * x)).val := by
        rw [← ZMod.val_natCast_of_lt hlt, hkmk]
      rw [hkeq]
      exact hkm
    · exact short_A_eq_zero S hP (by simp [IsShortIndex]) hk1 hlt hk2 hkmk
  · have hkeq : k = Nat.card Kˣ := by omega
    rw [hkeq]
    exact short_A_card_eq_zero S hP (by simp [IsShortIndex])

private theorem short_kp_pow_two {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    (hE : S.A (.difference 0 1 (by decide)) (2 * x).val ≠ 0)
    (hvan : ∀ r, IsShortIndex r → ∀ k, 1 ≤ k → k ≤ Nat.card Kˣ →
      (k : ZMod (Nat.card Kˣ)) ≠ 2 * x → S.A r k = 0) :
    ∃ l, 2 ^ l = (2 * x).val := by
  by_contra h
  simp only [not_exists] at h
  have hx' : (2 : ZMod (Nat.card Kˣ)) * x ≠ 0 := two_mul_ne_zero odd_natCard_units hP.ne_zero
  have hkp1 : 1 ≤ (2 * x).val := ZMod.val_pos.mpr hx'
  have hkpN : (2 * x).val < Nat.card Kˣ := ZMod.val_lt _
  obtain ⟨i, j, hi0, hj0, hij, hsum, hfac⟩ :=
    S.exists_A_eq_mul (.difference 0 1 (by decide)) hkp1 (by omega) fun l hh => h l hh.symm
  have hiN : i < Nat.card Kˣ := by omega
  have hikp : i ≠ (2 * x).val := by omega
  have hi2 : (i : ZMod (Nat.card Kˣ)) ≠ 2 * x := by
    intro hh
    apply hikp
    rw [← ZMod.val_natCast_of_lt hiN, hh]
  have hiA : S.A (.difference 0 1 (by decide)) i = 0 :=
    hvan _ (by simp [IsShortIndex]) i (by omega) (by omega) hi2
  exact hE (by rw [hfac, hiA, zero_mul])

private theorem short_not_both_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x) :
    S.A (.difference 0 1 (by decide)) (2 * x).val ≠ 0 ∨
      S.A (.difference 0 1 (by decide)) (-(2 * x)).val ≠ 0 := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hpos, hneg⟩ := h
  have hpos' : S.A (.difference 0 1 (by decide)) (2 * x).val = 0 := not_not.mp hpos
  have hneg' : S.A (.difference 0 1 (by decide)) (-(2 * x)).val = 0 := not_not.mp hneg
  have hx' : (2 : ZMod (Nat.card Kˣ)) * x ≠ 0 := two_mul_ne_zero odd_natCard_units hP.ne_zero
  have hr₀ : IsShortIndex (.difference 0 1 (by decide) : RootSubgroupIndex 3) := by
    simp [IsShortIndex]
  have hvan : ∀ k, 1 ≤ k → k < Nat.card Kˣ → k ≠ (2 * x).val →
      k ≠ (-(2 * x)).val → S.A (.difference 0 1 (by decide)) k = 0 := by
    intro k hk1 hkN hkkp hkkm
    refine short_A_eq_zero S hP hr₀ hk1 hkN ?_ ?_
    · intro hh
      apply hkkp
      rw [← ZMod.val_natCast_of_lt hkN, hh]
    · intro hh
      apply hkkm
      rw [← ZMod.val_natCast_of_lt hkN, hh]
  have hcard : S.A (.difference 0 1 (by decide)) (Nat.card Kˣ) = 0 :=
    short_A_card_eq_zero S hP hr₀
  have hvan' : ∀ k, 1 ≤ k → k ≤ Nat.card Kˣ → k ≠ (2 * x).val →
      S.A (.difference 0 1 (by decide)) k = 0 := by
    intro k hk1 hkN hkkp
    by_cases hlt : k < Nat.card Kˣ
    · by_cases hkmk : k = (-(2 * x)).val
      · rw [hkmk]
        exact hneg'
      · exact hvan k hk1 hlt hkkp hkmk
    · have hkeq : k = Nat.card Kˣ := by omega
      rw [hkeq]
      exact hcard
  have hψ : ∀ c : K, S.ψ (elt (.difference 0 1 (by decide)) c) = 1 := by
    intro c
    ext v
    rw [psi_apply_of_vanishing S (r := .difference 0 1 (by decide))
      (kp := (2 * x).val) (y := 2 * x) (ZMod.natCast_zmod_val _)
      (ZMod.val_pos.mpr hx') (ZMod.val_lt _)
      (fun k hk1 hkN hkz => hvan' k hk1 hkN (fun hkv => hkz (by
        rw [hkv, ZMod.natCast_zmod_val]))) c v, hpos']
    simp
  have h1 : elt (.difference 0 1 (by decide) : RootSubgroupIndex 3) (1 : K) = 1 :=
    S.ψ_injective (by rw [hψ 1, map_one])
  have h10 : elt (.difference 0 1 (by decide) : RootSubgroupIndex 3) (1 : K) =
      elt (.difference 0 1 (by decide) : RootSubgroupIndex 3) 0 := by
    rw [h1, elt_zero]
  exact one_ne_zero (elt_injective (F := K) (.difference 0 1 (by decide)) h10)

private theorem long_coord_ne {N : ℕ} (hN : Odd N) {x k : ZMod N} (hx : x ≠ 0)
    (hk0 : k ≠ 0) (hkx : k ≠ x) (hkn : k ≠ -x) (s : Bool) :
    (if s then x else -x) + k * 2 ≠ x ∧ (if s then x else -x) + k * 2 ≠ -x := by
  cases s
  · simp only [Bool.false_eq_true, if_false]
    constructor
    · intro h
      refine hkx (two_mul_cancel hN ?_)
      linear_combination h
    · intro h
      refine hk0 (two_mul_eq_zero hN ?_)
      linear_combination h
  · simp only [if_true]
    constructor
    · intro h
      refine hk0 (two_mul_eq_zero hN ?_)
      linear_combination h
    · intro h
      have h' : (2 : ZMod N) * (k + x) = 0 := by linear_combination h
      have hk : k + x = 0 := two_mul_eq_zero hN h'
      exact hkn (by linear_combination hk)

private theorem spinWt_add_x_rootWt {x : ZMod (Nat.card Kˣ)} (σ : Fin 3 → Bool)
    (hσ2 : σ 2 = false) :
    spinWt x σ + x • rootWt K (.positiveLong 2) = spinWt x (Function.update σ 2 true) := by
  funext b
  by_cases hb : b = 2
  · subst hb
    simp [spinWt, rootWt_positiveLong, Pi.smul_apply, smul_eq_mul, hσ2]
    ring
  · simp [spinWt, rootWt_positiveLong, Pi.single_eq_of_ne hb, hb]

private theorem spinWt_add_neg_x_rootWt {x : ZMod (Nat.card Kˣ)} (σ : Fin 3 → Bool)
    (hσ2 : σ 2 = true) :
    spinWt x σ + (-x) • rootWt K (.positiveLong 2) = spinWt x (Function.update σ 2 false) := by
  funext b
  by_cases hb : b = 2
  · subst hb
    simp [spinWt, rootWt_positiveLong, Pi.smul_apply, smul_eq_mul, hσ2]
    ring
  · simp [spinWt, rootWt_positiveLong, Pi.single_eq_of_ne hb, hb]

private theorem long_mult_eq_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < Nat.card Kˣ)
    (hkx : (k : ZMod (Nat.card Kˣ)) ≠ x) (hkn : (k : ZMod (Nat.card Kˣ)) ≠ -x)
    (σ : Fin 3 → Bool) :
    S.mult (spinWt x σ + (k : ZMod (Nat.card Kˣ)) • rootWt K (.positiveLong 2)) = 0 := by
  have hk0 : (k : ZMod (Nat.card Kˣ)) ≠ 0 := natCast_ne_zero hk1 hkN
  have hcoord : (spinWt x σ + (k : ZMod (Nat.card Kˣ)) • rootWt K (.positiveLong 2)) 2 =
      (if σ 2 then x else -x) + (k : ZMod (Nat.card Kˣ)) * 2 := by
    simp [spinWt, rootWt_positiveLong, Pi.smul_apply, smul_eq_mul]
  have hne := long_coord_ne odd_natCard_units hP.ne_zero hk0 hkx hkn (σ 2)
  refine mult_eq_zero_of_coord S hP (i := 2) ?_ ?_
  · rw [hcoord]
    exact hne.1
  · rw [hcoord]
    exact hne.2

private theorem long_A_x_apply_eq_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {σ : Fin 3 → Bool} (hσ2 : σ 2 = true) {v : V} (hv : v ∈ S.X (spinWt x σ)) :
    S.A (.positiveLong 2) x.val v = 0 := by
  have hxval : ((x.val : ℕ) : ZMod (Nat.card Kˣ)) = x := ZMod.natCast_zmod_val x
  have h3 := three_mul_ne_pm odd_natCard_units hP.ne_zero
  have hkill : S.mult (spinWt x σ + ((x.val : ℕ) : ZMod (Nat.card Kˣ)) •
      rootWt K (.positiveLong 2)) = 0 := by
    rw [hxval]
    have hcoord : (spinWt x σ + x • rootWt K (.positiveLong 2)) 2 =
        (3 : ZMod (Nat.card Kˣ)) * x := by
      simp [spinWt, rootWt_positiveLong, Pi.smul_apply, smul_eq_mul, hσ2]
      ring
    refine mult_eq_zero_of_coord S hP (i := 2) ?_ ?_
    · rw [hcoord]
      exact h3.1
    · rw [hcoord]
      exact h3.2.1
  have hmem := S.A_mem (.positiveLong 2) hv x.val
  rw [S.X_eq_bot_iff.mpr hkill] at hmem
  simpa using hmem

private theorem long_A_neg_x_apply_eq_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {σ : Fin 3 → Bool} (hσ2 : σ 2 = false) {v : V} (hv : v ∈ S.X (spinWt x σ)) :
    S.A (.positiveLong 2) (-x).val v = 0 := by
  have hxval : (((-x).val : ℕ) : ZMod (Nat.card Kˣ)) = -x := ZMod.natCast_zmod_val (-x)
  have h3 := three_mul_ne_pm odd_natCard_units hP.ne_zero
  have hkill : S.mult (spinWt x σ + (((-x).val : ℕ) : ZMod (Nat.card Kˣ)) •
      rootWt K (.positiveLong 2)) = 0 := by
    rw [hxval]
    have hcoord : (spinWt x σ + (-x) • rootWt K (.positiveLong 2)) 2 =
        -((3 : ZMod (Nat.card Kˣ)) * x) := by
      simp [spinWt, rootWt_positiveLong, Pi.smul_apply, smul_eq_mul, hσ2]
      ring
    refine mult_eq_zero_of_coord S hP (i := 2) ?_ ?_
    · rw [hcoord]
      exact h3.2.2.1
    · rw [hcoord]
      exact h3.2.2.2
  have hmem := S.A_mem (.positiveLong 2) hv (-x).val
  rw [S.X_eq_bot_iff.mpr hkill] at hmem
  simpa using hmem

private theorem long_A_x_mem {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {σ : Fin 3 → Bool} (hσ2 : σ 2 = false) {v : V} (hv : v ∈ S.X (spinWt x σ)) :
    S.A (.positiveLong 2) x.val v ∈ S.X (spinWt x (Function.update σ 2 true)) := by
  have hxval : ((x.val : ℕ) : ZMod (Nat.card Kˣ)) = x := ZMod.natCast_zmod_val x
  have h := S.A_mem (.positiveLong 2) hv x.val
  rwa [hxval, spinWt_add_x_rootWt σ hσ2] at h

private theorem long_A_neg_x_mem {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {σ : Fin 3 → Bool} (hσ2 : σ 2 = true) {v : V} (hv : v ∈ S.X (spinWt x σ)) :
    S.A (.positiveLong 2) (-x).val v ∈ S.X (spinWt x (Function.update σ 2 false)) := by
  have hxval : (((-x).val : ℕ) : ZMod (Nat.card Kˣ)) = -x := ZMod.natCast_zmod_val (-x)
  have h := S.A_mem (.positiveLong 2) hv (-x).val
  rwa [hxval, spinWt_add_neg_x_rootWt σ hσ2] at h

private theorem long_A_card_eq_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x) :
    S.A (.positiveLong 2) (Nat.card Kˣ) = 0 := by
  haveI : NeZero (Nat.card Kˣ) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero x := ⟨hP.ne_zero⟩
  have hval : x.val < Nat.card Kˣ := ZMod.val_lt _
  have hval' : (-x).val < Nat.card Kˣ := ZMod.val_lt _
  have hsum : x.val + (-x).val = Nat.card Kˣ := by
    rw [show (-x).val = Nat.card Kˣ - x.val from ZMod.val_neg_of_ne_zero x]
    exact Nat.add_sub_cancel' hval.le
  have hsub : Nat.card Kˣ - x.val = (-x).val :=
    Nat.sub_eq_of_eq_add (by omega : Nat.card Kˣ = (-x).val + x.val)
  have hsub' : Nat.card Kˣ - (-x).val = x.val :=
    Nat.sub_eq_of_eq_add (by omega : Nat.card Kˣ = x.val + (-x).val)
  have hfac : S.A (.positiveLong 2) x.val * S.A (.positiveLong 2) ((-x).val) =
      S.A (.positiveLong 2) (Nat.card Kˣ) := by
    rw [← S.A_mul_card_sub (.positiveLong 2) (i := x.val) hval.le, hsub]
  have hfac' : S.A (.positiveLong 2) ((-x).val) * S.A (.positiveLong 2) x.val =
      S.A (.positiveLong 2) (Nat.card Kˣ) := by
    rw [← S.A_mul_card_sub (.positiveLong 2) (i := (-x).val) hval'.le, hsub']
  refine ext_of_wtSpace (diagHom 3 K) S.ρ
    (f := S.A (.positiveLong 2) (Nat.card Kˣ)) (g := 0) fun a v hv => ?_
  change v ∈ S.X a at hv
  by_cases hm : S.mult a = 0
  · have hv0 : v = 0 := by rw [S.X_eq_bot_iff.mpr hm] at hv; simpa using hv
    rw [hv0]
    simp
  · obtain ⟨σ, rfl⟩ := exists_spinWt_of_mult_ne_zero S hP hm
    cases h2 : σ 2
    · have h0 := long_A_neg_x_apply_eq_zero S hP h2 hv
      rw [← hfac, Module.End.mul_apply, h0]
      simp
    · have h0 := long_A_x_apply_eq_zero S hP h2 hv
      rw [← hfac', Module.End.mul_apply, h0]
      simp

private theorem long_A_eq_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < Nat.card Kˣ)
    (hkx : (k : ZMod (Nat.card Kˣ)) ≠ x) (hkn : (k : ZMod (Nat.card Kˣ)) ≠ -x) :
    S.A (.positiveLong 2) k = 0 := by
  refine S.A_eq_zero (.positiveLong 2) k fun a ha => ?_
  obtain ⟨σ, rfl⟩ := exists_spinWt_of_mult_ne_zero S hP ha
  exact long_mult_eq_zero S hP hk1 hkN hkx hkn σ

private theorem long_A_commute_lw {k : Fin 3} (hk : k ≠ 2) (m : ℕ) :
    S.A (.positiveLong 2) m * S.ρ (lw k) = S.ρ (lw k) * S.A (.positiveLong 2) m := by
  have hT : ∀ c : K, Commute (S.ρ (elt (.positiveLong 2) c)) (S.ρ (lw k)) :=
    fun c => ((commute_lw_elt_positiveLong_two hk c).map S.ρ).symm
  have h := commute_rootOp (ρ := S.ρ) (x := elt (F := K) (.positiveLong 2)) hT m
  rw [commute_iff_eq] at h
  simpa only [A] using h

private theorem update_spinWt {N : ℕ} (x : ZMod N) (σ : Fin 3 → Bool) (k : Fin 3) :
    Function.update (spinWt x σ) k (-(spinWt x σ k)) =
      spinWt x (Function.update σ k (!(σ k))) := by
  funext i
  by_cases hik : i = k
  · subst hik
    simp only [Function.update_self, spinWt]
    cases h : σ i <;> simp [h]
  · simp only [spinWt, Function.update_of_ne hik]

private theorem long_shift_ne_zero {m : ℕ} {k : Fin 3} (hk : k ≠ 2) {x : ZMod (Nat.card Kˣ)}
    {σ : Fin 3 → Bool} {v : V} (hv : v ∈ S.X (spinWt x σ)) (hv0 : v ≠ 0)
    (hE : S.A (.positiveLong 2) m v ≠ 0) :
    S.A (.positiveLong 2) m (S.ψ (lw k) v) ≠ 0 := by
  have hcomm := long_A_commute_lw S hk m
  have h1 : S.A (.positiveLong 2) m (S.ψ (lw k) v) =
      S.ψ (lw k) (S.A (.positiveLong 2) m v) := by
    rw [← S.ρ_apply (lw k) v, ← Module.End.mul_apply, hcomm, Module.End.mul_apply,
      S.ρ_apply]
  rw [h1]
  intro h0
  apply hE
  have := congrArg (fun w => (S.ψ (lw k))⁻¹ w) h0
  simpa using this

private theorem bool_vec_cases {σ σ' : Fin 3 → Bool} (h2 : σ' 2 = σ 2) :
    σ' = σ ∨ σ' = Function.update σ 0 (!(σ 0)) ∨ σ' = Function.update σ 1 (!(σ 1)) ∨
      σ' = Function.update (Function.update σ 0 (!(σ 0))) 1
        (!(Function.update σ 0 (!(σ 0)) 1)) := by
  by_cases h0 : σ' 0 = σ 0
  · by_cases h1 : σ' 1 = σ 1
    · left
      funext i
      fin_cases i <;> simp_all
    · right; right; left
      have h1' : σ' 1 = !(σ 1) := by cases b0 : σ' 1 <;> cases b1 : σ 1 <;> simp_all
      funext i
      fin_cases i <;> simp_all
  · by_cases h1 : σ' 1 = σ 1
    · right; left
      have h0' : σ' 0 = !(σ 0) := by cases b0 : σ' 0 <;> cases b1 : σ 0 <;> simp_all
      funext i
      fin_cases i <;> simp_all
    · right; right; right
      have h0' : σ' 0 = !(σ 0) := by cases b0 : σ' 0 <;> cases b1 : σ 0 <;> simp_all
      have h1' : σ' 1 = !(σ 1) := by cases b0 : σ' 1 <;> cases b1 : σ 1 <;> simp_all
      funext i
      fin_cases i <;> simp_all

private theorem long_ne_zero_all {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {m : ℕ} {b : Bool}
    (hmap : ∀ (σ : Fin 3 → Bool), σ 2 = b → ∀ v ∈ S.X (spinWt x σ),
      S.A (.positiveLong 2) m v ∈ S.X (spinWt x (Function.update σ 2 (!b))))
    (hkill : ∀ (σ : Fin 3 → Bool), σ 2 = !b → ∀ v ∈ S.X (spinWt x σ),
      S.A (.positiveLong 2) m v = 0)
    (hF : S.A (.positiveLong 2) m ≠ 0) :
    ∀ σ, σ 2 = b → ∃ v ∈ S.X (spinWt x σ), S.A (.positiveLong 2) m v ≠ 0 := by
  obtain ⟨σ₁, v₁, hv₁, hE₁⟩ : ∃ σ v, v ∈ S.X (spinWt x σ) ∧
      S.A (.positiveLong 2) m v ≠ 0 := by
    by_contra h
    push Not at h
    exact hF (by
      refine ext_of_wtSpace (diagHom 3 K) S.ρ (f := S.A (.positiveLong 2) m) (g := 0)
        fun a u hu => ?_
      change u ∈ S.X a at hu
      by_cases hm : S.mult a = 0
      · have hu0 : u = 0 := by rw [S.X_eq_bot_iff.mpr hm] at hu; simpa using hu
        rw [hu0]
        simp
      · obtain ⟨σ, rfl⟩ := exists_spinWt_of_mult_ne_zero S hP hm
        exact h σ u hu)
  have hσ₁ : σ₁ 2 = b := by
    by_contra h
    have h' : σ₁ 2 = !b := by cases b0 : σ₁ 2 <;> cases bb : b <;> simp_all
    exact hE₁ (hkill σ₁ h' v₁ hv₁)
  have hv₁0 : v₁ ≠ 0 := fun h => hE₁ (by rw [h]; simp)
  have hstep : ∀ (k : Fin 3) (hk : k ≠ 2) {σ : Fin 3 → Bool} {v : V},
      v ∈ S.X (spinWt x σ) → v ≠ 0 → S.A (.positiveLong 2) m v ≠ 0 →
      ∃ w ∈ S.X (spinWt x (Function.update σ k (!(σ k)))), S.A (.positiveLong 2) m w ≠ 0 := by
    intro k hk σ v hv hv0 hE
    refine ⟨S.ψ (lw k) v, ?_, long_shift_ne_zero S hk hv hv0 hE⟩
    have h := S.ψ_lw_mem k hv
    rwa [update_spinWt] at h
  obtain ⟨v₀, hv₀, hE₀⟩ := hstep 0 (by decide) hv₁ hv₁0 hE₁
  obtain ⟨v₁', hv₁', hE₁'⟩ := hstep 1 (by decide) hv₁ hv₁0 hE₁
  have hv₀0 : v₀ ≠ 0 := fun h => hE₀ (by rw [h]; simp)
  obtain ⟨v₂, hv₂, hE₂⟩ := hstep 1 (by decide) hv₀ hv₀0 hE₀
  intro σ hσ
  rcases bool_vec_cases (σ := σ₁) (σ' := σ) (by rw [hσ, hσ₁]) with h | h | h | h
  · rw [h]
    exact ⟨v₁, hv₁, hE₁⟩
  · rw [h]
    exact ⟨v₀, hv₀, hE₀⟩
  · rw [h]
    exact ⟨v₁', hv₁', hE₁'⟩
  · rw [h]
    exact ⟨v₂, hv₂, hE₂⟩

private theorem long_ne_zero_on {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {m : ℕ} {b : Bool}
    (hmap : ∀ (σ : Fin 3 → Bool), σ 2 = b → ∀ v ∈ S.X (spinWt x σ),
      S.A (.positiveLong 2) m v ∈ S.X (spinWt x (Function.update σ 2 (!b))))
    (hkill : ∀ (σ : Fin 3 → Bool), σ 2 = !b → ∀ v ∈ S.X (spinWt x σ),
      S.A (.positiveLong 2) m v = 0)
    (hF : S.A (.positiveLong 2) m ≠ 0) :
    ∀ σ, σ 2 = b → ∀ v ∈ S.X (spinWt x σ), v ≠ 0 → S.A (.positiveLong 2) m v ≠ 0 := by
  intro σ hσ v hv hv0
  obtain ⟨u, hu, huE⟩ := long_ne_zero_all S hP hmap hkill hF σ hσ
  have hu0 : u ≠ 0 := fun h => huE (by rw [h]; simp)
  obtain ⟨c, hc⟩ := hP.eq_smul S hu hu0 hv
  intro h0
  rw [hc, map_smul] at h0
  rcases smul_eq_zero.mp h0 with hc0 | hFu
  · exact hv0 (by rw [hc, hc0, zero_smul])
  · exact huE hFu

private theorem long_dichotomy_pos {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    (hF : S.A (.positiveLong 2) x.val ≠ 0) : S.A (.positiveLong 2) (-x).val = 0 := by
  haveI : NeZero (Nat.card Kˣ) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero x := ⟨hP.ne_zero⟩
  have hval : x.val < Nat.card Kˣ := ZMod.val_lt _
  have hval' : (-x).val < Nat.card Kˣ := ZMod.val_lt _
  have hsum : x.val + (-x).val = Nat.card Kˣ := by
    rw [show (-x).val = Nat.card Kˣ - x.val from ZMod.val_neg_of_ne_zero x]
    exact Nat.add_sub_cancel' hval.le
  have hsub' : Nat.card Kˣ - (-x).val = x.val :=
    Nat.sub_eq_of_eq_add (by omega : Nat.card Kˣ = x.val + (-x).val)
  have hfac : S.A (.positiveLong 2) ((-x).val) * S.A (.positiveLong 2) x.val =
      S.A (.positiveLong 2) (Nat.card Kˣ) := by
    rw [← S.A_mul_card_sub (.positiveLong 2) (i := (-x).val) hval'.le, hsub']
  have hAN : S.A (.positiveLong 2) (Nat.card Kˣ) = 0 := long_A_card_eq_zero S hP
  have hkill_true : ∀ (τ : Fin 3 → Bool), τ 2 = true → ∀ w ∈ S.X (spinWt x τ),
      S.A (.positiveLong 2) (-x).val w = 0 := by
    intro τ hτ2 w hw
    have hσ2 : (Function.update τ 2 false) 2 = false := by
      rw [Function.update_self]
    obtain ⟨u, hu, huE⟩ :=
      long_ne_zero_all S hP (b := false) (m := x.val)
        (fun σ hσ v hv => long_A_x_mem S hP hσ hv)
        (fun σ hσ v hv => long_A_x_apply_eq_zero S hP hσ hv) hF
        (Function.update τ 2 false) hσ2
    have hu0 : u ≠ 0 := fun h => huE (by rw [h]; simp)
    have hmem : S.A (.positiveLong 2) x.val u ∈ S.X (spinWt x τ) := by
      have h := long_A_x_mem S hP hσ2 hu
      rwa [show Function.update (Function.update τ 2 false) 2 true = τ from by
        funext i
        by_cases hi : i = 2 <;> simp [Function.update, hi, hτ2]] at h
    have hkill0 : S.A (.positiveLong 2) (-x).val (S.A (.positiveLong 2) x.val u) = 0 := by
      rw [← Module.End.mul_apply, hfac, hAN]
      simp
    by_cases hw0 : w = 0
    · rw [hw0]
      simp
    · obtain ⟨c, hc⟩ := hP.eq_smul S hmem huE hw
      rw [hc, map_smul, hkill0, smul_zero]
  refine ext_of_wtSpace (diagHom 3 K) S.ρ
    (f := S.A (.positiveLong 2) (-x).val) (g := 0) fun a v hv => ?_
  change v ∈ S.X a at hv
  by_cases hm : S.mult a = 0
  · have hv0 : v = 0 := by rw [S.X_eq_bot_iff.mpr hm] at hv; simpa using hv
    rw [hv0]
    simp
  · obtain ⟨σ, rfl⟩ := exists_spinWt_of_mult_ne_zero S hP hm
    cases h2 : σ 2
    · exact long_A_neg_x_apply_eq_zero S hP h2 hv
    · exact hkill_true σ h2 v hv

private theorem long_not_both_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x) :
    S.A (.positiveLong 2) x.val ≠ 0 ∨ S.A (.positiveLong 2) (-x).val ≠ 0 := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hpos, hneg⟩ := h
  have hpos' : S.A (.positiveLong 2) x.val = 0 := not_not.mp hpos
  have hneg' : S.A (.positiveLong 2) (-x).val = 0 := not_not.mp hneg
  have hxval : ((x.val : ℕ) : ZMod (Nat.card Kˣ)) = x := ZMod.natCast_zmod_val x
  haveI : NeZero (Nat.card Kˣ) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero x := ⟨hP.ne_zero⟩
  have hval : x.val < Nat.card Kˣ := ZMod.val_lt _
  have hsum : x.val + (-x).val = Nat.card Kˣ := by
    rw [show (-x).val = Nat.card Kˣ - x.val from ZMod.val_neg_of_ne_zero x]
    exact Nat.add_sub_cancel' hval.le
  have hvan : ∀ k, 1 ≤ k → k < Nat.card Kˣ → k ≠ x.val → k ≠ (-x).val →
      S.A (.positiveLong 2) k = 0 := by
    intro k hk1 hkN hkx hkn
    by_cases hknx : (k : ZMod (Nat.card Kˣ)) = -x
    · have hkeq : k = (-x).val := by
        rw [← ZMod.val_natCast_of_lt hkN, hknx]
      rw [hkeq]
      exact hneg'
    · refine long_A_eq_zero S hP hk1 hkN ?_ hknx
      intro hh
      apply hkx
      rw [← ZMod.val_natCast_of_lt hkN, hh]
  have hcard : S.A (.positiveLong 2) (Nat.card Kˣ) = 0 := long_A_card_eq_zero S hP
  have hvan' : ∀ k, 1 ≤ k → k ≤ Nat.card Kˣ → k ≠ x.val →
      S.A (.positiveLong 2) k = 0 := by
    intro k hk1 hkN hkx
    by_cases hlt : k < Nat.card Kˣ
    · by_cases hkn : k = (-x).val
      · rw [hkn]
        exact hneg'
      · exact hvan k hk1 hlt hkx hkn
    · have hkeq : k = Nat.card Kˣ := by omega
      rw [hkeq]
      exact hcard
  have hψ : ∀ c : K, S.ψ (elt (.positiveLong 2) c) = 1 := by
    intro c
    ext v
    rw [psi_apply_of_vanishing S (r := .positiveLong 2) (kp := x.val) (y := x)
      (ZMod.natCast_zmod_val _) (ZMod.val_pos.mpr hP.ne_zero) hval
      (fun k hk1 hkN hkz => hvan' k hk1 hkN (fun hkv => hkz (by
        rw [hkv, ZMod.natCast_zmod_val]))) c v, hpos']
    simp
  have h1 : elt (.positiveLong 2 : RootSubgroupIndex 3) (1 : K) = 1 :=
    S.ψ_injective (by rw [hψ 1, map_one])
  have h10 : elt (.positiveLong 2 : RootSubgroupIndex 3) (1 : K) =
      elt (.positiveLong 2 : RootSubgroupIndex 3) 0 := by
    rw [h1, elt_zero]
  exact one_ne_zero (elt_injective (F := K) (.positiveLong 2) h10)

private theorem short_A_kp_apply_eq_zero_of_not_src {x : ZMod (Nat.card Kˣ)}
    (hP : S.IsSpinPattern x) {r : RootSubgroupIndex 3} (hr : IsShortIndex r) {kp : ℕ}
    (hkp : (kp : ZMod (Nat.card Kˣ)) = 2 * x) {σ : Fin 3 → Bool}
    (h : ¬ IsSrc (stdVec r) σ) {v : V} (hv : v ∈ S.X (spinWt x σ)) :
    S.A r kp v = 0 := by
  have hkill := mult_add_two_mul_eq_zero_of_not_src S hP hr h
  have hmem := S.A_mem r hv kp
  rw [hkp, S.X_eq_bot_iff.mpr hkill] at hmem
  simpa using hmem

private theorem short_A_kp_mem_flip {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    {r : RootSubgroupIndex 3} (hr : IsShortIndex r) {kp : ℕ}
    (hkp : (kp : ZMod (Nat.card Kˣ)) = 2 * x) {σ : Fin 3 → Bool}
    (hsrc : IsSrc (stdVec r) σ) {v : V} (hv : v ∈ S.X (spinWt x σ)) :
    S.A r kp v ∈ S.X (spinWt x (flipAt (stdVec r) σ)) := by
  have h := S.A_mem r hv kp
  rwa [hkp, spinWt_add_two_mul_rootWt hr hsrc] at h

private theorem flipAt_difference_two {σ : Fin 3 → Bool} (h2 : σ 2 = true) :
    (flipAt (stdVec (.difference (0 : Fin 3) 2 (by decide) : RootSubgroupIndex 3)) σ) 2 =
      false := by
  have h : stdVec (.difference (0 : Fin 3) 2 (by decide) : RootSubgroupIndex 3) 2 = -1 := by
    rw [stdVec_apply_difference]
    norm_num
  simp [flipAt, h, h2]

private theorem not_src_difference_zero_two {σ : Fin 3 → Bool} (hσ : σ 2 = false) :
    ¬ IsSrc (stdVec (.difference (0 : Fin 3) 2 (by decide))) σ := by
  intro hsrc
  have h2 : σ 2 = true := (hsrc 2).2 (by
    rw [stdVec_apply_difference]
    norm_num)
  rw [hσ] at h2
  exact Bool.noConfusion h2

private theorem difference_mul_neg_x_eq_zero {x : ZMod (Nat.card Kˣ)}
    (hP : S.IsSpinPattern x) :
    S.A (.difference 0 2 (by decide)) ((2 * x).val) *
      S.A (.positiveLong 2) (-x).val = 0 := by
  have hr : IsShortIndex (.difference 0 2 (by decide) : RootSubgroupIndex 3) := by
    simp [IsShortIndex]
  have hkp : ((2 * x).val : ZMod (Nat.card Kˣ)) = 2 * x := ZMod.natCast_zmod_val _
  refine ext_of_wtSpace (diagHom 3 K) S.ρ
    (f := S.A (.difference 0 2 (by decide)) ((2 * x).val) *
      S.A (.positiveLong 2) (-x).val) (g := 0) fun a v hv => ?_
  change v ∈ S.X a at hv
  by_cases hm : S.mult a = 0
  · have hv0 : v = 0 := by rw [S.X_eq_bot_iff.mpr hm] at hv; simpa using hv
    rw [hv0]
    simp
  · obtain ⟨σ, rfl⟩ := exists_spinWt_of_mult_ne_zero S hP hm
    cases h2 : σ 2
    · have h0 := long_A_neg_x_apply_eq_zero S hP h2 hv
      rw [Module.End.mul_apply, h0]
      simp
    · have hmem := long_A_neg_x_mem S hP h2 hv
      have h0 := short_A_kp_apply_eq_zero_of_not_src S hP hr hkp
        (not_src_difference_zero_two (by rw [Function.update_self])) hmem
      rw [Module.End.mul_apply]
      exact h0

private theorem neg_x_mul_difference_eq_zero {x : ZMod (Nat.card Kˣ)}
    (hP : S.IsSpinPattern x) :
    S.A (.positiveLong 2) (-x).val *
      S.A (.difference 0 2 (by decide)) ((2 * x).val) = 0 := by
  have hr : IsShortIndex (.difference 0 2 (by decide) : RootSubgroupIndex 3) := by
    simp [IsShortIndex]
  have hkp : ((2 * x).val : ZMod (Nat.card Kˣ)) = 2 * x := ZMod.natCast_zmod_val _
  refine ext_of_wtSpace (diagHom 3 K) S.ρ
    (f := S.A (.positiveLong 2) (-x).val *
      S.A (.difference 0 2 (by decide)) ((2 * x).val)) (g := 0) fun a v hv => ?_
  change v ∈ S.X a at hv
  by_cases hm : S.mult a = 0
  · have hv0 : v = 0 := by rw [S.X_eq_bot_iff.mpr hm] at hv; simpa using hv
    rw [hv0]
    simp
  · obtain ⟨σ, rfl⟩ := exists_spinWt_of_mult_ne_zero S hP hm
    cases h2 : σ 2
    · have h0 := short_A_kp_apply_eq_zero_of_not_src S hP hr hkp
        (not_src_difference_zero_two h2) hv
      rw [Module.End.mul_apply, h0]
      simp
    · by_cases hsrc : IsSrc (stdVec (.difference 0 2 (by decide))) σ
      · have hmem := short_A_kp_mem_flip S hP hr hkp hsrc hv
        have hflip := flipAt_difference_two h2
        have h0 := long_A_neg_x_apply_eq_zero S hP hflip hmem
        rw [Module.End.mul_apply]
        exact h0
      · have h0 := short_A_kp_apply_eq_zero_of_not_src S hP hr hkp hsrc hv
        rw [Module.End.mul_apply, h0]
        simp

private theorem long_Fplus_ne_zero {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    (hE : S.A (.difference 0 1 (by decide)) (2 * x).val ≠ 0)
    (hkm : S.A (.difference 0 1 (by decide)) (-(2 * x)).val = 0)
    (hvan : ∀ r, IsShortIndex r → ∀ k, 1 ≤ k → k ≤ Nat.card Kˣ →
      (k : ZMod (Nat.card Kˣ)) ≠ 2 * x → S.A r k = 0) :
    S.A (.positiveLong 2) x.val ≠ 0 := by
  by_contra hF
  have hF' : S.A (.positiveLong 2) x.val = 0 := hF
  rcases long_not_both_zero S hP with hpos | hneg
  · exact hpos hF'
  · let r' : RootSubgroupIndex 3 := .difference 0 2 (by decide)
    have hr' : IsShortIndex r' := by simp [r', IsShortIndex]
    have hkp : ((2 * x).val : ZMod (Nat.card Kˣ)) = 2 * x := ZMod.natCast_zmod_val _
    have hEr : S.A r' ((2 * x).val) * S.A (.positiveLong 2) (-x).val = 0 :=
      difference_mul_neg_x_eq_zero S hP
    have hFr : S.A (.positiveLong 2) (-x).val * S.A r' ((2 * x).val) = 0 :=
      neg_x_mul_difference_eq_zero S hP
    have hψr' : ((S.ψ (elt r' (1 : K)) : V ≃ₗ[K] V) : V →ₗ[K] V) =
        1 + S.A r' ((2 * x).val) := by
      ext v
      change S.ψ (elt r' (1 : K)) v = (1 + S.A r' ((2 * x).val)) v
      rw [psi_apply_of_vanishing S (r := r') (kp := (2 * x).val) (y := 2 * x) hkp
        (ZMod.val_pos.mpr (two_mul_ne_zero odd_natCard_units hP.ne_zero))
        (ZMod.val_lt _) (fun k hk1 hkN hkz => hvan r' hr' k hk1 hkN hkz) (1 : K) v]
      simp
    have hψβ : ((S.ψ (elt (.positiveLong 2) (1 : K)) : V ≃ₗ[K] V) : V →ₗ[K] V) =
        1 + S.A (.positiveLong 2) (-x).val := by
      ext v
      change S.ψ (elt (.positiveLong 2) (1 : K)) v =
        (1 + S.A (.positiveLong 2) (-x).val) v
      rw [psi_apply_of_vanishing S (r := .positiveLong 2) (kp := (-x).val) (y := -x)
        (ZMod.natCast_zmod_val _)
        (ZMod.val_pos.mpr (neg_ne_zero.mpr hP.ne_zero)) (ZMod.val_lt _) ?_ (1 : K) v]
      · simp
      · intro k hk1 hkN hkz
        by_cases hlt : k < Nat.card Kˣ
        · by_cases hkx : (k : ZMod (Nat.card Kˣ)) = x
          · have hkeq : k = x.val := by
              rw [← ZMod.val_natCast_of_lt hlt, hkx]
            rw [hkeq]
            exact hF'
          · exact long_A_eq_zero S hP hk1 hlt hkx hkz
        · have hkeq : k = Nat.card Kˣ := by omega
          rw [hkeq]
          exact long_A_card_eq_zero S hP
    have hErv : ∀ w : V, S.A r' ((2 * x).val) (S.A (.positiveLong 2) (-x).val w) = 0 := by
      intro w
      have h := congrArg (fun T : Module.End K V => T w) hEr
      simpa using h
    have hFrv : ∀ w : V, S.A (.positiveLong 2) (-x).val (S.A r' ((2 * x).val) w) = 0 := by
      intro w
      have h := congrArg (fun T : Module.End K V => T w) hFr
      simpa using h
    have hmul : ((S.ψ (elt r' (1 : K)) * S.ψ (elt (.positiveLong 2) (1 : K)) :
        V ≃ₗ[K] V) : V →ₗ[K] V) =
        ((S.ψ (elt (.positiveLong 2) (1 : K)) * S.ψ (elt r' (1 : K)) :
          V ≃ₗ[K] V) : V →ₗ[K] V) := by
      rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul, hψr', hψβ]
      ext v
      simp only [Module.End.mul_apply, LinearMap.add_apply]
      have hone : ∀ w : V, (1 : Module.End K V) w = w := fun w => rfl
      simp only [hone, map_add, hErv, hFrv, add_zero]
      abel
    have hcomm : S.ψ (elt r' (1 : K)) * S.ψ (elt (.positiveLong 2) (1 : K)) =
        S.ψ (elt (.positiveLong 2) (1 : K)) * S.ψ (elt r' (1 : K)) :=
      LinearEquiv.ext fun v => LinearMap.ext_iff.mp hmul v
    have heq : elt r' (1 : K) * elt (.positiveLong 2) (1 : K) =
        elt (.positiveLong 2) (1 : K) * elt r' (1 : K) := by
      apply S.ψ_injective
      rw [map_mul, map_mul]
      exact hcomm
    exact not_commute_elt_difference_positiveLong (show Commute _ _ from heq)

private theorem long_vanishing {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    (hF : S.A (.positiveLong 2) x.val ≠ 0) :
    ∀ k, 1 ≤ k → k ≤ Nat.card Kˣ → (k : ZMod (Nat.card Kˣ)) ≠ x →
      S.A (.positiveLong 2) k = 0 := by
  have hneg0 : S.A (.positiveLong 2) (-x).val = 0 := long_dichotomy_pos S hP hF
  intro k hk1 hkN hkz
  by_cases hlt : k < Nat.card Kˣ
  · by_cases hkn : (k : ZMod (Nat.card Kˣ)) = -x
    · have hkeq : k = (-x).val := by
        rw [← ZMod.val_natCast_of_lt hlt, hkn]
      rw [hkeq]
      exact hneg0
    · exact long_A_eq_zero S hP hk1 hlt hkz hkn
  · have hkeq : k = Nat.card Kˣ := by omega
    rw [hkeq]
    exact long_A_card_eq_zero S hP

private theorem long_mp_pow_two {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x)
    (hF : S.A (.positiveLong 2) x.val ≠ 0)
    (hvan : ∀ k, 1 ≤ k → k ≤ Nat.card Kˣ → (k : ZMod (Nat.card Kˣ)) ≠ x →
      S.A (.positiveLong 2) k = 0) :
    ∃ l', 2 ^ l' = x.val := by
  by_contra h
  simp only [not_exists] at h
  have hval1 : 1 ≤ x.val := ZMod.val_pos.mpr hP.ne_zero
  have hvalN : x.val < Nat.card Kˣ := ZMod.val_lt _
  obtain ⟨i, j, hi0, hj0, hij, hsum, hfac⟩ :=
    S.exists_A_eq_mul (.positiveLong 2) hval1 (by omega) fun l hh => h l hh.symm
  have hiN : i < Nat.card Kˣ := by omega
  have hix : i ≠ x.val := by omega
  have hiz : (i : ZMod (Nat.card Kˣ)) ≠ x := by
    intro hh
    apply hix
    rw [← ZMod.val_natCast_of_lt hiN, hh]
  have hiA : S.A (.positiveLong 2) i = 0 := hvan i (by omega) (by omega) hiz
  exact hF (by rw [hfac, hiA, zero_mul])

structure SpinRoots (S : SpinSetting K V) where
  x : ZMod (Nat.card Kˣ)
  pattern : S.IsSpinPattern x
  l : ℕ
  l' : ℕ
  short_apply : ∀ r : RootSubgroupIndex 3, IsShortIndex r → ∀ (c : K) (v : V),
    S.ψ (elt r c) v = v + c ^ (2 ^ l) • S.A r (2 ^ l) v
  short_src : ∀ r : RootSubgroupIndex 3, IsShortIndex r → ∀ σ, IsSrc (stdVec r) σ →
    ∀ v ∈ S.X (spinWt x σ), S.A r (2 ^ l) v ∈ S.X (spinWt x (flipAt (stdVec r) σ))
  short_not_src : ∀ r : RootSubgroupIndex 3, IsShortIndex r → ∀ σ, ¬ IsSrc (stdVec r) σ →
    ∀ v ∈ S.X (spinWt x σ), S.A r (2 ^ l) v = 0
  long_apply : ∀ (c : K) (v : V),
    S.ψ (elt (.positiveLong 2) c) v = v + c ^ (2 ^ l') • S.A (.positiveLong 2) (2 ^ l') v
  long_src : ∀ σ : Fin 3 → Bool, σ 2 = false → ∀ v ∈ S.X (spinWt x σ),
    S.A (.positiveLong 2) (2 ^ l') v ∈ S.X (spinWt x (Function.update σ 2 true))
  long_not_src : ∀ σ : Fin 3 → Bool, σ 2 = true → ∀ v ∈ S.X (spinWt x σ),
    S.A (.positiveLong 2) (2 ^ l') v = 0
  long_ne_zero : ∀ σ : Fin 3 → Bool, σ 2 = false → ∀ v ∈ S.X (spinWt x σ), v ≠ 0 →
    S.A (.positiveLong 2) (2 ^ l') v ≠ 0

theorem nonempty_spinRoots {x : ZMod (Nat.card Kˣ)} (hP : S.IsSpinPattern x) :
    Nonempty S.SpinRoots := by
  obtain ⟨x, hP, hE⟩ : ∃ x, S.IsSpinPattern x ∧
      S.A (.difference 0 1 (by decide)) (2 * x).val ≠ 0 := by
    by_cases h : S.A (.difference 0 1 (by decide)) (2 * x).val ≠ 0
    · exact ⟨x, hP, h⟩
    · have h0 : S.A (.difference 0 1 (by decide)) (2 * x).val = 0 := not_not.mp h
      refine ⟨-x, hP.neg, ?_⟩
      have h2 : (2 : ZMod (Nat.card Kˣ)) * (-x) = -(2 * x) := by ring
      rw [h2]
      rcases short_not_both_zero S hP with h' | h'
      · exact absurd h0 h'
      · exact h'
  have hx' : (2 : ZMod (Nat.card Kˣ)) * x ≠ 0 := two_mul_ne_zero odd_natCard_units hP.ne_zero
  have hkm : S.A (.difference 0 1 (by decide)) (-(2 * x)).val = 0 :=
    short_dichotomy S hP (r := .difference 0 1 (by decide)) (by simp [IsShortIndex]) hE
  have hvan := short_vanishing S hP hE hkm
  obtain ⟨l, hl⟩ := short_kp_pow_two S hP hE hvan
  have hF : S.A (.positiveLong 2) x.val ≠ 0 := long_Fplus_ne_zero S hP hE hkm hvan
  have hvanβ := long_vanishing S hP hF
  obtain ⟨l', hl'⟩ := long_mp_pow_two S hP hF hvanβ
  have hkp : ((2 ^ l : ℕ) : ZMod (Nat.card Kˣ)) = 2 * x := by
    rw [hl]
    exact ZMod.natCast_zmod_val _
  have hkpN : 2 ^ l < Nat.card Kˣ := by rw [hl]; exact ZMod.val_lt _
  have hkp1 : 1 ≤ 2 ^ l := by rw [hl]; exact ZMod.val_pos.mpr hx'
  have hmp : ((2 ^ l' : ℕ) : ZMod (Nat.card Kˣ)) = x := by
    rw [hl']
    exact ZMod.natCast_zmod_val _
  have hmpN : 2 ^ l' < Nat.card Kˣ := by rw [hl']; exact ZMod.val_lt _
  have hmp1 : 1 ≤ 2 ^ l' := by rw [hl']; exact ZMod.val_pos.mpr hP.ne_zero
  refine ⟨x, hP, l, l', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr c v
    exact psi_apply_of_vanishing S (r := r) (kp := 2 ^ l) (y := 2 * x) hkp hkp1 hkpN
      (fun k hk1 hkN hkz => hvan r hr k hk1 hkN hkz) c v
  · intro r hr σ hsrc v hv
    have h := short_A_kp_mem_flip S hP hr (kp := (2 * x).val) (ZMod.natCast_zmod_val _)
      hsrc hv
    simpa only [hl] using h
  · intro r hr σ hnot v hv
    exact short_A_kp_apply_eq_zero_of_not_src S hP hr hkp hnot hv
  · intro c v
    exact psi_apply_of_vanishing S (r := .positiveLong 2) (kp := 2 ^ l') (y := x) hmp hmp1
      hmpN (fun k hk1 hkN hkz => hvanβ k hk1 hkN hkz) c v
  · intro σ hσ v hv
    have h := long_A_x_mem S hP hσ hv
    simpa only [hl'] using h
  · intro σ hσ v hv
    have h := long_A_x_apply_eq_zero S hP hσ hv
    simpa only [hl'] using h
  · intro σ hσ v hv hv0
    have h := long_ne_zero_on S hP (b := false) (m := x.val)
      (fun σ hσ v hv => long_A_x_mem S hP hσ hv)
      (fun σ hσ v hv => long_A_x_apply_eq_zero S hP hσ hv) hF σ hσ v hv hv0
    simpa only [hl'] using h

end SpinSetting

end CFSG.LieType.Sp6Spin
