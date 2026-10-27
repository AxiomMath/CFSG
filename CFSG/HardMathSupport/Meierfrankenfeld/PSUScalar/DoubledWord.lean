module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

variable {α : Type*}

theorem period_shift_nsmul {N s : ℕ} (w : ZMod N → α)
    (hper : ∀ i, w (i + (s : ZMod N)) = w i) (k : ℕ) (i : ZMod N) :
    w (i + ((k * s : ℕ) : ZMod N)) = w i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Nat.cast_add, ← add_assoc, hper]
      exact ih

theorem zsmul_period {N s : ℕ} (w : ZMod N → α)
    (hper : ∀ i, w (i + (s : ZMod N)) = w i) :
    ∀ a ∈ AddSubgroup.zmultiples (s : ZMod N), ∀ i, w (i + a) = w i := by
  let P : AddSubgroup (ZMod N) :=
    { carrier := {a | ∀ i, w (i + a) = w i}
      zero_mem' := by
        intro i
        simp
      add_mem' := by
        intro a b ha hb i
        rw [← add_assoc, hb, ha]
      neg_mem' := by
        intro a ha i
        have h := ha (i + -a)
        rw [add_assoc, neg_add_cancel, add_zero] at h
        exact h.symm }
  have hsP : (s : ZMod N) ∈ P := hper
  have hle : AddSubgroup.zmultiples (s : ZMod N) ≤ P :=
    AddSubgroup.zmultiples_le.mpr hsP
  exact fun a ha => hle ha

theorem dvd_two_mul_of_minimal_period (_star : α → α) (_z : α) {f s : ℕ}
    (w : ZMod (2 * f) → α) (_hf : 0 < f) (hs : 0 < s)
    (hper : ∀ i, w (i + (s : ZMod (2 * f))) = w i)
    (hmin : ∀ s', 0 < s' → s' < s → ∃ i, w (i + (s' : ZMod (2 * f))) ≠ w i) :
    s ∣ 2 * f := by
  let g := Nat.gcd s (2 * f)
  have hgmem : (g : ZMod (2 * f)) ∈ AddSubgroup.zmultiples (s : ZMod (2 * f)) := by
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨(Nat.gcdA s (2 * f) : ℤ), ?_⟩
    have hbez := congrArg (fun z : ℤ => (z : ZMod (2 * f)))
      (Nat.gcd_eq_gcd_ab s (2 * f))
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self] at hbez
    rw [zsmul_eq_mul]
    simpa [g, mul_comm] using hbez.symm
  have hgper : ∀ i, w (i + (g : ZMod (2 * f))) = w i :=
    zsmul_period w hper (g : ZMod (2 * f)) hgmem
  have hgle : g ≤ s := Nat.le_of_dvd hs (Nat.gcd_dvd_left s (2 * f))
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left (2 * f) hs
  have hgeq : g = s := by
    by_contra hne
    have hlt : g < s := lt_of_le_of_ne hgle hne
    obtain ⟨i, hi⟩ := hmin g hgpos hlt
    exact hi (hgper i)
  exact Nat.gcd_eq_left_iff_dvd.mp (by simpa [g] using hgeq)

theorem div_dvd_card_ne (star : α → α) (z : α) {f s : ℕ}
    (w : ZMod (2 * f) → α) (hf : 0 < f) (hs : 0 < s)
    (hper : ∀ i, w (i + (s : ZMod (2 * f))) = w i)
    (hmin : ∀ s', 0 < s' → s' < s → ∃ i, w (i + (s' : ZMod (2 * f))) ≠ w i) :
    2 * f / s ∣ Nat.card {i : ZMod (2 * f) // w i ≠ z} := by
  classical
  have hdvd := dvd_two_mul_of_minimal_period star z w hf hs hper hmin
  have hNpos : 0 < 2 * f := Nat.mul_pos (by norm_num) hf
  have : NeZero (2 * f) := ⟨Nat.ne_of_gt hNpos⟩
  let H : AddSubgroup (ZMod (2 * f)) := AddSubgroup.zmultiples (s : ZMod (2 * f))
  have hHcard : Nat.card H = 2 * f / s := by
    dsimp [H]
    rw [Nat.card_zmultiples, ZMod.addOrderOf_coe s (Nat.ne_of_gt hNpos)]
    rw [Nat.gcd_eq_right hdvd]
  let A := {i : ZMod (2 * f) // w i ≠ z}
  let vaddH : H → A → A := fun a x =>
    ⟨(a : ZMod (2 * f)) + x.1, by
      have h : w ((a : ZMod (2 * f)) + x.1) = w x.1 := by
        rw [add_comm]
        exact zsmul_period w hper (a : ZMod (2 * f)) a.2 x.1
      intro hxz
      exact x.2 (h.symm.trans hxz)⟩
  let : AddAction H A :=
    { vadd := vaddH
      zero_vadd := by
        intro x
        apply Subtype.ext
        change (0 : ZMod (2 * f)) + x.1 = x.1
        simp
      add_vadd := by
        intro a b x
        apply Subtype.ext
        change ((a : ZMod (2 * f)) + (b : ZMod (2 * f))) + x.1 =
          (a : ZMod (2 * f)) + ((b : ZMod (2 * f)) + x.1)
        rw [add_assoc] }
  have hvadd : ∀ (a : H) (x : A),
      (a +ᵥ x).1 = (a : ZMod (2 * f)) + x.1 := fun _ _ => rfl
  have hfree : ∀ b : A, AddAction.stabilizer H b = ⊥ := by
    intro b
    ext a
    constructor
    · intro ha
      rw [AddSubgroup.mem_bot]
      apply Subtype.ext
      have h := congrArg Subtype.val (AddAction.mem_stabilizer_iff.mp ha)
      rw [hvadd] at h
      have h' : (a : ZMod (2 * f)) + b.1 = 0 + b.1 := by simpa using h
      exact add_right_cancel h'
    · intro ha
      rw [AddSubgroup.mem_bot] at ha
      subst ha
      simp
  have hcardA : Nat.card A =
      Nat.card (Quotient (AddAction.orbitRel H A)) * (2 * f / s) := by
    have e := AddAction.selfEquivOrbitsQuotientProd (G := H) (X := A) hfree
    calc
      Nat.card A = Nat.card (Quotient (AddAction.orbitRel H A) × H) := Nat.card_congr e
      _ = Nat.card (Quotient (AddAction.orbitRel H A)) * Nat.card H := Nat.card_prod _ _
      _ = Nat.card (Quotient (AddAction.orbitRel H A)) * (2 * f / s) := by rw [hHcard]
  have hdiv : 2 * f / s ∣ Nat.card A := by
    rw [hcardA]
    exact dvd_mul_left _ _
  exact hdiv

theorem two_mul_le_mul_card_ne (star : α → α) (z : α) {f s : ℕ}
    (w : ZMod (2 * f) → α) (hf : 0 < f) (hs : 0 < s)
    (hper : ∀ i, w (i + (s : ZMod (2 * f))) = w i)
    (hmin : ∀ s', 0 < s' → s' < s → ∃ i, w (i + (s' : ZMod (2 * f))) ≠ w i)
    (hT : 0 < Nat.card {i : ZMod (2 * f) // w i ≠ z}) :
    2 * f ≤ s * Nat.card {i : ZMod (2 * f) // w i ≠ z} := by
  have hNpos : 0 < 2 * f := Nat.mul_pos (by norm_num) hf
  have hdvd := dvd_two_mul_of_minimal_period star z w hf hs hper hmin
  have hdiv := div_dvd_card_ne star z w hf hs hper hmin
  have hle : s ≤ 2 * f := Nat.le_of_dvd hNpos hdvd
  have hhpos : 0 < 2 * f / s := Nat.div_pos hle hs
  have hhle : 2 * f / s ≤ Nat.card {i : ZMod (2 * f) // w i ≠ z} :=
    Nat.le_of_dvd hT hdiv
  calc
    2 * f = s * (2 * f / s) := (Nat.mul_div_cancel' hdvd).symm
    _ ≤ s * Nat.card {i : ZMod (2 * f) // w i ≠ z} := Nat.mul_le_mul_left s hhle

theorem star_eq_of_even (star : α → α) (z : α) {f s : ℕ}
    (w : ZMod (2 * f) → α) (hf : 0 < f)
    (hw : ∀ i, w (i + (f : ZMod (2 * f))) = star (w i)) (hs : 0 < s)
    (hper : ∀ i, w (i + (s : ZMod (2 * f))) = w i)
    (hmin : ∀ s', 0 < s' → s' < s → ∃ i, w (i + (s' : ZMod (2 * f))) ≠ w i)
    (heven : Even (2 * f / s)) : ∀ i, star (w i) = w i := by
  have hdvd := dvd_two_mul_of_minimal_period star z w hf hs hper hmin
  have hNmul : s * (2 * f / s) = 2 * f := Nat.mul_div_cancel' hdvd
  obtain ⟨k, hk⟩ := heven
  have hsk : s * k = f := by
    have h2 : 2 * (s * k) = 2 * f := by
      calc
        2 * (s * k) = s * k + s * k := by rw [two_mul]
        _ = s * (k + k) := by rw [mul_add]
        _ = s * (2 * f / s) := by rw [hk]
        _ = 2 * f := hNmul
    exact Nat.mul_left_cancel (by norm_num : 0 < 2) h2
  have hfper : ∀ i, w (i + (f : ZMod (2 * f))) = w i := by
    intro i
    have hfk : f = k * s := by rw [← hsk, Nat.mul_comm]
    rw [show (f : ZMod (2 * f)) = ((k * s : ℕ) : ZMod (2 * f)) from
      congrArg (fun n : ℕ => (n : ZMod (2 * f))) hfk]
    exact period_shift_nsmul w hper k i
  intro i
  rw [← hw i, hfper i]

theorem eq_two_mul_of_card_ne_eq_two (star : α → α) (z : α) {f s : ℕ}
    (w : ZMod (2 * f) → α) (hf : 0 < f)
    (hw : ∀ i, w (i + (f : ZMod (2 * f))) = star (w i)) (hs : 0 < s)
    (hper : ∀ i, w (i + (s : ZMod (2 * f))) = w i)
    (hmin : ∀ s', 0 < s' → s' < s → ∃ i, w (i + (s' : ZMod (2 * f))) ≠ w i)
    (hT : Nat.card {i : ZMod (2 * f) // w i ≠ z} = 2)
    (hns : ∃ i, star (w i) ≠ w i) : s = 2 * f := by
  have hdvd := dvd_two_mul_of_minimal_period star z w hf hs hper hmin
  have hdiv := div_dvd_card_ne star z w hf hs hper hmin
  have hhdvd2 : 2 * f / s ∣ 2 := by
    have h := hdiv
    rwa [hT] at h
  have hcases : 2 * f / s = 1 ∨ 2 * f / s = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hhdvd2
  have hnotEven : ¬ Even (2 * f / s) := by
    intro he
    obtain ⟨i, hi⟩ := hns
    exact hi (star_eq_of_even star z w hf hw hs hper hmin he i)
  have h1 : 2 * f / s = 1 := by
    rcases hcases with h1 | h2
    · exact h1
    · exfalso
      exact hnotEven (by rw [h2]; exact ⟨1, by norm_num⟩)
  have hNmul : s * (2 * f / s) = 2 * f := Nat.mul_div_cancel' hdvd
  rw [h1, Nat.mul_one] at hNmul
  exact hNmul

theorem eq_two_mul_of_card_ne_eq_four (star : α → α) (z : α) {f s : ℕ}
    (w : ZMod (2 * f) → α) (hf : 0 < f)
    (hw : ∀ i, w (i + (f : ZMod (2 * f))) = star (w i)) (hs : 0 < s)
    (hper : ∀ i, w (i + (s : ZMod (2 * f))) = w i)
    (hmin : ∀ s', 0 < s' → s' < s → ∃ i, w (i + (s' : ZMod (2 * f))) ≠ w i)
    (hT : Nat.card {i : ZMod (2 * f) // w i ≠ z} = 4)
    (hns : ∃ i, star (w i) ≠ w i) : s = 2 * f := by
  have hdvd := dvd_two_mul_of_minimal_period star z w hf hs hper hmin
  have hdiv := div_dvd_card_ne star z w hf hs hper hmin
  have hhdvd4 : 2 * f / s ∣ 4 := by
    have h := hdiv
    rwa [hT] at h
  have hnotEven : ¬ Even (2 * f / s) := by
    intro he
    obtain ⟨i, hi⟩ := hns
    exact hi (star_eq_of_even star z w hf hw hs hper hmin he i)
  have hdvd2 : 2 * f / s ∣ 2 ^ 2 := by simpa using hhdvd4
  obtain ⟨k, hk, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have h1 : 2 * f / s = 1 := by
    interval_cases k
    · simpa using hk_eq
    · exfalso
      exact hnotEven (by rw [hk_eq]; exact ⟨1, by norm_num⟩)
    · exfalso
      exact hnotEven (by rw [hk_eq]; exact ⟨2, by norm_num⟩)
  have hNmul : s * (2 * f / s) = 2 * f := Nat.mul_div_cancel' hdvd
  rw [h1, Nat.mul_one] at hNmul
  exact hNmul

theorem card_ne_eq_two_mul (star : α → α) (z : α) {f : ℕ}
    (w : ZMod (2 * f) → α) (hf : 0 < f)
    (hw : ∀ i, w (i + (f : ZMod (2 * f))) = star (w i))
    (hstar : ∀ a, star (star a) = a) (hz : star z = z) :
    Nat.card {i : ZMod (2 * f) // w i ≠ z} =
      2 * Nat.card {i : ZMod (2 * f) // i.val < f ∧ w i ≠ z} := by
  classical
  have : NeZero (2 * f) :=
    ⟨Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hf)⟩
  have : Fintype (ZMod (2 * f)) := ZMod.fintype (2 * f)
  have hfi : (f : ZMod (2 * f)).val = f :=
    ZMod.val_natCast_of_lt (by omega)
  have hff : (f : ZMod (2 * f)) + (f : ZMod (2 * f)) = 0 := by
    rw [← Nat.cast_add, show f + f = 2 * f by omega, ZMod.natCast_self]
  have hshift_shift : ∀ i : ZMod (2 * f),
      (i + (f : ZMod (2 * f))) + (f : ZMod (2 * f)) = i := by
    intro i
    rw [add_assoc, hff, add_zero]
  have hval1 : ∀ i : ZMod (2 * f), i.val < f →
      (i + (f : ZMod (2 * f))).val = i.val + f := by
    intro i hi
    rw [ZMod.val_add_of_lt]
    · rw [hfi]
    · rw [hfi]
      omega
  have hval2 : ∀ i : ZMod (2 * f), ¬ i.val < f →
      (i + (f : ZMod (2 * f))).val = i.val - f := by
    intro i hi
    rw [ZMod.val_add_of_le]
    · rw [hfi]
      omega
    · rw [hfi]
      omega
  have hstar_ne : ∀ a, star a ≠ z ↔ a ≠ z := by
    intro a
    constructor
    · intro h ha
      exact h (by rw [ha, hz])
    · intro h hsa
      apply h
      calc
        a = star (star a) := (hstar a).symm
        _ = star z := by rw [hsa]
        _ = z := hz
  let P : ZMod (2 * f) → Prop := fun i => i.val < f ∧ w i ≠ z
  let Q : ZMod (2 * f) → Prop := fun i => ¬ i.val < f ∧ w i ≠ z
  have hdisj : Disjoint P Q := by
    rw [disjoint_iff]
    funext i
    apply propext
    constructor
    · intro h
      exact h.2.1 h.1.1
    · intro h
      exact False.elim h
  let A1 := {i : ZMod (2 * f) // P i}
  let A2 := {i : ZMod (2 * f) // Q i}
  let e : A1 ≃ A2 :=
    { toFun := fun i =>
        ⟨i.1 + (f : ZMod (2 * f)), by
          constructor
          · have hval := hval1 i.1 i.2.1
            omega
          · rw [hw i.1]
            exact (hstar_ne (w i.1)).mpr i.2.2⟩
      invFun := fun i =>
        ⟨i.1 + (f : ZMod (2 * f)), by
          constructor
          · have hval := hval2 i.1 i.2.1
            have hival : i.1.val < 2 * f := ZMod.val_lt i.1
            omega
          · rw [hw i.1]
            exact (hstar_ne (w i.1)).mpr i.2.2⟩
      left_inv := by
        intro i
        apply Subtype.ext
        exact hshift_shift i.1
      right_inv := by
        intro i
        apply Subtype.ext
        exact hshift_shift i.1 }
  have hA : Nat.card {i : ZMod (2 * f) // w i ≠ z} =
      Nat.card {i : ZMod (2 * f) // P i ∨ Q i} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro i
    constructor
    · intro h
      by_cases hi : i.val < f
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr ⟨hi, h⟩
    · intro h
      rcases h with ⟨_, hw'⟩ | ⟨_, hw'⟩
      · exact hw'
      · exact hw'
  have hpart : Nat.card {i : ZMod (2 * f) // P i ∨ Q i} =
      Nat.card A1 + Nat.card A2 := by
    calc
      Nat.card {i : ZMod (2 * f) // P i ∨ Q i} = Nat.card (A1 ⊕ A2) :=
        Nat.card_congr (subtypeOrEquiv P Q hdisj)
      _ = Nat.card A1 + Nat.card A2 := by
        simp only [Nat.card_eq_fintype_card]
        exact Fintype.card_sum
  have hcard12 : Nat.card A1 = Nat.card A2 := Nat.card_congr e
  calc
    Nat.card {i : ZMod (2 * f) // w i ≠ z} = Nat.card A1 + Nat.card A2 := by
      rw [hA, hpart]
    _ = Nat.card A1 + Nat.card A1 := by rw [hcard12]
    _ = 2 * Nat.card A1 := by omega
    _ = 2 * Nat.card {i : ZMod (2 * f) // i.val < f ∧ w i ≠ z} := by
      rfl

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

end
