module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Set.Finite.Basic

public section

namespace CFSG.KS.Asc82Syl

variable {R : Type*} [Ring R]

def Spm (w : ℕ → R) (l : ℕ) : Set R := {x | ∃ e < 2 ^ l, x = w e ∨ x = -w e}

theorem mem_Spm {w : ℕ → R} {l : ℕ} {x : R} :
    x ∈ Spm w l ↔ ∃ e < 2 ^ l, x = w e ∨ x = -w e := Iff.rfl

theorem Spm_neg {w : ℕ → R} {l : ℕ} {x : R} (h : x ∈ Spm w l) : -x ∈ Spm w l := by
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inr (by rw [h])⟩
  · exact ⟨e, he, Or.inl (by rw [h, neg_neg])⟩

theorem Spm_w {w : ℕ → R} {l e : ℕ} (he : e < 2 ^ l) : w e ∈ Spm w l := ⟨e, he, Or.inl rfl⟩

theorem Spm_mono {w : ℕ → R} {l l' : ℕ} (hl : l ≤ l') : Spm w l ⊆ Spm w l' := by
  rintro x ⟨e, he, h⟩
  exact ⟨e, Nat.lt_of_lt_of_le he (Nat.pow_le_pow_right (by omega) hl), h⟩

theorem top_bit {e l : ℕ} (h0 : 0 < e) (hl : e < 2 ^ l) :
    ∃ i < l, ∃ e' < 2 ^ i, e = e' + 2 ^ i := by
  refine ⟨Nat.log 2 e, ?_, e - 2 ^ Nat.log 2 e, ?_, ?_⟩
  · exact Nat.log_lt_of_lt_pow (by omega) hl
  · have := Nat.lt_pow_succ_log_self (b := 2) (by omega) e
    rw [Nat.pow_succ] at this
    omega
  · have := Nat.pow_log_le_self 2 (by omega : e ≠ 0)
    omega

variable {w a : ℕ → R} {m : ℕ}

theorem conj_l (hw0 : w 0 = 1) (hstep : ∀ j < m, ∀ e < 2 ^ j, w (e + 2 ^ j) = w e * a j)
    {l j : ℕ} (hlj : l ≤ j) (hjm : j < m) (hcl : ∀ x ∈ Spm w l, ∀ y ∈ Spm w l, x * y ∈ Spm w l)
    (hc : ∀ i < l, ∃ y ∈ Spm w l, a i * a j = a j * y) :
    ∀ x ∈ Spm w l, ∃ y ∈ Spm w l, x * a j = a j * y := by
  have key : ∀ e < 2 ^ l, ∃ y ∈ Spm w l, w e * a j = a j * y := by
    intro e
    induction e using Nat.strong_induction_on with
    | _ e ih =>
      intro he
      rcases Nat.eq_zero_or_pos e with rfl | h0
      · exact ⟨1, by rw [← hw0]; exact Spm_w (Nat.two_pow_pos l), by rw [hw0, one_mul, mul_one]⟩
      · obtain ⟨i, hil, e', he', rfl⟩ := top_bit h0 he
        have he'l : e' < 2 ^ l :=
          Nat.lt_of_lt_of_le he' (Nat.pow_le_pow_right (by omega) (by omega))
        obtain ⟨y', hy', h1⟩ := ih e' (by have := Nat.two_pow_pos i; omega) he'l
        obtain ⟨y, hy, h2⟩ := hc i hil
        refine ⟨y' * y, hcl _ hy' _ hy, ?_⟩
        rw [hstep i (by omega) e' he', mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  rintro x ⟨e, he, rfl | rfl⟩
  · exact key e he
  · obtain ⟨y, hy, h⟩ := key e he
    exact ⟨-y, Spm_neg hy, by rw [neg_mul, h, mul_neg]⟩

theorem Spm_finite (w : ℕ → R) (l : ℕ) : (Spm w l).Finite := by
  classical
  refine Set.Finite.subset (((Finset.range (2 ^ l)).image w ∪
    (Finset.range (2 ^ l)).image (fun e => -w e) : Finset R).finite_toSet) ?_
  rintro x ⟨e, he, rfl | rfl⟩
  · simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union, Set.mem_image,
      Set.mem_Iio]
    exact Or.inl ⟨e, he, rfl⟩
  · simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union, Set.mem_image,
      Set.mem_Iio]
    exact Or.inr ⟨e, he, rfl⟩

theorem Spm_succ (hstep : ∀ j < m, ∀ e < 2 ^ j, w (e + 2 ^ j) = w e * a j) {j : ℕ} (hj : j < m)
    {x : R} : x ∈ Spm w (j + 1) ↔ x ∈ Spm w j ∨ ∃ s ∈ Spm w j, x = s * a j := by
  constructor
  · rintro ⟨e, he, hx⟩
    by_cases hlt : e < 2 ^ j
    · exact Or.inl ⟨e, hlt, hx⟩
    · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 ^ j := ⟨e - 2 ^ j, by omega⟩
      have he' : e' < 2 ^ j := by rw [Nat.pow_succ] at he; omega
      rw [hstep j hj e' he'] at hx
      rcases hx with hx | hx
      · exact Or.inr ⟨w e', Spm_w he', hx⟩
      · exact Or.inr ⟨-w e', Spm_neg (Spm_w he'), by rw [hx, neg_mul]⟩
  · rintro (hx | ⟨s, ⟨e, he, hs⟩, rfl⟩)
    · exact Spm_mono (by omega) hx
    · have he2 : e + 2 ^ j < 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
      rcases hs with rfl | rfl
      · exact ⟨e + 2 ^ j, he2, Or.inl (hstep j hj e he).symm⟩
      · exact ⟨e + 2 ^ j, he2, Or.inr (by rw [hstep j hj e he, neg_mul])⟩

theorem S_mul (hw0 : w 0 = 1) (hstep : ∀ j < m, ∀ e < 2 ^ j, w (e + 2 ^ j) = w e * a j)
    (hunit : ∀ j < m, IsUnit (a j)) (hsq : ∀ j < m, a j * a j ∈ Spm w j)
    (hc : ∀ j < m, ∀ i < j, ∃ y ∈ Spm w j, a i * a j = a j * y) :
    ∀ j ≤ m, ∀ x ∈ Spm w j, ∀ y ∈ Spm w j, x * y ∈ Spm w j := by
  intro j
  induction j with
  | zero =>
    intro _ x hx y hy
    have h1 : ∀ z ∈ Spm w 0, z = 1 ∨ z = -1 := by
      rintro z ⟨e, he, hz⟩
      have : e = 0 := by simpa using he
      rw [this, hw0] at hz
      exact hz
    have hm : ∀ z, z = 1 ∨ z = -1 → z ∈ Spm w 0 := by
      rintro z (rfl | rfl)
      · exact ⟨0, by decide, Or.inl hw0.symm⟩
      · exact ⟨0, by decide, Or.inr (by rw [hw0])⟩
    apply hm
    rcases h1 x hx with rfl | rfl <;> rcases h1 y hy with rfl | rfl <;> simp
  | succ j ih =>
    intro hj
    have hjm : j < m := by omega
    have hcl := ih (by omega)
    have hconj := conj_l (w := w) (a := a) (m := m) hw0 hstep le_rfl hjm hcl (hc j hjm)
    have hrev : ∀ t ∈ Spm w j, ∃ x ∈ Spm w j, a j * t = x * a j := by
      classical
      let φ : R → R := fun x => if h : x ∈ Spm w j then (hconj x h).choose else x
      have hφ : ∀ x ∈ Spm w j, φ x ∈ Spm w j ∧ x * a j = a j * φ x := by
        intro x hx
        simp only [φ, dif_pos hx]
        exact (hconj x hx).choose_spec
      have hmaps : Set.MapsTo φ (Spm w j) (Spm w j) := fun x hx => (hφ x hx).1
      have hinj : Set.InjOn φ (Spm w j) := by
        intro x hx x' hx' e
        have h1 := (hφ x hx).2
        have h2 := (hφ x' hx').2
        rw [e, ← h2] at h1
        exact (hunit j hjm).mul_right_cancel h1
      have hsurj := ((Spm_finite w j).injOn_iff_bijOn_of_mapsTo hmaps).1 hinj
      intro t ht
      obtain ⟨x, hx, rfl⟩ := hsurj.surjOn ht
      exact ⟨x, hx, (hφ x hx).2.symm⟩
    intro x hx y hy
    rw [Spm_succ hstep hjm] at hx hy ⊢
    rcases hx with hx | ⟨s, hs, rfl⟩ <;> rcases hy with hy | ⟨t, ht, rfl⟩
    · exact Or.inl (hcl _ hx _ hy)
    · exact Or.inr ⟨x * t, hcl _ hx _ ht, by rw [mul_assoc]⟩
    · obtain ⟨z, hz, e⟩ := hrev y hy
      exact Or.inr ⟨s * z, hcl _ hs _ hz, by rw [mul_assoc, e, ← mul_assoc]⟩
    · obtain ⟨z, hz, e⟩ := hrev t ht
      refine Or.inl ?_
      have : s * a j * (t * a j) = s * z * (a j * a j) := by
        rw [← mul_assoc, mul_assoc s, e, ← mul_assoc, mul_assoc (s * z)]
      rw [this]
      exact hcl _ (hcl _ hs _ hz) _ (hsq j hjm)

def Cpm (x y : R) : Prop := x * y = y * x ∨ x * y = -(y * x)

theorem Cpm_iff {x y : R} : Cpm x y ↔ x * y = y * x ∨ x * y = -(y * x) := Iff.rfl

theorem Cpm_of_gens (hw0 : w 0 = 1) (hstep : ∀ j < m, ∀ e < 2 ^ j, w (e + 2 ^ j) = w e * a j)
    {l : ℕ} (hl : l ≤ m) {z : R} (hz : ∀ i < l, Cpm (a i) z) : ∀ x ∈ Spm w l, Cpm x z := by
  have key : ∀ e < 2 ^ l, Cpm (w e) z := by
    intro e
    induction e using Nat.strong_induction_on with
    | _ e ih =>
      intro he
      rcases Nat.eq_zero_or_pos e with rfl | h0
      · exact Or.inl (by rw [hw0, one_mul, mul_one])
      · obtain ⟨i, hil, e', he', rfl⟩ := top_bit h0 he
        have he'l : e' < 2 ^ l :=
          Nat.lt_of_lt_of_le he' (Nat.pow_le_pow_right (by omega) (by omega))
        rw [hstep i (by omega) e' he']
        rcases ih e' (by have := Nat.two_pow_pos i; omega) he'l with h1 | h1 <;>
          rcases hz i hil with h2 | h2
        · exact Or.inl (by rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc])
        · exact Or.inr (by rw [mul_assoc, h2, mul_neg, ← mul_assoc, h1, mul_assoc])
        · exact Or.inr (by rw [mul_assoc, h2, ← mul_assoc, h1, neg_mul, mul_assoc])
        · exact Or.inl (by rw [mul_assoc, h2, mul_neg, ← mul_assoc, h1, neg_mul, neg_neg, mul_assoc])
  rintro x ⟨e, he, rfl | rfl⟩
  · exact key e he
  · rcases key e he with h | h
    · exact Or.inl (by rw [neg_mul, mul_neg, h])
    · exact Or.inr (by rw [neg_mul, mul_neg, h])

theorem Cpm_symm {x y : R} (h : Cpm x y) : Cpm y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

theorem S_comm (hw0 : w 0 = 1) (hstep : ∀ j < m, ∀ e < 2 ^ j, w (e + 2 ^ j) = w e * a j)
    {l : ℕ} (hl : l ≤ m) (hgen : ∀ i < l, ∀ i' < l, Cpm (a i) (a i')) :
    ∀ x ∈ Spm w l, ∀ y ∈ Spm w l, Cpm x y := by
  intro x hx y hy
  refine Cpm_of_gens hw0 hstep hl (fun i hi => ?_) x hx
  exact Cpm_symm (Cpm_of_gens hw0 hstep hl (fun i' hi' => Cpm_symm (hgen i hi i' hi')) y hy)

theorem S_normal (hw0 : w 0 = 1) (hstep : ∀ j < m, ∀ e < 2 ^ j, w (e + 2 ^ j) = w e * a j)
    {k : ℕ} (hclk : ∀ x ∈ Spm w k, ∀ y ∈ Spm w k, x * y ∈ Spm w k)
    (hab : ∀ x ∈ Spm w k, ∀ y ∈ Spm w k, Cpm x y)
    (hc : ∀ j < m, k ≤ j → ∀ i < k, ∃ y ∈ Spm w k, a i * a j = a j * y) :
    ∀ j, k ≤ j → j ≤ m → ∀ y ∈ Spm w j, ∀ x ∈ Spm w k, ∃ x' ∈ Spm w k, x * y = y * x' := by
  intro j hkj
  induction j, hkj using Nat.le_induction with
  | base =>
    intro _ y hy x hx
    rcases hab x hx y hy with h | h
    · exact ⟨x, hx, h⟩
    · exact ⟨-x, Spm_neg hx, by rw [h, mul_neg]⟩
  | succ j hkj ih =>
    intro hjm y hy x hx
    have hjm' : j < m := by omega
    rcases (Spm_succ hstep hjm').1 hy with hy | ⟨s, hs, rfl⟩
    · exact ih (by omega) y hy x hx
    · obtain ⟨x1, hx1, e1⟩ := ih (by omega) s hs x hx
      obtain ⟨x2, hx2, e2⟩ := conj_l hw0 hstep hkj hjm' hclk (hc j hjm' hkj) x1 hx1
      exact ⟨x2, hx2, by rw [← mul_assoc, e1, mul_assoc, e2, ← mul_assoc]⟩

end CFSG.KS.Asc82Syl

end
