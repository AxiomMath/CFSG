module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseCharacters

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalGeneralBase

open CFSG.Wreathed.ConditionalFourier

section Definitions

variable {A : Type*} [Group A] [Fintype A] {m : ℕ} [NeZero m]

omit [NeZero m] in
@[expose] noncomputable def baseMultiplicity (lam : ZMod m → ZMod m → A →* ℂ) (χ : A → ℂ)
    (i j : ZMod m) : ℂ :=
  (Fintype.card A : ℂ)⁻¹ * ∑ x, χ x * conj (lam i j x)

omit [Fintype A] [NeZero m] in
@[expose] noncomputable def zmodFourier (ζ : ℂ) (w : ℕ → ℂ) (j : ZMod m) : ℂ :=
  fourierTransform m ζ w j.val

omit [NeZero m] in
@[expose] noncomputable def baseColumn (lam : ZMod m → ZMod m → A →* ℂ) (χ : A → ℂ) (ζ : ℂ)
    (v : ℕ → Fin 2 → ℂ) (q₀ : ℂ) (i j : ZMod m) : ℂ :=
  baseMultiplicity lam χ 0 0 - baseMultiplicity lam χ i j +
    q₀ * (zmodFourier ζ (fun k => v k 1) i + zmodFourier ζ (fun k => v k 1) j +
      zmodFourier ζ (fun k => v k 1) (-i - j))

@[expose] noncomputable def baseColumnSum (lam : ZMod m → ZMod m → A →* ℂ) (χ : A → ℂ) (ζ : ℂ)
    (v : ℕ → Fin 2 → ℂ) (q₀ : ℂ) (l : ZMod m) : ℂ :=
  ∑ i : ZMod m, baseColumn lam χ ζ v q₀ i (l - i)

end Definitions

section Algebra

variable {m : ℕ} [NeZero m] {ζ : ℂ}

omit [NeZero m] in
theorem fourierTransform_index_zero (ζ : ℂ) (w : ℕ → ℂ) : fourierTransform m ζ w 0 = 0 := by
  simp [fourierTransform]

omit [NeZero m] in
theorem zmodFourier_zero (ζ : ℂ) (w : ℕ → ℂ) : zmodFourier ζ w (0 : ZMod m) = 0 := by
  rw [zmodFourier, ZMod.val_zero, fourierTransform_index_zero]

omit [NeZero m] in
theorem zmodFourier_natCast (ζ : ℂ) (w : ℕ → ℂ) {j : ℕ} (hj : j < m) :
    zmodFourier ζ w (j : ZMod m) = fourierTransform m ζ w j := by
  rw [zmodFourier, ZMod.val_cast_of_lt hj]

omit [NeZero m] in
theorem pow_eq_pow_of_natCast_eq (hζ : IsPrimitiveRoot ζ m) {a b : ℕ}
    (h : (a : ZMod m) = b) : ζ ^ a = ζ ^ b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.mod_add_div a m, ← Nat.mod_add_div b m, h, pow_add, pow_add, pow_mul, pow_mul,
    hζ.pow_eq_one, one_pow, one_pow]

theorem sum_zmod_pow_eq_zero (hζ : IsPrimitiveRoot ζ m) {k : ℕ} (hk : k ∈ Finset.Ico 1 m) :
    ∑ i : ZMod m, ζ ^ (k * i.val) = 0 := by
  rw [Finset.mem_Ico] at hk
  rw [sum_zmod_val (m := m) (fun n => ζ ^ (k * n)), sum_range_pow_mul hζ k,
    ite_eq_right fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)]

theorem sum_zmodFourier_mul_pow (hζ : IsPrimitiveRoot ζ m) (w : ℕ → ℂ) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 m) :
    ∑ l : ZMod m, zmodFourier ζ w l * ζ ^ ((m - k) * l.val) = w k := by
  have hk' := Finset.mem_Ico.mp hk
  change ∑ l : ZMod m, fourierTransform m ζ w l.val * ζ ^ ((m - k) * l.val) = w k
  rw [sum_zmod_val (m := m) (fun n => fourierTransform m ζ w n * ζ ^ ((m - k) * n)),
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [fourierTransform_index_zero, zero_mul, zero_add]
  rw [← fourierTransform_inversion hζ w hk'.1 hk'.2]
  exact Finset.sum_congr rfl fun n _ => mul_comm _ _

end Algebra

section Parity

variable {m : ℕ} [NeZero m]

theorem two_mul_eq_zero_iff_of_even (hm : Even m) (i : ZMod m) :
    2 * i = 0 ↔ i = 0 ∨ i = ((m / 2 : ℕ) : ZMod m) := by
  obtain ⟨M, hM⟩ := hm
  have hM2 : m / 2 = M := by omega
  rw [hM2]
  have hlt := ZMod.val_lt i
  have hm0 := NeZero.ne m
  constructor
  · intro h
    have h' : ((2 * i.val : ℕ) : ZMod m) = 0 := by
      push_cast [ZMod.natCast_zmod_val]
      exact h
    rw [ZMod.natCast_eq_zero_iff] at h'
    obtain ⟨c, hc⟩ := h'
    have hc2 : c < 2 := by
      by_contra hc2
      have := Nat.mul_le_mul_left m (not_lt.mp hc2)
      omega
    rcases Nat.lt_succ_iff.mp hc2 |>.lt_or_eq with hc1 | hc1
    · left
      have hc0 : c = 0 := by omega
      rw [hc0, mul_zero] at hc
      exact (ZMod.val_eq_zero i).mp (by omega)
    · right
      rw [hc1, mul_one] at hc
      rw [← ZMod.natCast_zmod_val i, show i.val = M by omega]
  · rintro (h | h)
    · rw [h, mul_zero]
    · have h2 : ((2 * M : ℕ) : ZMod m) = 0 := by
        rw [show 2 * M = m by omega, ZMod.natCast_self]
      rw [h]
      exact_mod_cast h2

theorem two_mul_ne_neg_of_odd (hm : Even m) {j : ℕ} (hj : Odd j) (i : ZMod m) :
    2 * i ≠ -(j : ZMod m) := by
  intro h
  have h' : ((2 * i.val + j : ℕ) : ZMod m) = 0 := by
    push_cast [ZMod.natCast_zmod_val]
    rw [h]
    ring
  rw [ZMod.natCast_eq_zero_iff] at h'
  have h2 : 2 ∣ 2 * i.val + j := (even_iff_two_dvd.mp hm).trans h'
  obtain ⟨k, hk⟩ := hj
  omega

theorem two_mul_eq_iff_of_two_mul_eq (hm : Even m) {r l : ZMod m} (hr : 2 * r = l)
    (i : ZMod m) : 2 * i = l ↔ i = r ∨ i = r + ((m / 2 : ℕ) : ZMod m) := by
  have h := two_mul_eq_zero_iff_of_even hm (i - r)
  rw [mul_sub, hr, sub_eq_zero, sub_eq_zero, sub_eq_iff_eq_add'] at h
  rw [h, add_comm r]

theorem two_dvd_sum_antidiag_sub (z : ZMod m → ZMod m → ℤ) (hz : ∀ i j, z i j = z j i)
    (l : ZMod m) :
    2 ∣ ∑ i, z i (l - i) - ∑ i ∈ Finset.univ.filter (fun i => 2 * i = l), z i i := by
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : ZMod m => 2 * i = l)
    (fun i => z i (l - i))
  have hS : ∑ i ∈ Finset.univ.filter (fun i => 2 * i = l), z i (l - i) =
      ∑ i ∈ Finset.univ.filter (fun i => 2 * i = l), z i i :=
    Finset.sum_congr rfl fun i hi => by
      have h2 := (Finset.mem_filter.mp hi).2
      rw [show l - i = i by rw [← h2]; ring]
  have hnot : ((∑ i ∈ Finset.univ.filter (fun i => ¬ 2 * i = l), z i (l - i) : ℤ) :
      ZMod 2) = 0 := by
    push_cast
    refine Finset.sum_involution (fun i _ => l - i) (fun i _ => ?_) (fun i hi _ h => ?_)
      (fun i hi => ?_) (fun i _ => sub_sub_cancel l i)
    · rw [sub_sub_cancel, hz (l - i) i]
      exact CharTwo.add_self_eq_zero _
    · have hi' := (Finset.mem_filter.mp hi).2
      exact hi' (by rw [two_mul]; nth_rewrite 1 [← h]; ring)
    · have hi' := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hi' ?_⟩
      linear_combination -h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hnot
  rw [← hsplit, hS]
  simpa using hnot

end Parity

section Rows

variable {A : Type*} [Group A] [Fintype A] {σ υ : A} {m : ℕ} [NeZero m] {ζ : ℂ}
  {lam : ZMod m → ZMod m → A →* ℂ}

theorem sum_baseMultiplicity_mul_pow (hc : Commute σ υ)
    (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤) (hσ : orderOf σ = m) (hυ : orderOf υ = m)
    (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (χ : A → ℂ) (k : ℕ) :
    ∑ i : ZMod m, ∑ j : ZMod m, baseMultiplicity lam χ i j * ζ ^ (k * (i.val + j.val)) =
      χ ((σ * υ) ^ k) := by
  have hpow : ∀ i j : ZMod m, ζ ^ (k * (i.val + j.val)) = lam i j ((σ * υ) ^ k) := by
    intro i j
    rw [map_pow, map_mul, (hlam i j).1, (hlam i j).2, ← pow_add, ← pow_mul, mul_comm]
  have hterm : ∀ i j : ZMod m, baseMultiplicity lam χ i j * ζ ^ (k * (i.val + j.val)) =
      (Fintype.card A : ℂ)⁻¹ * ∑ x, χ x * lam i j (x⁻¹ * (σ * υ) ^ k) := by
    intro i j
    rw [hpow, baseMultiplicity, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [conj_monoidHom_apply, mul_assoc, ← map_mul]
  have hcard : (Fintype.card A : ℂ) = (m : ℂ) ^ 2 := by
    exact_mod_cast card_eq_sq hc hgen hσ hυ hint hζ lam hlam
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  calc ∑ i : ZMod m, ∑ j : ZMod m, baseMultiplicity lam χ i j * ζ ^ (k * (i.val + j.val))
      = (Fintype.card A : ℂ)⁻¹ *
          ∑ x, χ x * ∑ i : ZMod m, ∑ j : ZMod m, lam i j (x⁻¹ * (σ * υ) ^ k) := by
        simp only [hterm, Finset.mul_sum]
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    _ = (Fintype.card A : ℂ)⁻¹ *
          ∑ x, χ x * (if x⁻¹ * (σ * υ) ^ k = 1 then (m : ℂ) ^ 2 else 0) := by
        simp only [sum_indices_linearCharacter hc hgen hσ hυ hint hζ lam hlam]
    _ = χ ((σ * υ) ^ k) := by
        simp only [inv_mul_eq_one, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte]
        rw [hcard]
        field_simp

theorem sum_baseColumn_mul_pow (hc : Commute σ υ)
    (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤) (hσ : orderOf σ = m) (hυ : orderOf υ = m)
    (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (χ : A → ℂ)
    (v : ℕ → Fin 2 → ℂ) (q₀ : ℂ)
    (hval : ∀ k ∈ Finset.Ico 1 m, χ ((σ * υ) ^ k) = v k 0 + (2 + m * q₀) * v k 1) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 m) :
    ∑ i : ZMod m, ∑ j : ZMod m, baseColumn lam χ ζ v q₀ i j * ζ ^ (k * (i.val + j.val)) =
      -(v k 0) - 2 * v k 1 := by
  have hgeo := sum_zmod_pow_eq_zero hζ hk
  have hsplit : ∀ i j : ZMod m, baseColumn lam χ ζ v q₀ i j * ζ ^ (k * (i.val + j.val)) =
      (baseMultiplicity lam χ 0 0 + q₀ * zmodFourier ζ (fun k => v k 1) i) *
          ζ ^ (k * i.val) * ζ ^ (k * j.val) +
        q₀ * zmodFourier ζ (fun k => v k 1) j * ζ ^ (k * j.val) * ζ ^ (k * i.val) -
        baseMultiplicity lam χ i j * ζ ^ (k * (i.val + j.val)) +
        q₀ * (zmodFourier ζ (fun k => v k 1) (-i - j) * ζ ^ (k * (i.val + j.val))) := by
    intro i j
    rw [baseColumn, mul_add k, pow_add]
    ring
  have h1 : ∑ i : ZMod m, ∑ j : ZMod m,
      (baseMultiplicity lam χ 0 0 + q₀ * zmodFourier ζ (fun k => v k 1) i) *
        ζ ^ (k * i.val) * ζ ^ (k * j.val) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [← Finset.mul_sum, hgeo, mul_zero]
  have h2 : ∑ i : ZMod m, ∑ j : ZMod m,
      q₀ * zmodFourier ζ (fun k => v k 1) j * ζ ^ (k * j.val) * ζ ^ (k * i.val) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun j _ => by rw [← Finset.mul_sum, hgeo, mul_zero]
  have hinner : ∀ i : ZMod m, ∑ j : ZMod m,
      zmodFourier ζ (fun k => v k 1) (-i - j) * ζ ^ (k * (i.val + j.val)) = v k 1 := by
    intro i
    rw [← sum_zmodFourier_mul_pow hζ (fun k => v k 1) hk]
    refine Fintype.sum_equiv (Equiv.subLeft (-i)) _ _ fun j => ?_
    rw [Equiv.subLeft_apply]
    congr 1
    apply pow_eq_pow_of_natCast_eq hζ
    have hkm := (Finset.mem_Ico.mp hk).2
    push_cast [Nat.cast_sub hkm.le, ZMod.natCast_self, ZMod.natCast_zmod_val]
    ring
  have h3 : ∑ i : ZMod m, ∑ j : ZMod m,
      q₀ * (zmodFourier ζ (fun k => v k 1) (-i - j) * ζ ^ (k * (i.val + j.val))) =
        q₀ * (m * v k 1) := by
    simp only [← Finset.mul_sum, hinner, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3, sum_baseMultiplicity_mul_pow hc hgen hσ hυ hint hζ hlam χ k, hval k hk]
  ring

theorem sum_baseColumnSum_mul_pow (hc : Commute σ υ)
    (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤) (hσ : orderOf σ = m) (hυ : orderOf υ = m)
    (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (χ : A → ℂ)
    (v : ℕ → Fin 2 → ℂ) (q₀ : ℂ)
    (hval : ∀ k ∈ Finset.Ico 1 m, χ ((σ * υ) ^ k) = v k 0 + (2 + m * q₀) * v k 1) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 m) :
    ∑ l : ZMod m, baseColumnSum lam χ ζ v q₀ l * ζ ^ (k * l.val) = -(v k 0) - 2 * v k 1 := by
  rw [← sum_baseColumn_mul_pow hc hgen hσ hυ hint hζ hlam χ v q₀ hval hk]
  simp only [baseColumnSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fintype.sum_equiv (Equiv.subRight i) _ _ fun l => ?_
  rw [Equiv.subRight_apply]
  congr 1
  apply pow_eq_pow_of_natCast_eq hζ
  push_cast [ZMod.natCast_zmod_val]
  ring

theorem second_row_identity (hc : Commute σ υ)
    (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤) (hσ : orderOf σ = m) (hυ : orderOf υ = m)
    (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (χ : A → ℂ)
    (v : ℕ → Fin 2 → ℂ) (q₀ : ℂ)
    (hval : ∀ k ∈ Finset.Ico 1 m, χ ((σ * υ) ^ k) = v k 0 + (2 + m * q₀) * v k 1)
    (j : ZMod m) :
    zmodFourier ζ (fun k => v k 0) j + 2 * zmodFourier ζ (fun k => v k 1) j =
      baseColumnSum lam χ ζ v q₀ 0 - baseColumnSum lam χ ζ v q₀ (-j) := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hm1 : 1 ≤ m := NeZero.one_le
  have hR : (m : ℂ)⁻¹ * ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j.val * k) - 1) *
      ∑ l : ZMod m, baseColumnSum lam χ ζ v q₀ l * ζ ^ (k * l.val) =
        -zmodFourier ζ (fun k => v k 0) j - 2 * zmodFourier ζ (fun k => v k 1) j := by
    have h : ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j.val * k) - 1) *
        ∑ l : ZMod m, baseColumnSum lam χ ζ v q₀ l * ζ ^ (k * l.val) =
          ∑ k ∈ Finset.Ico 1 m, (-((ζ ^ (j.val * k) - 1) * v k 0) -
            2 * ((ζ ^ (j.val * k) - 1) * v k 1)) :=
      Finset.sum_congr rfl fun k hk => by
        rw [sum_baseColumnSum_mul_pow hc hgen hσ hυ hint hζ hlam χ v q₀ hval hk]
        ring
    rw [h, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    simp only [zmodFourier, fourierTransform]
    ring
  have hdiv1 : ∀ l : ZMod m, (m ∣ j.val + l.val ↔ l = -j) := by
    intro l
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [ZMod.natCast_zmod_val]
    constructor <;> intro h <;> linear_combination h
  have hdiv2 : ∀ l : ZMod m, (m ∣ l.val ↔ l = 0) := by
    intro l
    rw [← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]
  have hL : (m : ℂ)⁻¹ * ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j.val * k) - 1) *
      ∑ l : ZMod m, baseColumnSum lam χ ζ v q₀ l * ζ ^ (k * l.val) =
        baseColumnSum lam χ ζ v q₀ (-j) - baseColumnSum lam χ ζ v q₀ 0 := by
    have h : ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j.val * k) - 1) *
        ∑ l : ZMod m, baseColumnSum lam χ ζ v q₀ l * ζ ^ (k * l.val) =
          ∑ l : ZMod m, baseColumnSum lam χ ζ v q₀ l *
            (∑ k ∈ Finset.Ico 1 m, ζ ^ ((j.val + l.val) * k) -
              ∑ k ∈ Finset.Ico 1 m, ζ ^ (l.val * k)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [add_mul, pow_add, mul_comm k l.val]
      ring
    have hS : ∀ l : ZMod m, ∑ k ∈ Finset.Ico 1 m, ζ ^ ((j.val + l.val) * k) -
        ∑ k ∈ Finset.Ico 1 m, ζ ^ (l.val * k) =
          (if l = -j then (m : ℂ) else 0) - (if l = 0 then (m : ℂ) else 0) := by
      intro l
      rw [sum_Ico_pow_mul hζ hm1, sum_Ico_pow_mul hζ hm1]
      simp only [hdiv1 l, hdiv2 l]
      ring
    rw [h, Finset.sum_congr rfl fun l _ => by rw [hS l]]
    simp only [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    field_simp
  have hEq := hL.symm.trans hR
  linear_combination hEq

theorem second_row_reconstruction (hc : Commute σ υ)
    (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤) (hσ : orderOf σ = m) (hυ : orderOf υ = m)
    (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (χ : A → ℂ)
    (v : ℕ → Fin 2 → ℂ) (q₀ : ℂ)
    (hval : ∀ k ∈ Finset.Ico 1 m, χ ((σ * υ) ^ k) = v k 0 + (2 + m * q₀) * v k 1) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 m) :
    v k 1 = (1 / 2) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
      (baseColumnSum lam χ ζ v q₀ 0 - baseColumnSum lam χ ζ v q₀ (-(j : ZMod m)) -
        zmodFourier ζ (fun k => v k 0) (j : ZMod m)) := by
  have hk' := Finset.mem_Ico.mp hk
  have hm1 : 1 ≤ m := NeZero.one_le
  have hterm : ∀ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
      (baseColumnSum lam χ ζ v q₀ 0 - baseColumnSum lam χ ζ v q₀ (-(j : ZMod m)) -
        zmodFourier ζ (fun k => v k 0) (j : ZMod m)) =
          2 * (ζ ^ ((m - k) * j) * fourierTransform m ζ (fun k => v k 1) j) := by
    intro j hj
    rw [← second_row_identity hc hgen hσ hυ hint hζ hlam χ v q₀ hval (j : ZMod m),
      zmodFourier_natCast ζ (fun k => v k 1) (Finset.mem_Ico.mp hj).2,
      zpow_neg_mul_eq_pow hm1 hζ.pow_eq_one hk'.2.le]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    fourierTransform_inversion hζ (fun k => v k 1) hk'.1 hk'.2]
  ring

theorem two_mul_row_value (hc : Commute σ υ)
    (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤) (hσ : orderOf σ = m) (hυ : orderOf υ = m)
    (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (χ : A → ℂ)
    (v : ℕ → Fin 2 → ℂ) (q₀ : ℂ)
    (hval : ∀ k ∈ Finset.Ico 1 m, χ ((σ * υ) ^ k) = v k 0 + (2 + m * q₀) * v k 1) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 m) (φ w : ℂ) (hw : w = v k 0 + v k 1 * (1 + φ)) :
    2 * w = (1 - φ) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
        zmodFourier ζ (fun k => v k 0) (j : ZMod m) +
      (1 + φ) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
        (baseColumnSum lam χ ζ v q₀ 0 - baseColumnSum lam χ ζ v q₀ (-(j : ZMod m))) := by
  have hk' := Finset.mem_Ico.mp hk
  have hm1 : 1 ≤ m := NeZero.one_le
  have h1 := second_row_reconstruction hc hgen hσ hυ hint hζ hlam χ v q₀ hval hk
  have h0 : v k 0 = ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
      zmodFourier ζ (fun k => v k 0) (j : ZMod m) := by
    rw [← fourierTransform_inversion hζ (fun k => v k 0) hk'.1 hk'.2]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [zmodFourier_natCast ζ (fun k => v k 0) (Finset.mem_Ico.mp hj).2,
      zpow_neg_mul_eq_pow hm1 hζ.pow_eq_one hk'.2.le]
  have hsplit : ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
      (baseColumnSum lam χ ζ v q₀ 0 - baseColumnSum lam χ ζ v q₀ (-(j : ZMod m)) -
        zmodFourier ζ (fun k => v k 0) (j : ZMod m)) =
      ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
          (baseColumnSum lam χ ζ v q₀ 0 - baseColumnSum lam χ ζ v q₀ (-(j : ZMod m))) -
        ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
          zmodFourier ζ (fun k => v k 0) (j : ZMod m) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit] at h1
  rw [hw, h1, h0]
  ring

theorem base_column_parity (hc : Commute σ υ)
    (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤) (hσ : orderOf σ = m) (hυ : orderOf υ = m)
    (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (χ : A → ℂ)
    (v : ℕ → Fin 2 → ℂ) (q₀ : ℂ)
    (hval : ∀ k ∈ Finset.Ico 1 m, χ ((σ * υ) ^ k) = v k 0 + (2 + m * q₀) * v k 1)
    (hm : Even m) (hcint : ∀ i j, ∃ z : ℤ, baseColumn lam χ ζ v q₀ i j = z)
    (hcsym : ∀ i j, baseColumn lam χ ζ v q₀ i j = baseColumn lam χ ζ v q₀ j i)
    (hFint : ∀ j : ZMod m, ∃ z : ℤ, zmodFourier ζ (fun k => v k 1) j = z)
    (hXint : ∀ j : ZMod m, ∃ z : ℤ, zmodFourier ζ (fun k => v k 0) j = z) :
    (∀ j ∈ Finset.Ico 1 m, Odd j → ∃ k : ℤ, zmodFourier ζ (fun k => v k 0) (j : ZMod m) -
        baseColumn lam χ ζ v q₀ ((m / 2 : ℕ) : ZMod m) ((m / 2 : ℕ) : ZMod m) = 2 * k) ∧
    ∀ j ∈ Finset.Ico 1 m, Even j → ∀ r : ZMod m, 2 * r = -(j : ZMod m) →
      ∃ k : ℤ, zmodFourier ζ (fun k => v k 0) (j : ZMod m) -
        (baseColumn lam χ ζ v q₀ ((m / 2 : ℕ) : ZMod m) ((m / 2 : ℕ) : ZMod m) +
          baseColumn lam χ ζ v q₀ r r +
          baseColumn lam χ ζ v q₀ (r + ((m / 2 : ℕ) : ZMod m)) (r + ((m / 2 : ℕ) : ZMod m))) =
            2 * k := by
  set M : ZMod m := ((m / 2 : ℕ) : ZMod m) with hMdef
  choose z hzc using hcint
  have hzsym : ∀ i j, z i j = z j i := fun i j => by
    have h := hcsym i j
    rw [hzc, hzc] at h
    exact_mod_cast h
  have hz00 : z 0 0 = 0 := by
    have h : baseColumn lam χ ζ v q₀ 0 0 = 0 := by
      rw [baseColumn, neg_zero, zero_sub, neg_zero, zmodFourier_zero]
      ring
    rw [hzc] at h
    exact_mod_cast h
  have hM0 : M ≠ 0 := by
    obtain ⟨M', hM'⟩ := hm
    have hm0 := NeZero.ne m
    intro h
    have h' := (two_mul_eq_zero_iff_of_even ⟨M', hM'⟩ M).mpr (Or.inr rfl)
    rw [hMdef, ← ZMod.val_eq_zero, ZMod.val_cast_of_lt (by omega)] at h
    omega
  have hCl : ∀ l, baseColumnSum lam χ ζ v q₀ l = ((∑ i, z i (l - i) : ℤ) : ℂ) := by
    intro l
    rw [baseColumnSum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hzc i (l - i)
  have hfilter0 : Finset.univ.filter (fun i : ZMod m => 2 * i = 0) = {0, M} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact two_mul_eq_zero_iff_of_even hm i
  have hC0 : 2 ∣ ∑ i, z i (0 - i) - z M M := by
    have h := two_dvd_sum_antidiag_sub z hzsym 0
    rwa [hfilter0, Finset.sum_pair (Ne.symm hM0), hz00, zero_add] at h
  have hrow : ∀ j : ZMod m, ∃ x f : ℤ, zmodFourier ζ (fun k => v k 0) j = x ∧
      x + 2 * f = ∑ i, z i (0 - i) - ∑ i, z i (-j - i) := by
    intro j
    obtain ⟨x, hx⟩ := hXint j
    obtain ⟨f, hf⟩ := hFint j
    refine ⟨x, f, hx, ?_⟩
    have h := second_row_identity hc hgen hσ hυ hint hζ hlam χ v q₀ hval j
    rw [hx, hf, hCl, hCl] at h
    exact_mod_cast h
  refine ⟨fun j hj hjo => ?_, fun j hj hje r hr => ?_⟩
  · obtain ⟨x, f, hx, hxf⟩ := hrow (j : ZMod m)
    have hfilter : Finset.univ.filter (fun i : ZMod m => 2 * i = -(j : ZMod m)) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact two_mul_ne_neg_of_odd hm hjo i
    have hCj := two_dvd_sum_antidiag_sub z hzsym (-(j : ZMod m))
    rw [hfilter, Finset.sum_empty, sub_zero] at hCj
    obtain ⟨k, hk⟩ : 2 ∣ x - z M M := by
      have : x - z M M = (∑ i, z i (0 - i) - z M M) - ∑ i, z i (-(j : ZMod m) - i) - 2 * f := by
        linarith
      rw [this]
      exact dvd_sub (dvd_sub hC0 hCj) (dvd_mul_right 2 f)
    refine ⟨k, ?_⟩
    rw [hx, hzc]
    exact_mod_cast hk
  · obtain ⟨x, f, hx, hxf⟩ := hrow (j : ZMod m)
    have hrM : r ≠ r + M := fun h => hM0 (by linear_combination -h)
    have hfilter : Finset.univ.filter (fun i : ZMod m => 2 * i = -(j : ZMod m)) = {r, r + M} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact two_mul_eq_iff_of_two_mul_eq hm hr i
    have hCj := two_dvd_sum_antidiag_sub z hzsym (-(j : ZMod m))
    rw [hfilter, Finset.sum_pair hrM] at hCj
    obtain ⟨k, hk⟩ : 2 ∣ x - (z M M + z r r + z (r + M) (r + M)) := by
      have : x - (z M M + z r r + z (r + M) (r + M)) = (∑ i, z i (0 - i) - z M M) -
          (∑ i, z i (-(j : ZMod m) - i) - (z r r + z (r + M) (r + M))) - 2 * f -
            2 * (z r r + z (r + M) (r + M)) := by
        linarith
      rw [this]
      exact dvd_sub (dvd_sub (dvd_sub hC0 hCj) (dvd_mul_right 2 f)) (dvd_mul_right 2 _)
    refine ⟨k, ?_⟩
    rw [hx, hzc, hzc, hzc]
    exact_mod_cast hk

end Rows

end CFSG.Wreathed.ConditionalGeneralBase
