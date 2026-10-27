module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneTableColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.ColumnRigidity

public section

open Finset

namespace CFSG.Semidihedral.FieldFactorOne

namespace TableCoordinates

variable {L : Type*} [DecidableEq L]

theorem sum_ite_eq_zero_of_forall_ne {R : Type*} [CommRing R] {I : Finset ℕ} {ψ : ℕ → L}
    {x : L} (h : ∀ l ∈ I, x ≠ ψ l) : ∑ l ∈ I, (if x = ψ l then (1 : R) else 0) = 0 :=
  Finset.sum_eq_zero fun l hl => by simp [h l hl]

theorem sum_ite_eq_one_of_injOn {R : Type*} [CommRing R] {I : Finset ℕ} {ψ : ℕ → L}
    (hinj : Set.InjOn ψ (I : Set ℕ)) {m : ℕ} (hm : m ∈ I) :
    ∑ l ∈ I, (if ψ m = ψ l then (1 : R) else 0) = 1 := by
  rw [Finset.sum_eq_single_of_mem m hm fun l hl hlm =>
    ite_eq_right fun e => hlm (hinj hl hm e.symm)]
  simp

theorem sum_mul_sum_ite {R : Type*} [CommRing R] {B : Finset L} (X : L → R) {I : Finset ℕ}
    {ψ : ℕ → L} (hψ : ∀ l ∈ I, ψ l ∈ B) :
    ∑ x ∈ B, X x * ∑ l ∈ I, (if x = ψ l then (1 : R) else 0) = ∑ l ∈ I, X (ψ l) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l hl => by simp [hψ l hl]

theorem sum_mul_formΘ {R : Type*} [CommRing R] {B : Finset L} (X : L → R) {c₀ c₁ c₂ c₃ : L}
    (h₀ : c₀ ∈ B) (h₁ : c₁ ∈ B) (h₂ : c₂ ∈ B) (h₃ : c₃ ∈ B) (a₀ a₁ a₂ a₃ : R) :
    ∑ x ∈ B, X x * (a₀ * (if x = c₀ then 1 else 0) + a₁ * (if x = c₁ then 1 else 0) +
      a₂ * (if x = c₂ then 1 else 0) + a₃ * (if x = c₃ then 1 else 0)) =
      a₀ * X c₀ + a₁ * X c₁ + a₂ * X c₂ + a₃ * X c₃ := by
  simp [mul_add, Finset.sum_add_distrib, h₀, h₁, h₂, h₃]
  ring

theorem sum_mul_formU {R : Type*} [CommRing R] {B : Finset L} (X : L → R)
    {c₀ c₁ c₂ c₃ c₄ : L} (h₀ : c₀ ∈ B) (h₁ : c₁ ∈ B) (h₂ : c₂ ∈ B) (h₃ : c₃ ∈ B) (h₄ : c₄ ∈ B)
    (a₀ a₁ a₂ a₃ a₄ : R) :
    ∑ x ∈ B, X x * (a₀ * (if x = c₀ then 1 else 0) - a₁ * (if x = c₁ then 1 else 0) +
      a₂ * (if x = c₂ then 1 else 0) - a₃ * (if x = c₃ then 1 else 0) +
      2 * a₄ * (if x = c₄ then 1 else 0)) =
      a₀ * X c₀ - a₁ * X c₁ + a₂ * X c₂ - a₃ * X c₃ + 2 * a₄ * X c₄ := by
  simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, h₀, h₁, h₂, h₃, h₄]
  ring

theorem sum_mul_formE {R : Type*} [CommRing R] {B : Finset L} (X : L → R) {c₀ c₁ p : L}
    (h₀ : c₀ ∈ B) (h₁ : c₁ ∈ B) (hp : p ∈ B) (a₀ a₁ a : R) :
    ∑ x ∈ B, X x * (a₀ * (if x = c₀ then 1 else 0) + a₁ * (if x = c₁ then 1 else 0) -
      a * (if x = p then 1 else 0)) = a₀ * X c₀ + a₁ * X c₁ - a * X p := by
  simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, h₀, h₁, hp]
  ring

theorem sum_mul_formF {R : Type*} [CommRing R] {B : Finset L} (X : L → R) {y z : L}
    (hy : y ∈ B) (hz : z ∈ B) (a : R) :
    ∑ x ∈ B, X x * (a * ((if x = y then 1 else 0) - (if x = z then 1 else 0))) =
      a * (X y - X z) := by
  simp [mul_sub, Finset.sum_sub_distrib, hy, hz]
  ring

theorem sum_mul_formV {R : Type*} [CommRing R] {B : Finset L} (X : L → R) {c₁ c₂ c₄ : L}
    (h₁ : c₁ ∈ B) (h₂ : c₂ ∈ B) (h₄ : c₄ ∈ B) {I J : Finset ℕ} {ψ ν : ℕ → L}
    (hψ : ∀ l ∈ I, ψ l ∈ B) (hν : ∀ i ∈ J, ν i ∈ B) (a₁ a₂ a₄ aψ aν : R) :
    ∑ x ∈ B, X x * (a₁ * (if x = c₁ then 1 else 0) - a₂ * (if x = c₂ then 1 else 0) -
      a₄ * (if x = c₄ then 1 else 0) + aψ * ∑ l ∈ I, (if x = ψ l then 1 else 0) -
      aν * ∑ i ∈ J, (if x = ν i then 1 else 0)) =
      a₁ * X c₁ - a₂ * X c₂ - a₄ * X c₄ + aψ * ∑ l ∈ I, X (ψ l) - aν * ∑ i ∈ J, X (ν i) := by
  have eψ := sum_mul_sum_ite X hψ
  have eν := sum_mul_sum_ite X hν
  have e : ∀ x ∈ B, X x * (a₁ * (if x = c₁ then 1 else 0) - a₂ * (if x = c₂ then 1 else 0) -
      a₄ * (if x = c₄ then 1 else 0) + aψ * ∑ l ∈ I, (if x = ψ l then 1 else 0) -
      aν * ∑ i ∈ J, (if x = ν i then 1 else 0)) =
      a₁ * (X x * (if x = c₁ then 1 else 0)) - a₂ * (X x * (if x = c₂ then 1 else 0)) -
      a₄ * (X x * (if x = c₄ then 1 else 0)) +
      aψ * (X x * ∑ l ∈ I, (if x = ψ l then 1 else 0)) -
      aν * (X x * ∑ i ∈ J, (if x = ν i then 1 else 0)) := fun x _ => by ring
  rw [Finset.sum_congr rfl e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, eψ, eν]
  simp [h₁, h₂, h₄]

theorem orth_relations {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {k : ℕ} (hk : 2 ≤ k)
    {δ₀ δ₁ δ₂ δ₃ δ₄ δ δF aν : R} (hδF : δF ≠ 0) {X₀ X₁ X₂ X₃ X₄ : R} {Xψ Xν : ℕ → R}
    (eΘ : δ₀ * X₀ + δ₁ * X₁ + δ₂ * X₂ + δ₃ * X₃ = 0)
    (eE : ∀ l ∈ Icc 1 (k - 1), δ₀ * X₀ + δ₁ * X₁ - δ * Xψ l = 0)
    (eF : ∀ j ∈ Icc 1 (k - 1), δF * (Xν j - Xν 0) = 0)
    (eU : δ₀ * X₀ - δ₁ * X₁ + δ₂ * X₂ - δ₃ * X₃ + 2 * δ₄ * X₄ = 0)
    (eV : δ₁ * X₁ - δ₂ * X₂ - δ₄ * X₄ + δ * ∑ l ∈ Icc 1 (k - 1), Xψ l -
      aν * ∑ i ∈ range k, Xν i = 0) :
    δ₀ * X₀ + δ₁ * X₁ + δ₂ * X₂ + δ₃ * X₃ = 0 ∧
      (∀ l ∈ Icc 1 (k - 1), δ * Xψ l = δ₀ * X₀ + δ₁ * X₁) ∧
      (∀ i ∈ range k, aν * Xν i = δ₀ * X₀ + δ₁ * X₁) ∧
      δ₀ * X₀ + δ₂ * X₂ + δ₄ * X₄ = 0 := by
  have h16 : δ₀ * X₀ + δ₂ * X₂ + δ₄ * X₄ = 0 := by
    have e : (2 : R) * (δ₀ * X₀ + δ₂ * X₂ + δ₄ * X₄) = 0 := by linear_combination eΘ + eU
    exact (mul_eq_zero.mp e).resolve_left two_ne_zero
  have h14 : ∀ l ∈ Icc 1 (k - 1), δ * Xψ l = δ₀ * X₀ + δ₁ * X₁ := fun l hl => by
    linear_combination -eE l hl
  have hν : ∀ i ∈ range k, Xν i = Xν 0 := by
    intro i hi
    by_cases hi0 : i = 0
    · rw [hi0]
    have hiI : i ∈ Icc 1 (k - 1) := by
      rw [Finset.mem_range] at hi
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact sub_eq_zero.mp ((mul_eq_zero.mp (eF i hiI)).resolve_left hδF)
  have hsumψ : δ * ∑ l ∈ Icc 1 (k - 1), Xψ l = ((k : R) - 1) * (δ₀ * X₀ + δ₁ * X₁) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl h14, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
      Nat.add_sub_cancel, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hsumν : ∑ i ∈ range k, Xν i = (k : R) * Xν 0 := by
    rw [Finset.sum_congr rfl hν, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsumψ, hsumν] at eV
  have hk0 : (k : R) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (k : R) * (δ₀ * X₀ + δ₁ * X₁ - aν * Xν 0) = 0 := by
    linear_combination eV + h16
  have h17 : aν * Xν 0 = δ₀ * X₀ + δ₁ * X₁ := by
    have := (mul_eq_zero.mp key).resolve_left hk0
    linear_combination -this
  exact ⟨eΘ, h14, fun i hi => by rw [hν i hi, h17], h16⟩

section Families

variable {k : ℕ} {B : Finset L} {E F : ℕ → L → ℤ} {c₀ c₁ c₂ c₃ c₄ : L} {δ₀ δ₁ δ δF : ℤ}
  {ψ ν : ℕ → L}

theorem ESystem.apply_eq_zero (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ) {x : L}
    (hx : x ∈ B) (h0 : x ≠ c₀) (h1 : x ≠ c₁) (hψ : ∀ l ∈ Icc 1 (k - 1), x ≠ ψ l) :
    ∀ l ∈ Icc 1 (k - 1), E l x = 0 := fun l hl => by
  rw [S.hE l hl x hx]
  simp [h0, h1, hψ l hl]

theorem ESystem.apply_c₁ (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ) (h₁ : c₁ ∈ B)
    (h01 : c₀ ≠ c₁) : ∀ l ∈ Icc 1 (k - 1), E l c₁ = δ₁ := fun l hl => by
  obtain ⟨-, -, hψ1, -⟩ := mem_sdiff_five.mp (S.hψ l hl)
  rw [S.hE l hl c₁ h₁]
  simp [h01.symm, hψ1.symm]

theorem ESystem.apply_ψ (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ) {m : ℕ}
    (hm : m ∈ Icc 1 (k - 1)) : ∀ l ∈ Icc 1 (k - 1), E l (ψ m) = -δ * (if ψ m = ψ l then 1 else 0) :=
  fun l hl => by
    obtain ⟨hB, h0, h1, -⟩ := mem_sdiff_five.mp (S.hψ m hm)
    rw [S.hE l hl _ hB]
    simp only [h0, h1, ↓reduceIte]
    ring

theorem FSystem.sum_mul_F (T : FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ ν δF) (hk : 2 ≤ k) {j : ℕ}
    (hj : j ∈ Icc 1 (k - 1)) (f : L → ℤ) :
    ∑ x ∈ B, f x * F j x = δF * (f (ν j) - f (ν 0)) := by
  have hjr : j ∈ range k := by
    rw [Finset.mem_Icc] at hj
    exact Finset.mem_range.mpr (by omega)
  have h0r : 0 ∈ range k := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_congr rfl fun x hx => by rw [T.hF j hj x hx]]
  exact sum_mul_formF f (Finset.mem_sdiff.mp (T.hν j hjr)).1 (Finset.mem_sdiff.mp (T.hν 0 h0r)).1 δF

theorem FSystem.apply_eq_zero (T : FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ ν δF) (hk : 2 ≤ k) {x : L}
    (hx : x ∈ B) (hν : ∀ i ∈ range k, x ≠ ν i) : ∀ j ∈ Icc 1 (k - 1), F j x = 0 := by
  intro j hj
  have hjr : j ∈ range k := by
    rw [Finset.mem_Icc] at hj
    exact Finset.mem_range.mpr (by omega)
  rw [T.hF j hj x hx]
  simp [hν j hjr, hν 0 (Finset.mem_range.mpr (by omega))]

end Families

theorem odd_of_dvd {k : ℕ} (hk : Even k) {v c : ℤ} (h : (2 * k : ℤ) ∣ 2 * v + 2 * c)
    (hc : c = 1 ∨ c = -1) : Odd v := by
  obtain ⟨m, hm⟩ := hk
  have h4 : (4 : ℤ) ∣ 2 * v + 2 * c :=
    dvd_trans ⟨m, by rw [hm]; push_cast; ring⟩ h
  rw [Int.odd_iff]
  rcases hc with rfl | rfl <;> omega


section StageV

variable {k : ℕ} {B : Finset L} {deg Θ : L → ℤ} {E F : ℕ → L → ℤ} {U V : L → ℤ}
  {c₀ c₁ c₂ c₃ c₄ : L} {δ₀ δ₁ δ₂ δ₃ δ₄ δ δF : ℤ} {ψ ν : ℕ → L}

omit [DecidableEq L] in
theorem injOn_Icc_of_range {ν : ℕ → L} (h : Set.InjOn ν (range k : Set ℕ)) :
    Set.InjOn ν (Icc 1 (k - 1) : Set ℕ) :=
  h.mono fun i hi => by
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.coe_range, Set.mem_Iio] at hi ⊢
    omega

theorem Hyp.cong_points (h : Hyp k B deg Θ E F U V)
    (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ)
    (T : FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ ν δF) :
    (2 * k : ℤ) ∣ 2 * V c₁ + 2 * (-δ₁) ∧ (2 * k : ℤ) ∣ 2 * V c₂ + 2 * δ₂ ∧
      (2 * k : ℤ) ∣ 2 * V c₄ + 2 * δ₄ ∧ (2 * k : ℤ) ∣ 2 * V (ψ 1) + 2 * (-δ) ∧
      (2 * k : ℤ) ∣ 2 * V (ν 1) + 2 * δF := by
  have hk := h.hk
  have hI1 := h.one_mem
  have h1r : 1 ∈ range k := Finset.mem_range.mpr (by omega)
  have h0r : 0 ∈ range k := Finset.mem_range.mpr (by omega)
  obtain ⟨-, hΘ₁, hΘ₂, -, hΘ₄⟩ := A.Θ_values
  obtain ⟨-, hU₁, hU₂, -, hU₄⟩ := A.U_values
  have hνC : ∀ i ∈ range k, ν i ≠ c₀ ∧ ν i ≠ c₁ ∧ ν i ≠ c₂ ∧ ν i ≠ c₃ ∧ ν i ≠ c₄ :=
    fun i hi => (mem_sdiff_five.mp (T.hν i hi)).2
  have hψC : ∀ l ∈ Icc 1 (k - 1), ψ l ≠ c₀ ∧ ψ l ≠ c₁ ∧ ψ l ≠ c₂ ∧ ψ l ≠ c₃ ∧ ψ l ≠ c₄ :=
    fun l hl => (mem_sdiff_five.mp (S.hψ l hl)).2
  have hψB : ψ 1 ∈ B := (Finset.mem_sdiff.mp (S.hψ 1 hI1)).1
  have hνB : ν 1 ∈ B := (Finset.mem_sdiff.mp (T.hν 1 h1r)).1
  have hFsum0 : ∀ x ∈ B, (∀ i ∈ range k, x ≠ ν i) → ∑ j ∈ Icc 1 (k - 1), F j x = 0 :=
    fun x hx hν => Finset.sum_eq_zero (T.apply_eq_zero hk hx hν)
  have hEsum0 : ∀ x ∈ B, x ≠ c₀ → x ≠ c₁ → (∀ l ∈ Icc 1 (k - 1), x ≠ ψ l) →
      ∑ l ∈ Icc 1 (k - 1), E l x = 0 :=
    fun x hx h0 h1 hψ => Finset.sum_eq_zero (S.apply_eq_zero hx h0 h1 hψ)
  have hEsum1 : ∑ l ∈ Icc 1 (k - 1), E l c₁ = ((k : ℤ) - 1) * δ₁ := by
    rw [Finset.sum_congr rfl (S.apply_c₁ A.h₁ A.n01), Finset.sum_const, Nat.card_Icc,
      nsmul_eq_mul, Nat.add_sub_cancel, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hEsumψ : ∑ l ∈ Icc 1 (k - 1), E l (ψ 1) = -δ := by
    rw [Finset.sum_congr rfl (S.apply_ψ hI1), ← Finset.mul_sum,
      sum_ite_eq_one_of_injOn S.inj hI1, mul_one]
  have hFsumν : ∑ j ∈ Icc 1 (k - 1), F j (ν 1) = δF := by
    have h10 : ν 1 ≠ ν 0 := fun e => absurd (T.inj h1r h0r e) one_ne_zero
    rw [Finset.sum_congr rfl fun j hj => T.hF j hj _ hνB]
    simp only [h10, ↓reduceIte, sub_zero]
    rw [← Finset.mul_sum, sum_ite_eq_one_of_injOn (injOn_Icc_of_range T.inj) hI1, mul_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have c := h.hcong c₁ A.h₁
    rw [hU₁, hΘ₁, hEsum1, hFsum0 c₁ A.h₁ fun i hi => (hνC i hi).2.1.symm] at c
    have e : (2 * k : ℤ) ∣ 2 * k * δ₁ := dvd_mul_right _ _
    convert dvd_sub c e using 1
    ring
  · have c := h.hcong c₂ A.h₂
    rw [hU₂, hΘ₂, hEsum0 c₂ A.h₂ A.n02.symm A.n12.symm fun l hl => (hψC l hl).2.2.1.symm,
      hFsum0 c₂ A.h₂ fun i hi => (hνC i hi).2.2.1.symm] at c
    convert c using 1
    ring
  · have c := h.hcong c₄ A.h₄
    rw [hU₄, hΘ₄, hEsum0 c₄ A.h₄ A.n04.symm A.n14.symm fun l hl => (hψC l hl).2.2.2.2.symm,
      hFsum0 c₄ A.h₄ fun i hi => (hνC i hi).2.2.2.2.symm] at c
    convert c using 1
    ring
  · have c := h.hcong (ψ 1) hψB
    obtain ⟨hΘψ, hUψ⟩ := A.vanish (S.hψ 1 hI1)
    rw [hUψ, hΘψ, hEsumψ, hFsum0 _ hψB fun i hi => (T.νψ i hi 1 hI1).symm] at c
    convert c using 1
    ring
  · have c := h.hcong (ν 1) hνB
    obtain ⟨hΘν, hUν⟩ := A.vanish (T.hν 1 h1r)
    rw [hUν, hΘν, hFsumν, hEsum0 _ hνB (hνC 1 h1r).1 (hνC 1 h1r).2.1 fun l hl =>
      T.νψ 1 h1r l hl] at c
    convert c using 1
    ring

theorem Hyp.V_values (h : Hyp k B deg Θ E F U V)
    (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ)
    (T : FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ ν δF) :
    V c₁ = δ₁ ∧ V c₂ = -δ₂ ∧ V c₄ = -δ₄ ∧ (∀ l ∈ Icc 1 (k - 1), V (ψ l) = δ) ∧
      (∀ i ∈ range k, V (ν i) = V (ν 0)) ∧ (V (ν 0) = 1 ∨ V (ν 0) = -1) ∧
      ∀ x ∈ B, x ≠ c₁ → x ≠ c₂ → x ≠ c₄ → (∀ l ∈ Icc 1 (k - 1), x ≠ ψ l) →
        (∀ i ∈ range k, x ≠ ν i) → V x = 0 := by
  have hk := h.hk
  have hI1 := h.one_mem
  have h1r : 1 ∈ range k := Finset.mem_range.mpr (by omega)
  have h0r : 0 ∈ range k := Finset.mem_range.mpr (by omega)
  obtain ⟨cg₁, cg₂, cg₄, cgψ, cgν⟩ := h.cong_points A S T
  have neg_sign : ∀ {σ : ℤ}, (σ = 1 ∨ σ = -1) → (-σ = 1 ∨ -σ = -1) := fun hσ => by
    rcases hσ with rfl | rfl <;> norm_num
  have hodd₁ := odd_of_dvd h.heven cg₁ (neg_sign A.s₁)
  have hodd₂ := odd_of_dvd h.heven cg₂ A.s₂
  have hodd₄ := odd_of_dvd h.heven cg₄ A.s₄
  have hoddψ := odd_of_dvd h.heven cgψ (neg_sign S.hδ)
  have hoddν := odd_of_dvd h.heven cgν T.hδF
  have hVE : ∀ l ∈ Icc 1 (k - 1), δ * V (ψ l) = δ₀ * V c₀ + δ₁ * V c₁ := fun l hl => by
    have e := h.hVE l hl
    rw [S.sum_mul_E A.h₀ A.h₁ hl] at e
    linear_combination -e
  have hVψ : ∀ l ∈ Icc 1 (k - 1), V (ψ l) = V (ψ 1) := fun l hl =>
    mul_left_cancel₀ (sign_ne_zero S.hδ) ((hVE l hl).trans (hVE 1 hI1).symm)
  have hVν : ∀ i ∈ range k, V (ν i) = V (ν 0) := by
    intro i hi
    by_cases hi0 : i = 0
    · rw [hi0]
    have hiI : i ∈ Icc 1 (k - 1) := by
      rw [Finset.mem_range] at hi
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have e := h.hVF i hiI
    rw [T.sum_mul_F hk hiI] at e
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (sign_ne_zero T.hδF))
  set D : Finset L := insert c₁ (insert c₂ (insert c₄ ((Icc 1 (k - 1)).image ψ ∪
    (range k).image ν))) with hD
  have hmemD : ∀ y, y ∈ D ↔ y = c₁ ∨ y = c₂ ∨ y = c₄ ∨ (∃ l ∈ Icc 1 (k - 1), ψ l = y) ∨
      ∃ i ∈ range k, ν i = y := by
    intro y
    simp only [hD, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  have hDB : D ⊆ B := by
    intro y hy
    rcases (hmemD y).mp hy with rfl | rfl | rfl | ⟨l, hl, rfl⟩ | ⟨i, hi, rfl⟩
    exacts [A.h₁, A.h₂, A.h₄, (Finset.mem_sdiff.mp (S.hψ l hl)).1,
      (Finset.mem_sdiff.mp (T.hν i hi)).1]
  have hDodd : ∀ y ∈ D, Odd (V y) := by
    intro y hy
    rcases (hmemD y).mp hy with rfl | rfl | rfl | ⟨l, hl, rfl⟩ | ⟨i, hi, rfl⟩
    · exact hodd₁
    · exact hodd₂
    · exact hodd₄
    · rw [hVψ l hl]
      exact hoddψ
    · rw [hVν i hi, ← hVν 1 h1r]
      exact hoddν
  have hψC : ∀ l ∈ Icc 1 (k - 1), ψ l ≠ c₀ ∧ ψ l ≠ c₁ ∧ ψ l ≠ c₂ ∧ ψ l ≠ c₃ ∧ ψ l ≠ c₄ :=
    fun l hl => (mem_sdiff_five.mp (S.hψ l hl)).2
  have hνC : ∀ i ∈ range k, ν i ≠ c₀ ∧ ν i ≠ c₁ ∧ ν i ≠ c₂ ∧ ν i ≠ c₃ ∧ ν i ≠ c₄ :=
    fun i hi => (mem_sdiff_five.mp (T.hν i hi)).2
  have hcard : #D = 2 * k + 2 := by
    have hA : #((Icc 1 (k - 1)).image ψ) = k - 1 := by
      rw [Finset.card_image_of_injOn S.inj, Nat.card_Icc]
      omega
    have hB' : #((range k).image ν) = k := by
      rw [Finset.card_image_of_injOn T.inj, Finset.card_range]
    have hdisj : Disjoint ((Icc 1 (k - 1)).image ψ) ((range k).image ν) := by
      rw [Finset.disjoint_left]
      intro y hya hyb
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hya
      obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hyb
      exact T.νψ i hi l hl e
    have hx₄n : c₄ ∉ (Icc 1 (k - 1)).image ψ ∪ (range k).image ν := by
      simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
      exact ⟨fun l hl e => (hψC l hl).2.2.2.2 e, fun i hi e => (hνC i hi).2.2.2.2 e⟩
    have hx₂n : c₂ ∉ insert c₄ ((Icc 1 (k - 1)).image ψ ∪ (range k).image ν) := by
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or, not_exists,
        not_and]
      exact ⟨A.n24, fun l hl e => (hψC l hl).2.2.1 e, fun i hi e => (hνC i hi).2.2.1 e⟩
    have hx₁n : c₁ ∉ insert c₂ (insert c₄ ((Icc 1 (k - 1)).image ψ ∪ (range k).image ν)) := by
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or, not_exists,
        not_and]
      exact ⟨A.n12, A.n14, fun l hl e => (hψC l hl).2.1 e, fun i hi e => (hνC i hi).2.1 e⟩
    rw [hD, Finset.card_insert_of_notMem hx₁n, Finset.card_insert_of_notMem hx₂n,
      Finset.card_insert_of_notMem hx₄n, Finset.card_union_of_disjoint hdisj, hA, hB']
    omega
  obtain ⟨hpm, hzero⟩ := Principal.ColumnRigidity.odd_support_of_norm_eq_card hDB hDodd (by
    rw [h.hVV, hcard]
    push_cast
    ring)
  have hV0 : ∀ x ∈ B, x ≠ c₁ → x ≠ c₂ → x ≠ c₄ → (∀ l ∈ Icc 1 (k - 1), x ≠ ψ l) →
      (∀ i ∈ range k, x ≠ ν i) → V x = 0 := by
    intro x hx h1 h2 h4 hψ' hν'
    refine hzero x hx fun hxD => ?_
    rcases (hmemD x).mp hxD with e | e | e | ⟨l, hl, e⟩ | ⟨i, hi, e⟩
    exacts [h1 e, h2 e, h4 e, hψ' l hl e.symm, hν' i hi e.symm]
  have hVc₀ : V c₀ = 0 := hV0 c₀ A.h₀ A.n01 A.n02 A.n04
    (fun l hl e => (hψC l hl).1 e.symm) fun i hi e => (hνC i hi).1 e.symm
  have hVc₃ : V c₃ = 0 := hV0 c₃ A.h₃ A.n13.symm A.n23.symm A.n34
    (fun l hl e => (hψC l hl).2.2.2.1 e.symm) fun i hi e => (hνC i hi).2.2.2.1 e.symm
  have hVΘ := h.hVΘ
  rw [A.sum_mul_Θ V, hVc₀, hVc₃] at hVΘ
  have hUV := h.hUV
  rw [A.sum_U_mul V, hVc₀, hVc₃] at hUV
  have hv₁ := hpm c₁ ((hmemD c₁).mpr (Or.inl rfl))
  have hv₂ := hpm c₂ ((hmemD c₂).mpr (Or.inr (Or.inl rfl)))
  have hv₄ := hpm c₄ ((hmemD c₄).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hp : δ₁ * V c₁ = 1 ∨ δ₁ * V c₁ = -1 := by
    rcases hv₁ with e | e <;> rcases A.s₁ with hd | hd <;> rw [e, hd] <;> norm_num
  have hq : δ₂ * V c₂ = 1 ∨ δ₂ * V c₂ = -1 := by
    rcases hv₂ with e | e <;> rcases A.s₂ with hd | hd <;> rw [e, hd] <;> norm_num
  have hr : δ₄ * V c₄ = 1 ∨ δ₄ * V c₄ = -1 := by
    rcases hv₄ with e | e <;> rcases A.s₄ with hd | hd <;> rw [e, hd] <;> norm_num
  have e₁ : δ₁ * V c₁ + δ₂ * V c₂ = 0 := by linear_combination hVΘ
  have e₂ : 2 * (δ₄ * V c₄) = 2 * (δ₁ * V c₁) - 4 := by linear_combination hUV - e₁
  have hp1 : δ₁ * V c₁ = 1 := by omega
  have hq1 : δ₂ * V c₂ = -1 := by omega
  have hr1 : δ₄ * V c₄ = -1 := by omega
  have hV₁ : V c₁ = δ₁ := by linear_combination δ₁ * hp1 - V c₁ * sign_mul_self A.s₁
  have hV₂ : V c₂ = -δ₂ := by linear_combination δ₂ * hq1 - V c₂ * sign_mul_self A.s₂
  have hV₄ : V c₄ = -δ₄ := by linear_combination δ₄ * hr1 - V c₄ * sign_mul_self A.s₄
  have hVψδ : ∀ l ∈ Icc 1 (k - 1), V (ψ l) = δ := fun l hl => by
    have e := hVE l hl
    rw [hVc₀, hV₁, sign_mul_self A.s₁] at e
    linear_combination δ * e - V (ψ l) * sign_mul_self S.hδ
  exact ⟨hV₁, hV₂, hV₄, hVψδ, hVν,
    hpm _ ((hmemD (ν 0)).mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨0, h0r, rfl⟩))))), hV0⟩

theorem Hyp.V_apply (h : Hyp k B deg Θ E F U V)
    (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ)
    (T : FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ ν δF) {aν : ℤ} (haν : ∀ i ∈ range k, V (ν i) = -aν)
    {x : L} (hx : x ∈ B) :
    V x = δ₁ * (if x = c₁ then 1 else 0) - δ₂ * (if x = c₂ then 1 else 0) -
      δ₄ * (if x = c₄ then 1 else 0) + δ * ∑ l ∈ Icc 1 (k - 1), (if x = ψ l then 1 else 0) -
      aν * ∑ i ∈ range k, (if x = ν i then 1 else 0) := by
  obtain ⟨hV₁, hV₂, hV₄, hVψ, -, -, hV0⟩ := h.V_values A S T
  have hψC : ∀ l ∈ Icc 1 (k - 1), ψ l ≠ c₀ ∧ ψ l ≠ c₁ ∧ ψ l ≠ c₂ ∧ ψ l ≠ c₃ ∧ ψ l ≠ c₄ :=
    fun l hl => (mem_sdiff_five.mp (S.hψ l hl)).2
  have hνC : ∀ i ∈ range k, ν i ≠ c₀ ∧ ν i ≠ c₁ ∧ ν i ≠ c₂ ∧ ν i ≠ c₃ ∧ ν i ≠ c₄ :=
    fun i hi => (mem_sdiff_five.mp (T.hν i hi)).2
  by_cases e1 : x = c₁
  · subst e1
    rw [sum_ite_eq_zero_of_forall_ne fun l hl => (hψC l hl).2.1.symm,
      sum_ite_eq_zero_of_forall_ne fun i hi => (hνC i hi).2.1.symm]
    simp [A.n12, A.n14, hV₁]
  by_cases e2 : x = c₂
  · subst e2
    rw [sum_ite_eq_zero_of_forall_ne fun l hl => (hψC l hl).2.2.1.symm,
      sum_ite_eq_zero_of_forall_ne fun i hi => (hνC i hi).2.2.1.symm]
    simp [A.n12.symm, A.n24, hV₂]
  by_cases e4 : x = c₄
  · subst e4
    rw [sum_ite_eq_zero_of_forall_ne fun l hl => (hψC l hl).2.2.2.2.symm,
      sum_ite_eq_zero_of_forall_ne fun i hi => (hνC i hi).2.2.2.2.symm]
    simp [A.n14.symm, A.n24.symm, hV₄]
  by_cases eψ : ∃ l ∈ Icc 1 (k - 1), x = ψ l
  · obtain ⟨l, hl, rfl⟩ := eψ
    rw [sum_ite_eq_one_of_injOn S.inj hl,
      sum_ite_eq_zero_of_forall_ne fun i hi => (T.νψ i hi l hl).symm]
    simp [(hψC l hl).2.1, (hψC l hl).2.2.1, (hψC l hl).2.2.2.2, hVψ l hl]
  by_cases eν : ∃ i ∈ range k, x = ν i
  · obtain ⟨i, hi, rfl⟩ := eν
    rw [sum_ite_eq_zero_of_forall_ne fun l hl => T.νψ i hi l hl,
      sum_ite_eq_one_of_injOn T.inj hi]
    simp [(hνC i hi).2.1, (hνC i hi).2.2.1, (hνC i hi).2.2.2.2, haν i hi]
  have eψ' : ∀ l ∈ Icc 1 (k - 1), x ≠ ψ l := fun l hl e => eψ ⟨l, hl, e⟩
  have eν' : ∀ i ∈ range k, x ≠ ν i := fun i hi e => eν ⟨i, hi, e⟩
  rw [sum_ite_eq_zero_of_forall_ne eψ', sum_ite_eq_zero_of_forall_ne eν']
  simp [e1, e2, e4, hV0 x hx e1 e2 e4 eψ' eν']

theorem Hyp.stageV (h : Hyp k B deg Θ E F U V)
    (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ)
    (T : FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ ν δF) :
    (∀ x ∈ B, V x = δ₁ * (if x = c₁ then 1 else 0) - δ₂ * (if x = c₂ then 1 else 0) -
      δ₄ * (if x = c₄ then 1 else 0) + δ * ∑ l ∈ Icc 1 (k - 1), (if x = ψ l then 1 else 0) -
      δ * ∑ i ∈ range k, (if x = ν i then 1 else 0)) ∧ (4 ≤ k → δF = δ) := by
  have hk := h.hk
  have hI1 := h.one_mem
  have h1r : 1 ∈ range k := Finset.mem_range.mpr (by omega)
  have h0r : 0 ∈ range k := Finset.mem_range.mpr (by omega)
  obtain ⟨-, -, -, -, hVν, hVν0, -⟩ := h.V_values A S T
  have haν : ∀ i ∈ range k, V (ν i) = -(-V (ν 0)) := fun i hi => by rw [hVν i hi, neg_neg]
  have hψB : ∀ l ∈ Icc 1 (k - 1), ψ l ∈ B := fun l hl => (Finset.mem_sdiff.mp (S.hψ l hl)).1
  have hνB : ∀ i ∈ range k, ν i ∈ B := fun i hi => (Finset.mem_sdiff.mp (T.hν i hi)).1
  have eΘ := h.hdegΘ
  rw [A.sum_mul_Θ deg] at eΘ
  have eU := h.hdegU
  rw [A.sum_mul_U deg] at eU
  have eE : ∀ l ∈ Icc 1 (k - 1), δ₀ * deg c₀ + δ₁ * deg c₁ - δ * deg (ψ l) = 0 :=
    fun l hl => by rw [← S.sum_mul_E A.h₀ A.h₁ hl deg]; exact h.hdegE l hl
  have eF : ∀ j ∈ Icc 1 (k - 1), δF * (deg (ν j) - deg (ν 0)) = 0 :=
    fun j hj => by rw [← T.sum_mul_F hk hj deg]; exact h.hdegF j hj
  have eV : δ₁ * deg c₁ - δ₂ * deg c₂ - δ₄ * deg c₄ + δ * ∑ l ∈ Icc 1 (k - 1), deg (ψ l) -
      (-V (ν 0)) * ∑ i ∈ range k, deg (ν i) = 0 := by
    have e := h.hdegV
    have hpt : ∀ x ∈ B, deg x * V x = deg x * (δ₁ * (if x = c₁ then 1 else 0) -
        δ₂ * (if x = c₂ then 1 else 0) - δ₄ * (if x = c₄ then 1 else 0) +
        δ * ∑ l ∈ Icc 1 (k - 1), (if x = ψ l then 1 else 0) -
        (-V (ν 0)) * ∑ i ∈ range k, (if x = ν i then 1 else 0)) :=
      fun x hx => by rw [h.V_apply A S T haν hx]
    rw [Finset.sum_congr rfl hpt, sum_mul_formV deg A.h₁ A.h₂ A.h₄ hψB hνB] at e
    exact e
  obtain ⟨-, h14, h17, -⟩ := orth_relations (R := ℤ) (X₀ := deg c₀) (X₁ := deg c₁)
    (X₂ := deg c₂) (X₃ := deg c₃) (X₄ := deg c₄) (Xψ := fun l => deg (ψ l))
    (Xν := fun i => deg (ν i)) hk (sign_ne_zero T.hδF) eΘ eE eF eU eV
  have e : -V (ν 0) * deg (ν 0) = δ * deg (ψ 1) := (h17 0 h0r).trans (h14 1 hI1).symm
  have hp1 := h.hdeg (ν 0) (hνB 0 h0r)
  have hp2 := h.hdeg (ψ 1) (hψB 1 hI1)
  have haνδ : -V (ν 0) = δ := by
    rcases hVν0 with ha | ha <;> rcases S.hδ with hd | hd <;> rw [ha, hd] at e ⊢ <;>
      first | rfl | (exfalso; linarith)
  refine ⟨fun x hx => by rw [h.V_apply A S T haν hx, haνδ], fun hk4 => ?_⟩
  obtain ⟨-, -, -, -, cgν⟩ := h.cong_points A S T
  rw [haν 1 h1r, haνδ] at cgν
  have hdvd : (k : ℤ) ∣ δF - δ := by
    have e2 : (2 * k : ℤ) ∣ 2 * (δF - δ) := by
      convert cgν using 1
      ring
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp e2
  have hlt : |δF - δ| < k := by
    have hk4' : (4 : ℤ) ≤ k := by exact_mod_cast hk4
    rcases T.hδF with e1 | e1 <;> rcases S.hδ with e2 | e2 <;> rw [e1, e2] <;> norm_num <;>
      linarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  linarith

end StageV

end TableCoordinates

end CFSG.Semidihedral.FieldFactorOne
