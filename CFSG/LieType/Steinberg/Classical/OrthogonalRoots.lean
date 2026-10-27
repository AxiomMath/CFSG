module

public import CFSG.LieType.Universal.Spin.Roots.TypeB
public import CFSG.LieType.Universal.Spin.Roots.TypeD
public import CFSG.LieType.Steinberg.Statement

public section

namespace CFSG.LieType.Steinberg.Orthogonal

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem

variable {n : ℕ}

section Norm

variable (T : (Fin n → ℤ) →+ (Fin n → ℤ))

@[expose] def normSq (v : Fin n → ℤ) : ℤ := ∑ a, T v a * T v a

@[expose] def dotT (v w : Fin n → ℤ) : ℤ := ∑ a, T v a * T w a

theorem normSq_nsmul_add_nsmul (i j : ℕ) (v w : Fin n → ℤ) :
    normSq T (i • v + j • w) =
      (i : ℤ) ^ 2 * normSq T v + (j : ℤ) ^ 2 * normSq T w + 2 * i * j * dotT T v w := by
  have h : T (i • v + j • w) = i • T v + j • T w := by rw [map_add, map_nsmul, map_nsmul]
  simp only [normSq, dotT, h]
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem normSq_add (v w : Fin n → ℤ) :
    normSq T (v + w) = normSq T v + normSq T w + 2 * dotT T v w := by
  simp only [normSq, dotT, map_add, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem normSq_sub (v w : Fin n → ℤ) :
    normSq T (v - w) = normSq T v + normSq T w - 2 * dotT T v w := by
  simp only [normSq, dotT, map_sub, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

variable {T}

theorem one_le_normSq (hT : Function.Injective T) {v : Fin n → ℤ} (hv : v ≠ 0) :
    1 ≤ normSq T v := by
  have hTv : T v ≠ 0 := fun h => hv (hT (h.trans (map_zero T).symm))
  obtain ⟨a, ha⟩ : ∃ a, T v a ≠ 0 := by
    by_contra h
    push Not at h
    exact hTv (funext h)
  have hle : T v a * T v a ≤ normSq T v :=
    Finset.single_le_sum (f := fun b => T v b * T v b) (fun b _ => mul_self_nonneg _)
      (Finset.mem_univ a)
  have : 1 ≤ T v a * T v a := by nlinarith [mul_self_pos.2 ha]
  omega

theorem two_mul_abs_dotT_le (hT : Function.Injective T) {α β : Fin n → ℤ} (h1 : α ≠ β)
    (h2 : α + β ≠ 0) :
    2 * dotT T α β ≤ normSq T α + normSq T β - 1 ∧
      -(2 * dotT T α β) ≤ normSq T α + normSq T β - 1 := by
  have hs := one_le_normSq hT (sub_ne_zero.2 h1)
  have ha := one_le_normSq hT h2
  rw [normSq_sub] at hs
  rw [normSq_add] at ha
  constructor <;> linarith

end Norm

theorem exponent_bound {A B C : ℤ} {i j : ℕ} (hA : A = 1 ∨ A = 2) (hB : B = 1 ∨ B = 2)
    (hC1 : 2 * C ≤ A + B - 1) (hC2 : -(2 * C) ≤ A + B - 1) (hi : 0 < i) (hj : 0 < j)
    (hM : (i : ℤ) ^ 2 * A + (j : ℤ) ^ 2 * B + 2 * i * j * C ≤ 2) :
    (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
  have hi' : (1 : ℤ) ≤ i := by exact_mod_cast hi
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hij : (0 : ℤ) ≤ i * j := by positivity
  have hbound : (i : ℤ) ≤ 2 ∧ (j : ℤ) ≤ 2 := by
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · have : C = 0 := by omega
      subst this
      constructor <;> nlinarith
    · have : -1 ≤ C := by omega
      have hC' : -(2 * (i : ℤ) * j) ≤ 2 * i * j * C := by nlinarith
      constructor <;> nlinarith [sq_nonneg ((i : ℤ) - j)]
    · have : -1 ≤ C := by omega
      have hC' : -(2 * (i : ℤ) * j) ≤ 2 * i * j * C := by nlinarith
      constructor <;> nlinarith [sq_nonneg ((i : ℤ) - j)]
    · have : -1 ≤ C := by omega
      have hC' : -(2 * (i : ℤ) * j) ≤ 2 * i * j * C := by nlinarith
      constructor <;> nlinarith [sq_nonneg ((i : ℤ) - j)]
  obtain ⟨hi2, hj2⟩ := hbound
  have hi2' : i ≤ 2 := by exact_mod_cast hi2
  have hj2' : j ≤ 2 := by exact_mod_cast hj2
  interval_cases i <;> interval_cases j
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exfalso
    push_cast at hM
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> omega

theorem exponent_bound_two {C : ℤ} {i j : ℕ} (hC1 : 2 * C ≤ 3) (hC2 : -(2 * C) ≤ 3)
    (hi : 0 < i) (hj : 0 < j) (hM : (i : ℤ) ^ 2 * 2 + (j : ℤ) ^ 2 * 2 + 2 * i * j * C ≤ 2) :
    i = 1 ∧ j = 1 := by
  have hC : -1 ≤ C := by omega
  have hi' : (1 : ℤ) ≤ i := by exact_mod_cast hi
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hij : (0 : ℤ) ≤ i * j := by positivity
  have hC' : -(2 * (i : ℤ) * j) ≤ 2 * i * j * C := by nlinarith
  have h1 : (i : ℤ) ≤ 1 := by nlinarith [sq_nonneg ((i : ℤ) - j)]
  have h2 : (j : ℤ) ≤ 1 := by nlinarith [sq_nonneg ((i : ℤ) - j)]
  constructor <;> omega

section TypeB

variable (n) in
@[expose] def toStdBHom : (Fin n → ℤ) →+ (Fin n → ℤ) where
  toFun := toStdB n
  map_zero' := toStdB_zero n
  map_add' := toStdB_add n

theorem toStdBHom_injective : Function.Injective (toStdBHom n) := toStdB_injective n

theorem normSq_single_add_single {i j : Fin n} (hij : i ≠ j) {s t : ℤ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) (T : (Fin n → ℤ) →+ (Fin n → ℤ)) {γ : Fin n → ℤ}
    (h : T γ = Pi.single i s + Pi.single j t) : normSq T γ = 2 := by
  simp only [normSq, h, Pi.add_apply, Pi.single_apply]
  rw [Finset.sum_eq_add i j hij]
  · simp only [↓reduceIte, Ne.symm hij, hij]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num
  · intro c _ hc
    simp [hc.1, hc.2]
  · simp
  · simp

theorem normSq_single {i : Fin n} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (T : (Fin n → ℤ) →+ (Fin n → ℤ)) {γ : Fin n → ℤ} (h : T γ = Pi.single i s) :
    normSq T γ = 1 := by
  simp only [normSq, h, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp only [↓reduceIte]
    rcases hs with rfl | rfl <;> norm_num
  · intro c _ hc
    simp [hc]
  · simp

theorem normSq_of_mem_rootsB {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) :
    normSq (toStdBHom n) γ = 1 ∨ normSq (toStdBHom n) γ = 2 := by
  rw [rootsB_eq] at hγ
  rcases hγ with ⟨i, j, s, t, hij, hs, ht, h⟩ | ⟨i, s, hs, h⟩
  · exact Or.inr (normSq_single_add_single hij hs ht _ h)
  · exact Or.inl (normSq_single hs _ h)

theorem mem_expPairs_B {Φ : RootSystem (Fin n)} (hΦ : Φ.roots = roots (isFiniteType_cartanB n) ∅)
    {α β : Fin n → ℤ} (hα : α ∈ Φ.roots) (hβ : β ∈ Φ.roots) (hαβ : α + β ≠ 0) (p : ℕ × ℕ) :
    p ∈ expPairs Φ α β ↔
      (p = (1, 1) ∨ p = (1, 2) ∨ p = (2, 1)) ∧ p.1 • α + p.2 • β ∈ Φ.roots := by
  rw [hΦ] at hα hβ
  constructor
  · rintro ⟨hp1, hp2, hr⟩
    refine ⟨?_, hr⟩
    rw [hΦ] at hr
    have hM := normSq_of_mem_rootsB hr
    rw [normSq_nsmul_add_nsmul] at hM
    have hA := normSq_of_mem_rootsB hα
    have hB := normSq_of_mem_rootsB hβ
    have hM' : (p.1 : ℤ) ^ 2 * normSq (toStdBHom n) α + (p.2 : ℤ) ^ 2 * normSq (toStdBHom n) β +
        2 * p.1 * p.2 * dotT (toStdBHom n) α β ≤ 2 := by omega
    by_cases hab : α = β
    · subst hab
      exfalso
      have hd : dotT (toStdBHom n) α α = normSq (toStdBHom n) α := rfl
      rw [hd] at hM'
      have h1 : (1 : ℤ) ≤ p.1 := by exact_mod_cast hp1
      have h2 : (1 : ℤ) ≤ p.2 := by exact_mod_cast hp2
      rcases hA with h | h <;> rw [h] at hM' <;> nlinarith
    · obtain ⟨hC1, hC2⟩ := two_mul_abs_dotT_le toStdBHom_injective hab hαβ
      rcases exponent_bound hA hB hC1 hC2 hp1 hp2 hM' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Prod.ext h1 h2)
      · exact Or.inr (Or.inl (Prod.ext h1 h2))
      · exact Or.inr (Or.inr (Prod.ext h1 h2))
  · rintro ⟨hp, hr⟩
    refine ⟨?_, ?_, hr⟩ <;> rcases hp with rfl | rfl | rfl <;> norm_num

end TypeB

section TypeD

variable (n) in
@[expose] def toStdDHom : (Fin n → ℤ) →+ (Fin n → ℤ) where
  toFun := toStdD n
  map_zero' := toStdD_zero n
  map_add' := toStdD_add n

theorem toStdDHom_injective : Function.Injective (toStdDHom n) := toStdD_injective n

theorem normSq_of_mem_rootsD (hn : n ≠ 1) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) : normSq (toStdDHom n) γ = 2 := by
  rw [rootsD_eq n hn] at hγ
  obtain ⟨i, j, s, t, hij, hs, ht, h⟩ := hγ
  exact normSq_single_add_single hij hs ht _ h

theorem mem_expPairs_D (hn : n ≠ 1) {Φ : RootSystem (Fin n)}
    (hΦ : Φ.roots = roots (isFiniteType_cartanD n) ∅) {α β : Fin n → ℤ} (hα : α ∈ Φ.roots)
    (hβ : β ∈ Φ.roots) (hαβ : α + β ≠ 0) (p : ℕ × ℕ) :
    p ∈ expPairs Φ α β ↔ p = (1, 1) ∧ α + β ∈ Φ.roots := by
  rw [hΦ] at hα hβ
  constructor
  · rintro ⟨hp1, hp2, hr⟩
    rw [hΦ] at hr
    have hM := normSq_of_mem_rootsD hn hr
    rw [normSq_nsmul_add_nsmul, normSq_of_mem_rootsD hn hα, normSq_of_mem_rootsD hn hβ] at hM
    by_cases hab : α = β
    · subst hab
      exfalso
      have hd : dotT (toStdDHom n) α α = normSq (toStdDHom n) α := rfl
      rw [hd, normSq_of_mem_rootsD hn hα] at hM
      have h1 : (1 : ℤ) ≤ p.1 := by exact_mod_cast hp1
      have h2 : (1 : ℤ) ≤ p.2 := by exact_mod_cast hp2
      nlinarith
    · obtain ⟨hC1, hC2⟩ := two_mul_abs_dotT_le toStdDHom_injective hab hαβ
      rw [normSq_of_mem_rootsD hn hα, normSq_of_mem_rootsD hn hβ] at hC1 hC2
      obtain ⟨h1, h2⟩ := exponent_bound_two (by omega) (by omega) hp1 hp2 hM.le
      have hp : p = (1, 1) := Prod.ext h1 h2
      refine ⟨hp, ?_⟩
      have hr' : p.1 • α + p.2 • β ∈ roots (isFiniteType_cartanD n) ∅ := hr
      rw [hp] at hr'
      simpa [hΦ] using hr'
  · rintro ⟨rfl, hr⟩
    exact ⟨one_pos, one_pos, by simpa using hr⟩

end TypeD

end CFSG.LieType.Steinberg.Orthogonal
