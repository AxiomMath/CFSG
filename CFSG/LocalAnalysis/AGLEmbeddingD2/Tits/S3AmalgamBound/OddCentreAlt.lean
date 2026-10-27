module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open
open scoped Pointwise

theorem zpow_cases_of_cube {A : Type*} [Group A] (y : A) (h3 : y ^ 3 = 1) (k : ℤ) :
    y ^ k = 1 ∨ y ^ k = y ∨ y ^ k = y⁻¹ := by
  have : y ^ k = y ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
    have : y ^ (3 : ℤ) = 1 := by exact_mod_cast h3
    rw [this, one_zpow, mul_one]
  rw [this]
  have hm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hm with hm | hm | hm
  · left; rw [hm]; simp
  · right; left; rw [hm]; simp
  · right; right; rw [hm]
    have : y ^ (2 : ℤ) * y = 1 := by rw [← zpow_add_one]; exact_mod_cast h3
    exact eq_inv_of_mul_eq_one_left this

namespace Alt6

open Equiv

abbrev A := alternatingGroup (Fin 6)

def a0 : A := ⟨c[0, 1, 2], by rw [Perm.mem_alternatingGroup]; decide⟩
def b0 : A := ⟨c[3, 4, 5], by rw [Perm.mem_alternatingGroup]; decide⟩
def gg : A := ⟨c[0, 3] * c[1, 4, 2, 5], by rw [Perm.mem_alternatingGroup]; decide⟩

theorem a0_pow : a0 ^ 3 = 1 := by decide +kernel
theorem a0_ne : a0 ≠ 1 := by decide +kernel
theorem b0_not_mem_zpowers_a0 : b0 ∉ Subgroup.zpowers a0 := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rcases zpow_cases_of_cube a0 a0_pow k with h | h | h <;> rw [h] at hk <;> revert hk <;> decide +kernel
theorem mem_closure_iff (x : A) (hx : x ∈ Subgroup.closure ({a0, b0} : Set A)) :
    ∃ i j : Fin 3, x = a0 ^ (i : ℕ) * b0 ^ (j : ℕ) := by
  have hmul : ∀ i j k l : Fin 3, ∃ m n : Fin 3,
      (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * (a0 ^ (k : ℕ) * b0 ^ (l : ℕ)) =
        a0 ^ (m : ℕ) * b0 ^ (n : ℕ) := by decide +kernel
  have hinv : ∀ i j : Fin 3, ∃ m n : Fin 3,
      (a0 ^ (i : ℕ) * b0 ^ (j : ℕ))⁻¹ = a0 ^ (m : ℕ) * b0 ^ (n : ℕ) := by decide +kernel
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    obtain ⟨m, n, h⟩ := hmul i j k l
    exact ⟨m, n, h⟩
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨m, n, h⟩ := hinv i j
    exact ⟨m, n, h⟩

theorem gg_not_mem : ∀ i j : Fin 3, (i, j) ≠ ((0 : Fin 3), (0 : Fin 3)) →
    gg * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * gg⁻¹ ≠ 1 ∧
    gg * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * gg⁻¹ ≠ a0 ^ (i : ℕ) * b0 ^ (j : ℕ) ∧
    gg * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * gg⁻¹ ≠ (a0 ^ (i : ℕ) * b0 ^ (j : ℕ))⁻¹ := by
  decide +kernel

theorem gg_conj_closure : ∀ i j : Fin 3, ∃ m n : Fin 3,
    gg * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * gg⁻¹ = a0 ^ (m : ℕ) * b0 ^ (n : ℕ) := by decide +kernel

theorem ggi_conj_closure : ∀ i j : Fin 3, ∃ m n : Fin 3,
    gg⁻¹ * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * gg = a0 ^ (m : ℕ) * b0 ^ (n : ℕ) := by decide +kernel

theorem exp3 : ∀ i j : Fin 3, (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) ^ 3 = 1 := by decide +kernel

theorem comm_all : ∀ i j k l : Fin 3,
    (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * (a0 ^ (k : ℕ) * b0 ^ (l : ℕ)) =
      (a0 ^ (k : ℕ) * b0 ^ (l : ℕ)) * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) := by decide +kernel

def P0 : Subgroup A := Subgroup.closure ({a0, b0} : Set A)

theorem P0_elems : ∀ x ∈ P0, ∃ i j : Fin 3, x = a0 ^ (i : ℕ) * b0 ^ (j : ℕ) := mem_closure_iff

theorem P0_pow : ∀ x ∈ P0, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨i, j, rfl⟩ := P0_elems x hx
  exact exp3 i j

theorem P0_comm : ∀ x ∈ P0, ∀ y ∈ P0, x * y = y * x := by
  intro x hx y hy
  obtain ⟨i, j, rfl⟩ := P0_elems x hx
  obtain ⟨k, l, rfl⟩ := P0_elems y hy
  exact comm_all i j k l

theorem card_A : Nat.card A = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem fact3 : (Nat.card A).factorization 3 = 2 := by
  rw [card_A]
  have h : (360 : ℕ) = 3 ^ 2 * 40 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 40),
    Nat.Prime.factorization_pow Nat.prime_three]
  simp

theorem isPGroup_P0 : IsPGroup 3 P0 := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using P0_pow g.1 g.2

theorem card_P0 : Nat.card P0 = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := isPGroup_P0.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup A) = 9 := by
    rw [Sylow.card_eq_multiplicity, fact3]; norm_num
  have h1 : Nat.card P0 ∣ 9 := hQcard ▸ Subgroup.card_dvd_of_le hQ
  have ha : a0 ∈ P0 := Subgroup.subset_closure (Or.inl rfl)
  have hb : b0 ∈ P0 := Subgroup.subset_closure (Or.inr rfl)
  have hz : Subgroup.zpowers a0 < P0 :=
    lt_of_le_of_ne ((Subgroup.zpowers_le).mpr ha) (fun h => b0_not_mem_zpowers_a0 (h ▸ hb))
  have h3 : Nat.card (Subgroup.zpowers a0) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime a0_pow a0_ne
  have h5 : 3 < Nat.card P0 := by
    by_contra hle
    push Not at hle
    have : Subgroup.zpowers a0 = P0 :=
      Subgroup.eq_of_le_of_card_ge hz.le (by rw [h3]; exact hle)
    exact hz.ne this
  have hle : Nat.card P0 ≤ 9 := Nat.le_of_dvd (by norm_num) h1
  have key : ∀ n ≤ 9, 3 < n → n ∣ 9 → n = 9 := by decide
  exact key _ hle h5 h1

theorem normalizes_P0 : ∀ x : A, x ∈ P0 ↔ gg * x * gg⁻¹ ∈ P0 := by
  have hgen : ∀ m n : Fin 3, a0 ^ (m : ℕ) * b0 ^ (n : ℕ) ∈ P0 := fun m n =>
    P0.mul_mem (P0.pow_mem (Subgroup.subset_closure (Or.inl rfl)) _)
      (P0.pow_mem (Subgroup.subset_closure (Or.inr rfl)) _)
  have h1 : ∀ x ∈ P0, gg * x * gg⁻¹ ∈ P0 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := P0_elems x hx
    obtain ⟨m, n, h⟩ := gg_conj_closure i j
    rw [h]; exact hgen m n
  have h2 : ∀ x ∈ P0, gg⁻¹ * x * gg ∈ P0 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := P0_elems x hx
    obtain ⟨m, n, h⟩ := ggi_conj_closure i j
    rw [h]; exact hgen m n
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem exists_conj (Pb : Subgroup A) (h9 : Nat.card Pb = 9) :
    ∃ t : A, ∀ x : A, x ∈ Pb ↔ t⁻¹ * x * t ∈ P0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let SP : Sylow 3 A := Sylow.ofCard Pb (by rw [h9, fact3]; norm_num)
  let S0 : Sylow 3 A := Sylow.ofCard P0 (by rw [card_P0, fact3]; norm_num)
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq A S0 SP
  refine ⟨t, fun x => ?_⟩
  have h : (SP : Subgroup A) = MulAut.conj t • (S0 : Subgroup A) := by
    rw [← ht, Sylow.coe_subgroup_smul]
  have hSP : (SP : Subgroup A) = Pb := rfl
  have hS0 : (S0 : Subgroup A) = P0 := rfl
  rw [← hSP, h, hS0, Subgroup.pointwise_smul_def]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨t⁻¹ * x * t, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem hel_hg_A (Pb : Subgroup A) (h9 : Nat.card Pb = 9) :
    IsElemAbelian 3 Pb ∧ ∃ g ∈ Subgroup.normalizer (Pb : Set A),
      ∀ x ∈ Pb, x ≠ 1 → g * x * g⁻¹ ∉ Subgroup.zpowers x := by
  obtain ⟨t, ht⟩ := exists_conj Pb h9
  have hmemP : ∀ x ∈ Pb, t⁻¹ * x * t ∈ P0 := fun x hx => (ht x).mp hx
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, t * gg * t⁻¹, ?_, ?_⟩
  · have h := P0_comm _ (hmemP a a.2) _ (hmemP b b.2)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have : t⁻¹ * ((a : A) * b) * t = t⁻¹ * ((b : A) * a) * t := by
      calc t⁻¹ * ((a : A) * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) := by group
        _ = (t⁻¹ * b * t) * (t⁻¹ * a * t) := h
        _ = t⁻¹ * ((b : A) * a) * t := by group
    simpa using this
  · have h := P0_pow _ (hmemP x hx)
    have e : (t⁻¹ * x * t) ^ 3 = t⁻¹ * x ^ 3 * t := by
      simpa using (conj_pow (i := 3) (a := t⁻¹) (b := x))
    rw [e] at h
    have := congrArg (fun y => t * y * t⁻¹) h
    simpa [mul_assoc] using this
  · refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    rw [ht x, ht (t * gg * t⁻¹ * x * (t * gg * t⁻¹)⁻¹)]
    have e : t⁻¹ * (t * gg * t⁻¹ * x * (t * gg * t⁻¹)⁻¹) * t = gg * (t⁻¹ * x * t) * gg⁻¹ := by
      group
    rw [e]; exact normalizes_P0 _
  · intro x hx hx1 hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    set x₀ := t⁻¹ * x * t with hx₀
    have hx₀P : x₀ ∈ P0 := hmemP x hx
    obtain ⟨i, j, hij⟩ := P0_elems x₀ hx₀P
    have hx₀1 : x₀ ≠ 1 := fun h => hx1 (by
      have : x = t * x₀ * t⁻¹ := by rw [hx₀]; group
      rw [this, h]; group)
    have hij0 : (i, j) ≠ ((0 : Fin 3), (0 : Fin 3)) := by
      intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      apply hx₀1; rw [hij]; simp
    have hx₀3 : x₀ ^ 3 = 1 := P0_pow x₀ hx₀P
    have hconj : gg * x₀ * gg⁻¹ = x₀ ^ k := by
      have h1 : t⁻¹ * (x ^ k) * t = x₀ ^ k := by
        rw [hx₀]
        have := @conj_zpow _ _ k t⁻¹ x
        simpa using this.symm
      have h2 : t⁻¹ * (t * gg * t⁻¹ * x * (t * gg * t⁻¹)⁻¹) * t = gg * x₀ * gg⁻¹ := by
        rw [hx₀]; group
      rw [← h2, ← hk, h1]
    obtain ⟨n1, n2, n3⟩ := gg_not_mem i j hij0
    rw [← hij] at n1 n2 n3
    rcases zpow_cases_of_cube x₀ hx₀3 k with h | h | h
    · exact n1 (hconj.trans h)
    · exact n2 (hconj.trans h)
    · exact n3 (hconj.trans h)

end Alt6

namespace Alt7

open Equiv

abbrev A := alternatingGroup (Fin 7)

def a0 : A := ⟨c[0, 1, 2], by rw [Perm.mem_alternatingGroup]; decide⟩
def b0 : A := ⟨c[3, 4, 5], by rw [Perm.mem_alternatingGroup]; decide⟩
def gg : A := ⟨c[0, 3] * c[1, 4, 2, 5], by rw [Perm.mem_alternatingGroup]; decide⟩

theorem a0_pow : a0 ^ 3 = 1 := by decide +kernel
theorem a0_ne : a0 ≠ 1 := by decide +kernel
theorem b0_not_mem_zpowers_a0 : b0 ∉ Subgroup.zpowers a0 := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rcases zpow_cases_of_cube a0 a0_pow k with h | h | h <;> rw [h] at hk <;> revert hk <;> decide +kernel
theorem mem_closure_iff (x : A) (hx : x ∈ Subgroup.closure ({a0, b0} : Set A)) :
    ∃ i j : Fin 3, x = a0 ^ (i : ℕ) * b0 ^ (j : ℕ) := by
  have hmul : ∀ i j k l : Fin 3, ∃ m n : Fin 3,
      (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * (a0 ^ (k : ℕ) * b0 ^ (l : ℕ)) =
        a0 ^ (m : ℕ) * b0 ^ (n : ℕ) := by decide +kernel
  have hinv : ∀ i j : Fin 3, ∃ m n : Fin 3,
      (a0 ^ (i : ℕ) * b0 ^ (j : ℕ))⁻¹ = a0 ^ (m : ℕ) * b0 ^ (n : ℕ) := by decide +kernel
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    obtain ⟨m, n, h⟩ := hmul i j k l
    exact ⟨m, n, h⟩
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨m, n, h⟩ := hinv i j
    exact ⟨m, n, h⟩

theorem gg_not_mem : ∀ i j : Fin 3, (i, j) ≠ ((0 : Fin 3), (0 : Fin 3)) →
    gg * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * gg⁻¹ ≠ 1 ∧
    gg * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * gg⁻¹ ≠ a0 ^ (i : ℕ) * b0 ^ (j : ℕ) ∧
    gg * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * gg⁻¹ ≠ (a0 ^ (i : ℕ) * b0 ^ (j : ℕ))⁻¹ := by
  decide +kernel

theorem gg_conj_closure : ∀ i j : Fin 3, ∃ m n : Fin 3,
    gg * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * gg⁻¹ = a0 ^ (m : ℕ) * b0 ^ (n : ℕ) := by decide +kernel

theorem ggi_conj_closure : ∀ i j : Fin 3, ∃ m n : Fin 3,
    gg⁻¹ * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * gg = a0 ^ (m : ℕ) * b0 ^ (n : ℕ) := by decide +kernel

theorem exp3 : ∀ i j : Fin 3, (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) ^ 3 = 1 := by decide +kernel

theorem comm_all : ∀ i j k l : Fin 3,
    (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) * (a0 ^ (k : ℕ) * b0 ^ (l : ℕ)) =
      (a0 ^ (k : ℕ) * b0 ^ (l : ℕ)) * (a0 ^ (i : ℕ) * b0 ^ (j : ℕ)) := by decide +kernel

def P0 : Subgroup A := Subgroup.closure ({a0, b0} : Set A)

theorem P0_elems : ∀ x ∈ P0, ∃ i j : Fin 3, x = a0 ^ (i : ℕ) * b0 ^ (j : ℕ) := mem_closure_iff

theorem P0_pow : ∀ x ∈ P0, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨i, j, rfl⟩ := P0_elems x hx
  exact exp3 i j

theorem P0_comm : ∀ x ∈ P0, ∀ y ∈ P0, x * y = y * x := by
  intro x hx y hy
  obtain ⟨i, j, rfl⟩ := P0_elems x hx
  obtain ⟨k, l, rfl⟩ := P0_elems y hy
  exact comm_all i j k l

theorem card_A : Nat.card A = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem fact3 : (Nat.card A).factorization 3 = 2 := by
  rw [card_A]
  have h : (2520 : ℕ) = 3 ^ 2 * 280 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 280),
    Nat.Prime.factorization_pow Nat.prime_three]
  simp

theorem isPGroup_P0 : IsPGroup 3 P0 := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using P0_pow g.1 g.2

theorem card_P0 : Nat.card P0 = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := isPGroup_P0.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup A) = 9 := by
    rw [Sylow.card_eq_multiplicity, fact3]; norm_num
  have h1 : Nat.card P0 ∣ 9 := hQcard ▸ Subgroup.card_dvd_of_le hQ
  have ha : a0 ∈ P0 := Subgroup.subset_closure (Or.inl rfl)
  have hb : b0 ∈ P0 := Subgroup.subset_closure (Or.inr rfl)
  have hz : Subgroup.zpowers a0 < P0 :=
    lt_of_le_of_ne ((Subgroup.zpowers_le).mpr ha) (fun h => b0_not_mem_zpowers_a0 (h ▸ hb))
  have h3 : Nat.card (Subgroup.zpowers a0) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime a0_pow a0_ne
  have h5 : 3 < Nat.card P0 := by
    by_contra hle
    push Not at hle
    have : Subgroup.zpowers a0 = P0 :=
      Subgroup.eq_of_le_of_card_ge hz.le (by rw [h3]; exact hle)
    exact hz.ne this
  have hle : Nat.card P0 ≤ 9 := Nat.le_of_dvd (by norm_num) h1
  have key : ∀ n ≤ 9, 3 < n → n ∣ 9 → n = 9 := by decide
  exact key _ hle h5 h1

theorem normalizes_P0 : ∀ x : A, x ∈ P0 ↔ gg * x * gg⁻¹ ∈ P0 := by
  have hgen : ∀ m n : Fin 3, a0 ^ (m : ℕ) * b0 ^ (n : ℕ) ∈ P0 := fun m n =>
    P0.mul_mem (P0.pow_mem (Subgroup.subset_closure (Or.inl rfl)) _)
      (P0.pow_mem (Subgroup.subset_closure (Or.inr rfl)) _)
  have h1 : ∀ x ∈ P0, gg * x * gg⁻¹ ∈ P0 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := P0_elems x hx
    obtain ⟨m, n, h⟩ := gg_conj_closure i j
    rw [h]; exact hgen m n
  have h2 : ∀ x ∈ P0, gg⁻¹ * x * gg ∈ P0 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := P0_elems x hx
    obtain ⟨m, n, h⟩ := ggi_conj_closure i j
    rw [h]; exact hgen m n
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem exists_conj (Pb : Subgroup A) (h9 : Nat.card Pb = 9) :
    ∃ t : A, ∀ x : A, x ∈ Pb ↔ t⁻¹ * x * t ∈ P0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let SP : Sylow 3 A := Sylow.ofCard Pb (by rw [h9, fact3]; norm_num)
  let S0 : Sylow 3 A := Sylow.ofCard P0 (by rw [card_P0, fact3]; norm_num)
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq A S0 SP
  refine ⟨t, fun x => ?_⟩
  have h : (SP : Subgroup A) = MulAut.conj t • (S0 : Subgroup A) := by
    rw [← ht, Sylow.coe_subgroup_smul]
  have hSP : (SP : Subgroup A) = Pb := rfl
  have hS0 : (S0 : Subgroup A) = P0 := rfl
  rw [← hSP, h, hS0, Subgroup.pointwise_smul_def]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨t⁻¹ * x * t, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem hel_hg_A (Pb : Subgroup A) (h9 : Nat.card Pb = 9) :
    IsElemAbelian 3 Pb ∧ ∃ g ∈ Subgroup.normalizer (Pb : Set A),
      ∀ x ∈ Pb, x ≠ 1 → g * x * g⁻¹ ∉ Subgroup.zpowers x := by
  obtain ⟨t, ht⟩ := exists_conj Pb h9
  have hmemP : ∀ x ∈ Pb, t⁻¹ * x * t ∈ P0 := fun x hx => (ht x).mp hx
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, t * gg * t⁻¹, ?_, ?_⟩
  · have h := P0_comm _ (hmemP a a.2) _ (hmemP b b.2)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have : t⁻¹ * ((a : A) * b) * t = t⁻¹ * ((b : A) * a) * t := by
      calc t⁻¹ * ((a : A) * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) := by group
        _ = (t⁻¹ * b * t) * (t⁻¹ * a * t) := h
        _ = t⁻¹ * ((b : A) * a) * t := by group
    simpa using this
  · have h := P0_pow _ (hmemP x hx)
    have e : (t⁻¹ * x * t) ^ 3 = t⁻¹ * x ^ 3 * t := by
      simpa using (conj_pow (i := 3) (a := t⁻¹) (b := x))
    rw [e] at h
    have := congrArg (fun y => t * y * t⁻¹) h
    simpa [mul_assoc] using this
  · refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    rw [ht x, ht (t * gg * t⁻¹ * x * (t * gg * t⁻¹)⁻¹)]
    have e : t⁻¹ * (t * gg * t⁻¹ * x * (t * gg * t⁻¹)⁻¹) * t = gg * (t⁻¹ * x * t) * gg⁻¹ := by
      group
    rw [e]; exact normalizes_P0 _
  · intro x hx hx1 hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    set x₀ := t⁻¹ * x * t with hx₀
    have hx₀P : x₀ ∈ P0 := hmemP x hx
    obtain ⟨i, j, hij⟩ := P0_elems x₀ hx₀P
    have hx₀1 : x₀ ≠ 1 := fun h => hx1 (by
      have : x = t * x₀ * t⁻¹ := by rw [hx₀]; group
      rw [this, h]; group)
    have hij0 : (i, j) ≠ ((0 : Fin 3), (0 : Fin 3)) := by
      intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      apply hx₀1; rw [hij]; simp
    have hx₀3 : x₀ ^ 3 = 1 := P0_pow x₀ hx₀P
    have hconj : gg * x₀ * gg⁻¹ = x₀ ^ k := by
      have h1 : t⁻¹ * (x ^ k) * t = x₀ ^ k := by
        rw [hx₀]
        have := @conj_zpow _ _ k t⁻¹ x
        simpa using this.symm
      have h2 : t⁻¹ * (t * gg * t⁻¹ * x * (t * gg * t⁻¹)⁻¹) * t = gg * x₀ * gg⁻¹ := by
        rw [hx₀]; group
      rw [← h2, ← hk, h1]
    obtain ⟨n1, n2, n3⟩ := gg_not_mem i j hij0
    rw [← hij] at n1 n2 n3
    rcases zpow_cases_of_cube x₀ hx₀3 k with h | h | h
    · exact n1 (hconj.trans h)
    · exact n2 (hconj.trans h)
    · exact n3 (hconj.trans h)

end Alt7

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
