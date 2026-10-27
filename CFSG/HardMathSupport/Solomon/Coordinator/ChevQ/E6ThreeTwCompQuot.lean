module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

theorem twCompQuot_pow_three_of_pow {G : Type*} [Group G] {T : Subgroup G}
    (h9 : ∀ τ ∈ T, τ ^ 9 = 1 → τ ^ 3 = 1) :
    ∀ e : ℕ, ∀ σ ∈ T, σ ^ 3 ^ (e + 1) = 1 → σ ^ 3 = 1 := by
  intro e
  induction e with
  | zero => intro σ _ hσ; simpa using hσ
  | succ e ih =>
    intro σ hσT hσ
    apply ih σ hσT
    have h1 : (σ ^ 3 ^ e) ^ 9 = 1 := by
      rw [← pow_mul, show 3 ^ e * 9 = 3 ^ (e + 1 + 1) by ring]
      exact hσ
    have h2 := h9 _ (T.pow_mem hσT _) h1
    rwa [← pow_mul, ← pow_succ] at h2

theorem twCompQuot_exists_torsion {G : Type*} [Group G] {T N : Subgroup G} [Finite T]
    (h9 : ∀ τ ∈ T, τ ^ 9 = 1 → τ ^ 3 = 1) (hcube : ∀ τ ∈ T, τ ^ 3 ∈ N) {τ : G} (hτ : τ ∈ T) :
    ∃ χ ∈ T, χ ^ 3 = 1 ∧ τ * χ⁻¹ ∈ N := by
  have hM : Nat.card T ≠ 0 := Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  obtain ⟨e, m, hm3, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM 3 (by norm_num)
  have hτM : τ ^ Nat.card T = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := T) (x := ⟨τ, hτ⟩))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have hσ : (τ ^ m) ^ 3 ^ e = 1 := by
    rw [← pow_mul, mul_comm, ← hm, hτM]
  have hσ3 : (τ ^ m) ^ 3 = 1 := by
    cases e with
    | zero =>
      rw [pow_zero, pow_one] at hσ
      rw [hσ, one_pow]
    | succ e => exact twCompQuot_pow_three_of_pow h9 e _ (T.pow_mem hτ m) hσ
  obtain ⟨k, j, hkj⟩ : ∃ k j : ℕ, m * k = 3 * j + 1 := by
    rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with h | h
    · exact ⟨1, m / 3, by omega⟩
    · exact ⟨2, 2 * m / 3, by omega⟩
  refine ⟨(τ ^ m) ^ k, T.pow_mem (T.pow_mem hτ m) k, ?_, ?_⟩
  · rw [pow_right_comm, hσ3, one_pow]
  · have h1 : (τ ^ m) ^ k = (τ ^ j) ^ 3 * τ := by
      rw [← pow_mul, hkj, ← pow_mul, pow_succ, mul_comm j 3]
    rw [h1, mul_inv_rev, mul_inv_cancel_left]
    exact N.inv_mem (hcube _ (T.pow_mem hτ j))

theorem twCompQuot_dvd_of_pow_mem {G : Type*} [Group G] {N : Subgroup G} {χ : G}
    (hχ3 : χ ^ 3 = 1) (hχN : χ ∉ N) {m : ℕ} (hm : χ ^ m ∈ N) : 3 ∣ m := by
  rw [pow_eq_pow_mod m hχ3] at hm
  have hχ : χ = (χ ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hχ3, one_mul]
  rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
  · omega
  · rw [h, pow_one] at hm
    exact absurd hm hχN
  · rw [h] at hm
    exact (hχN (by rw [hχ]; exact N.pow_mem hm 2)).elim

theorem twCompQuot_torsion_cong {G : Type*} [Group G] {T N : Subgroup G} [Finite T]
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hNT : N ≤ T)
    (hX : Nat.card {τ : G // τ ∈ T ∧ τ ^ 3 = 1} ≤ 9) {h₀ : G} (hh₀N : h₀ ∈ N) (hh₀ : h₀ ≠ 1)
    (hh₀3 : h₀ ^ 3 = 1) {χ : G} (hχT : χ ∈ T) (hχ3 : χ ^ 3 = 1) (hχN : χ ∉ N)
    {ψ : G} (hψT : ψ ∈ T) (hψ3 : ψ ^ 3 = 1) : ∃ j < 3, ψ * (χ ^ j)⁻¹ ∈ N := by
  have hh₀T : h₀ ∈ T := hNT hh₀N
  have hc : Commute h₀ χ := hTc h₀ hh₀T χ hχT
  let F : Fin 3 × Fin 3 → {τ : G // τ ∈ T ∧ τ ^ 3 = 1} := fun p =>
    ⟨h₀ ^ (p.1 : ℕ) * χ ^ (p.2 : ℕ), T.mul_mem (T.pow_mem hh₀T _) (T.pow_mem hχT _), by
      rw [(hc.pow_pow _ _).mul_pow, pow_right_comm h₀, pow_right_comm χ, hh₀3, hχ3, one_pow,
        one_pow, one_mul]⟩
  have hinj : Function.Injective F := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hF
    have heq : h₀ ^ (i : ℕ) * χ ^ (j : ℕ) = h₀ ^ (i' : ℕ) * χ ^ (j' : ℕ) :=
      congrArg Subtype.val hF
    have hjN : χ ^ ((j : ℕ) + 2 * (j' : ℕ)) ∈ N := by
      have h1 : χ ^ (j : ℕ) * (χ ^ (j' : ℕ))⁻¹ = (h₀ ^ (i : ℕ))⁻¹ * h₀ ^ (i' : ℕ) := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq]
        exact heq
      have h2 : (χ ^ (j' : ℕ))⁻¹ = χ ^ (2 * (j' : ℕ)) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_add, show (j' : ℕ) + 2 * (j' : ℕ) = 3 * (j' : ℕ) by ring, pow_mul, hχ3,
          one_pow]
      rw [pow_add, ← h2, h1]
      exact N.mul_mem (N.inv_mem (N.pow_mem hh₀N _)) (N.pow_mem hh₀N _)
    have hd := twCompQuot_dvd_of_pow_mem hχ3 hχN hjN
    have hjj : j = j' := Fin.ext (by have := j.isLt; have := j'.isLt; omega)
    subst hjj
    have hii : h₀ ^ (i : ℕ) = h₀ ^ (i' : ℕ) := mul_right_cancel heq
    have ho : orderOf h₀ = 3 := orderOf_eq_prime hh₀3 hh₀
    have hi : (i : ℕ) ∈ Set.Iio (orderOf h₀) := by rw [ho]; exact i.isLt
    have hi' : (i' : ℕ) ∈ Set.Iio (orderOf h₀) := by rw [ho]; exact i'.isLt
    exact Prod.ext (Fin.ext (pow_injOn_Iio_orderOf hi hi' hii)) rfl
  haveI : Finite {τ : G // τ ∈ T ∧ τ ^ 3 = 1} :=
    Finite.of_injective (fun x => (⟨x.1, x.2.1⟩ : T)) fun a b hab =>
      Subtype.ext (congrArg (fun x : T => (x : G)) hab)
  obtain ⟨⟨i, j⟩, hij⟩ := (hinj.bijective_of_nat_card_le (by simpa using hX)).2 ⟨ψ, hψT, hψ3⟩
  have hψ : h₀ ^ (i : ℕ) * χ ^ (j : ℕ) = ψ := congrArg Subtype.val hij
  refine ⟨j, j.isLt, ?_⟩
  rw [← hψ, mul_inv_cancel_right]
  exact N.pow_mem hh₀N _

theorem twCompQuot_sq_mem {G : Type*} [Group G] {N : Subgroup G} {n χ : G}
    (hnN : ∀ τ, τ ∈ N ↔ n * τ * n⁻¹ ∈ N)
    (hab : n * χ * n⁻¹ * (n * (n * χ * n⁻¹) * n⁻¹) =
      n * (n * χ * n⁻¹) * n⁻¹ * (n * χ * n⁻¹))
    (h1 : n * χ * n⁻¹ * χ ∈ N) (h3 : n ^ 3 * χ * (n ^ 3)⁻¹ * χ⁻¹ ∈ N) : χ ^ 2 ∈ N := by
  have m2 := (hnN _).1 h1
  have m3 := (hnN _).1 m2
  have m2' : n * χ * n⁻¹ * (n * (n * χ * n⁻¹) * n⁻¹) ∈ N := by
    rw [hab]
    convert m2 using 1
    group
  have h := N.mul_mem (N.mul_mem (N.mul_mem (N.inv_mem h3) m3) (N.inv_mem m2')) h1
  rw [pow_two]
  convert h using 1
  group

theorem twCompQuot_comm_mem_of_mul_inv_mem {G : Type*} [Group G] {N : Subgroup G} {n σ τ : G}
    (hnN : ∀ τ, τ ∈ N ↔ n * τ * n⁻¹ ∈ N) (hσ : n * σ * n⁻¹ * σ⁻¹ ∈ N) (hτσ : τ * σ⁻¹ ∈ N) :
    n * τ * n⁻¹ * τ⁻¹ ∈ N := by
  have h := N.mul_mem (N.mul_mem ((hnN _).1 hτσ) hσ) (N.inv_mem hτσ)
  convert h using 1
  group

theorem twConj_comm_mem_of_cube {G : Type*} [Group G] {T N : Subgroup G} [Finite T]
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hNT : N ≤ T)
    (h9 : ∀ τ ∈ T, τ ^ 9 = 1 → τ ^ 3 = 1) (hcube : ∀ τ ∈ T, τ ^ 3 ∈ N)
    (hX : Nat.card {τ : G // τ ∈ T ∧ τ ^ 3 = 1} ≤ 9) {h₀ : G} (hh₀N : h₀ ∈ N) (hh₀ : h₀ ≠ 1)
    (hh₀3 : h₀ ^ 3 = 1) {n : G} (hnT : ∀ τ, τ ∈ T ↔ n * τ * n⁻¹ ∈ T)
    (hnN : ∀ τ, τ ∈ N ↔ n * τ * n⁻¹ ∈ N)
    (hn3 : ∀ τ ∈ T, n ^ 3 * τ * (n ^ 3)⁻¹ * τ⁻¹ ∈ N) :
    ∀ τ ∈ T, n * τ * n⁻¹ * τ⁻¹ ∈ N := by
  intro τ hτ
  rcases em (∃ χ ∈ T, χ ^ 3 = 1 ∧ χ ∉ N) with ⟨χ, hχT, hχ3, hχN⟩ | hXN
  · have hcong : ∀ σ ∈ T, ∃ j < 3, σ * (χ ^ j)⁻¹ ∈ N := by
      intro σ hσ
      obtain ⟨ψ, hψT, hψ3, hσψ⟩ := twCompQuot_exists_torsion h9 hcube hσ
      obtain ⟨j, hj, hψj⟩ := twCompQuot_torsion_cong hTc hNT hX hh₀N hh₀ hh₀3 hχT hχ3 hχN hψT hψ3
      refine ⟨j, hj, ?_⟩
      have h := N.mul_mem hσψ hψj
      rwa [mul_assoc, inv_mul_cancel_left] at h
    have haT : n * χ * n⁻¹ ∈ T := (hnT χ).1 hχT
    have hk1 : n * χ * n⁻¹ * χ⁻¹ ∈ N := by
      obtain ⟨k, hk, hak⟩ := hcong _ haT
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · rw [pow_zero, inv_one, mul_one] at hak
        exact absurd ((hnN χ).2 hak) hχN
      · rwa [pow_one] at hak
      · rw [inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hχ3 : χ ^ 2 * χ = 1)] at hak
        have hab := hTc _ haT _ ((hnT _).1 haT)
        exact absurd (twCompQuot_dvd_of_pow_mem hχ3 hχN
          (twCompQuot_sq_mem hnN hab hak (hn3 χ hχT))) (by norm_num)
    have hkj : ∀ j : ℕ, n * χ ^ j * n⁻¹ * (χ ^ j)⁻¹ ∈ N := by
      intro j
      have hcomm : Commute (n * χ * n⁻¹) χ⁻¹ := hTc _ haT _ (T.inv_mem hχT)
      have h := N.pow_mem hk1 j
      rwa [hcomm.mul_pow, conj_pow, inv_pow] at h
    obtain ⟨j, -, hτj⟩ := hcong τ hτ
    exact twCompQuot_comm_mem_of_mul_inv_mem hnN (hkj j) hτj
  · obtain ⟨χ, hχT, hχ3, hτχ⟩ := twCompQuot_exists_torsion h9 hcube hτ
    have hτN : τ ∈ N := by
      have h := N.mul_mem hτχ (by_contra fun h => hXN ⟨χ, hχT, hχ3, h⟩)
      rwa [inv_mul_cancel_right] at h
    exact N.mul_mem ((hnN τ).1 hτN) (N.inv_mem hτN)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
