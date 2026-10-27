module

public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.EvenSporadicStandard.HypOne.Fi23

open Subgroup

variable {G : Type*} [Group G]

theorem eq_of_braid {A : Type*} [CommGroup A] {a b : A} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) ^ 3 = 1) : b = a := by
  have h1 : a ^ 3 = a := by rw [pow_succ, sq, ha, one_mul]
  have h2 : b ^ 3 = b := by rw [pow_succ, sq, hb, one_mul]
  rw [mul_pow, h1, h2] at hab
  have h3 : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
  rw [h3]
  exact inv_eq_of_mul_eq_one_right ha

theorem perfect_of_braid_tree {n : ℕ} (hn : 0 < n) (T : ℕ → G) (par : ℕ → ℕ)
    (hT2 : ∀ i < n, T i * T i = 1) (hpar : ∀ j, 1 ≤ j → j < n → par j < j)
    (hbr : ∀ j, 1 ≤ j → j < n → (T (par j) * T j) ^ 3 = 1)
    (u v : List ℕ) (hu : ∀ i ∈ u, i < n) (hv : ∀ i ∈ v, i < n)
    (hodd : u.length % 2 = 1) (heven : v.length % 2 = 0)
    (huv : (u.map T).prod = (v.map T).prod) :
    ∀ i < n, T i ∈ ⁅closure (T '' {i | i < n}), closure (T '' {i | i < n})⁆ := by
  classical
  set P : Subgroup G := closure (T '' {i | i < n}) with hP
  have hmem : ∀ i < n, T i ∈ P := fun i hi => subset_closure ⟨i, hi, rfl⟩
  let t : ℕ → ↥P := fun i => if h : i < n then ⟨T i, hmem i h⟩ else 1
  have ht : ∀ i (h : i < n), t i = ⟨T i, hmem i h⟩ := fun i h => by simp [t, h]
  let a : ℕ → Abelianization ↥P := fun i => Abelianization.of (t i)
  have ha2 : ∀ i < n, a i * a i = 1 := by
    intro i hi
    show Abelianization.of (t i) * Abelianization.of (t i) = 1
    rw [← map_mul, ht i hi]
    have : (⟨T i, hmem i hi⟩ : ↥P) * ⟨T i, hmem i hi⟩ = 1 := Subtype.ext (hT2 i hi)
    rw [this, map_one]
  have hab : ∀ j, 1 ≤ j → j < n → a j = a (par j) := by
    intro j hj1 hjn
    have hpj := hpar j hj1 hjn
    refine eq_of_braid (ha2 _ (hpj.trans hjn)) (ha2 j hjn) ?_
    show (Abelianization.of (t (par j)) * Abelianization.of (t j)) ^ 3 = 1
    rw [← map_mul, ← map_pow, ht _ (hpj.trans hjn), ht j hjn]
    have : ((⟨T (par j), hmem _ (hpj.trans hjn)⟩ : ↥P) * ⟨T j, hmem j hjn⟩) ^ 3 = 1 :=
      Subtype.ext (by simpa using hbr j hj1 hjn)
    rw [this, map_one]
  have hall : ∀ j, j < n → a j = a 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hjn
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rfl
      · rw [hab j hj hjn]
        exact ih _ (hpar j hj hjn) ((hpar j hj hjn).trans hjn)
  have hword : ∀ w : List ℕ, (∀ i ∈ w, i < n) →
      Abelianization.of (w.map t).prod = a 0 ^ w.length := by
    intro w hw
    induction w with
    | nil => simp
    | cons i w ih =>
      have hi : i < n := hw i List.mem_cons_self
      rw [List.map_cons, List.prod_cons, map_mul, ih (fun j hj => hw j (List.mem_cons_of_mem _ hj)),
        List.length_cons, pow_succ, mul_comm]
      congr 1
      exact hall i hi
  have hprod : ∀ w : List ℕ, (∀ i ∈ w, i < n) →
      (((w.map t).prod : ↥P) : G) = (w.map T).prod := by
    intro w hw
    induction w with
    | nil => simp
    | cons i w ih =>
      have hi : i < n := hw i List.mem_cons_self
      rw [List.map_cons, List.prod_cons, Subgroup.coe_mul,
        ih (fun j hj => hw j (List.mem_cons_of_mem _ hj)), List.map_cons, List.prod_cons,
        ht i hi]
  have h0 : a 0 = 1 := by
    have e1 := hword u hu
    have e2 := hword v hv
    have heq : (u.map t).prod = (v.map t).prod := Subtype.ext (by
      rw [hprod u hu, hprod v hv]
      exact huv)
    rw [heq, e2] at e1
    have h00 : a 0 * a 0 = 1 := ha2 0 hn
    have hsq : a 0 ^ 2 = 1 := by rw [sq, h00]
    have hk : v.length = 2 * (v.length / 2) := by omega
    have hl : u.length = 2 * (u.length / 2) + 1 := by omega
    have h2k : a 0 ^ v.length = 1 := by
      rw [hk, pow_mul, hsq, one_pow]
    have h2l : a 0 ^ u.length = a 0 := by
      rw [hl, pow_succ, pow_mul, hsq, one_pow, one_mul]
    rw [h2k, h2l] at e1
    exact e1.symm
  intro i hi
  have hti : t i ∈ _root_.commutator ↥P := by
    rw [← QuotientGroup.eq_one_iff (N := _root_.commutator ↥P)]
    show Abelianization.of (t i) = 1
    exact (hall i hi).trans h0
  have hmap : (_root_.commutator ↥P).map P.subtype = ⁅P, P⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← hmap]
  refine ⟨t i, hti, ?_⟩
  rw [ht i hi]
  rfl

theorem le_commutator_of_braid_tree {n : ℕ} (hn : 0 < n) (T : ℕ → G) (par : ℕ → ℕ)
    (hT2 : ∀ i < n, T i * T i = 1) (hpar : ∀ j, 1 ≤ j → j < n → par j < j)
    (hbr : ∀ j, 1 ≤ j → j < n → (T (par j) * T j) ^ 3 = 1)
    (u v : List ℕ) (hu : ∀ i ∈ u, i < n) (hv : ∀ i ∈ v, i < n)
    (hodd : u.length % 2 = 1) (heven : v.length % 2 = 0)
    (huv : (u.map T).prod = (v.map T).prod) :
    closure (T '' {i | i < n}) ≤ ⁅closure (T '' {i | i < n}), closure (T '' {i | i < n})⁆ := by
  rw [closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact perfect_of_braid_tree hn T par hT2 hpar hbr u v hu hv hodd heven huv i hi

end CFSG.EvenSporadicStandard.HypOne.Fi23
