module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S6Perm

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

theorem s6_base_pow {A : Type*} [Group A] (a b : A) (n : ℕ) :
    (base a b) ^ n = base (a ^ n) (b ^ n) := by
  unfold base
  rw [← map_pow]
  rfl

theorem s6_tau_conj_helper {A : Type*} [Group A] (p q a b : A) :
    base p q * tau * (base a b * tau)⁻¹ = base (p * a⁻¹) (q * b⁻¹) := by
  rw [mul_inv_rev, tau_inv, base_inv, mul_assoc, ← mul_assoc tau tau (base a⁻¹ b⁻¹),
    tau_mul_tau, one_mul, base_mul_base]

theorem s6_commutator_tau {A : Type*} [Group A] (ρ a b : A) :
    base ρ 1 * (base a b * tau) * (base ρ 1)⁻¹ * (base a b * tau)⁻¹ =
      base ρ (b * ρ⁻¹ * b⁻¹) := by
  rw [conj_base_base_mul_tau, s6_tau_conj_helper]
  simp [mul_assoc]

theorem s6_commutator_base {A : Type*} [Group A] (p q a b : A) :
    base p q * base a b * (base p q)⁻¹ * (base a b)⁻¹ =
      base (p * a * p⁻¹ * a⁻¹) (q * b * q⁻¹ * b⁻¹) := by
  rw [base_inv, base_inv, base_mul_base, base_mul_base, base_mul_base]

theorem s6_comm_cube {A : Type*} [Group A] {a ρ : A} (h : (a * ρ * a⁻¹ * ρ⁻¹) ^ 3 = 1) :
    (ρ * a * ρ⁻¹ * a⁻¹) ^ 3 = 1 := by
  have : ρ * a * ρ⁻¹ * a⁻¹ = (a * ρ * a⁻¹ * ρ⁻¹)⁻¹ := by group
  rw [this, inv_pow, h, inv_one]

theorem s6_three_elt (g : Wr2 (Equiv.Perm (Fin 5))) (h3 : g ^ 3 = 1) (h1 : g ≠ 1)
    (hc : g * tau = tau * g) :
    ∃ c : Equiv.Perm (Fin 5), c ^ 3 = 1 ∧ c ≠ 1 ∧ g = base c c := by
  rcases eq_base_or_eq_base_mul_tau g with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · rw [tau_mul_base, base_mul_tau_inj] at hc
    obtain ⟨hab, -⟩ := hc
    subst hab
    refine ⟨a, ?_, ?_, rfl⟩
    · rw [s6_base_pow, ← base_one, base_injective] at h3
      exact h3.1
    · rintro rfl
      exact h1 base_one
  · have := congrArg swapChar h3
    rw [map_pow, swapChar_base_mul_tau, swapChar.map_one] at this
    exact absurd this (by decide)

theorem s6_card_perm_cent (c : Equiv.Perm (Fin 5)) (h3 : c ^ 3 = 1) (h1 : c ≠ 1) :
    Nat.card (centralizer ({c} : Set (Equiv.Perm (Fin 5)))) = 6 := by
  have h := s6_cent3_card c h3 h1
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun p => mem_centralizer_singleton_iff)),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

theorem s6_card_cent (c : Equiv.Perm (Fin 5)) (h3 : c ^ 3 = 1) (h1 : c ≠ 1) :
    Nat.card (centralizer ({base c c} : Set (Wr2 (Equiv.Perm (Fin 5))))) = 72 := by
  rw [card_centralizer_base_self, s6_card_perm_cent c h3 h1]
  norm_num

theorem s6_solvable_cent (c : Equiv.Perm (Fin 5)) (h3 : c ^ 3 = 1) (h1 : c ≠ 1) :
    Group.IsSolvable (centralizer ({base c c} : Set (Wr2 (Equiv.Perm (Fin 5))))) := by
  set H := centralizer ({base c c} : Set (Wr2 (Equiv.Perm (Fin 5)))) with hH
  let f : H →* Multiplicative (ZMod 2) := swapChar.comp H.subtype
  have hker : ∀ x y : f.ker, x * y = y * x := by
    have key : ∀ x : f.ker, ∃ p q : Equiv.Perm (Fin 5), (x : Wr2 (Equiv.Perm (Fin 5))) = base p q ∧
        p * c = c * p ∧ q * c = c * q := by
      rintro ⟨⟨x, hx⟩, hxk⟩
      have hs : swapChar x = 1 := hxk
      rcases eq_base_or_eq_base_mul_tau x with ⟨p, q, rfl⟩ | ⟨p, q, rfl⟩
      · refine ⟨p, q, rfl, ?_⟩
        have := (mem_centralizer_base_iff p q c c).1 (by
          rw [mem_centralizer_singleton_iff] at hx ⊢
          exact hx)
        exact this
      · exact absurd hs (swapChar_base_mul_tau_ne_one p q)
    intro x y
    obtain ⟨p, q, hx, hp, hq⟩ := key x
    obtain ⟨p', q', hy, hp', hq'⟩ := key y
    apply Subtype.ext
    apply Subtype.ext
    show (x : Wr2 (Equiv.Perm (Fin 5))) * y = y * x
    rw [hx, hy, base_mul_base, base_mul_base, s6_cent3_comm c h3 h1 p p' hp hp',
      s6_cent3_comm c h3 h1 q q' hq hq']
  have : Group.IsSolvable f.ker := Group.isSolvable_of_comm hker
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩)

theorem s6_solvable_of_le {c : Equiv.Perm (Fin 5)} (h3 : c ^ 3 = 1) (h1 : c ≠ 1)
    {X : Subgroup (Wr2 (Equiv.Perm (Fin 5)))} (hX : X ≤ centralizer ({base c c} : Set _)) :
    Group.IsSolvable X := by
  have := s6_solvable_cent c h3 h1
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hX)

section Bound

variable (i j : Fin 5) (hij : i ≠ j)

include hij

theorem s6_N_bound (N : Subgroup (Wr2 (Equiv.Perm (Fin 5))))
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (hQ : ∀ x ∈ N, x * base (Equiv.swap i j) (Equiv.swap i j) =
      base (Equiv.swap i j) (Equiv.swap i j) * x)
    (hconj : ∀ p q : Equiv.Perm (Fin 5), p ^ 3 = 1 → q ^ 3 = 1 →
      p * Equiv.swap i j = Equiv.swap i j * p → q * Equiv.swap i j = Equiv.swap i j * q →
      ∀ x ∈ N, base p q * x * (base p q)⁻¹ ∈ N) :
    ∀ x ∈ N, ∃ s s' : Equiv.Perm (Fin 5), (s = 1 ∨ s = Equiv.swap i j) ∧
      (s' = 1 ∨ s' = Equiv.swap i j) ∧ x = base s s' := by
  obtain ⟨ρ, hρ3, hρ1, hρσ⟩ := s6_exists_rho i j hij
  have no3 : ∀ z ∈ N, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    obtain ⟨k, hk⟩ := h2 z hz
    have hd1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have hd2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have h1ρ : ∀ x ∈ N, base ρ 1 * x * (base ρ 1)⁻¹ * x⁻¹ ∈ N := fun x hx =>
    N.mul_mem (hconj ρ 1 hρ3 (one_pow 3) hρσ (by simp) x hx) (N.inv_mem hx)
  have hρρ : ∀ x ∈ N, base ρ ρ * x * (base ρ ρ)⁻¹ * x⁻¹ ∈ N := fun x hx =>
    N.mul_mem (hconj ρ ρ hρ3 hρ3 hρσ hρσ x hx) (N.inv_mem hx)
  intro x hx
  rcases eq_base_or_eq_base_mul_tau x with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · have hc := hQ _ hx
    rw [base_mul_base, base_mul_base, base_injective] at hc
    obtain ⟨ha, hb⟩ := hc
    have hz := hρρ _ hx
    rw [s6_commutator_base] at hz
    have hz3 : (base (ρ * a * ρ⁻¹ * a⁻¹) (ρ * b * ρ⁻¹ * b⁻¹)) ^ 3 = 1 := by
      rw [s6_base_pow, ← base_one, base_injective]
      exact ⟨s6_comm_cube ((s6_factA i j hij ρ a hρ3 hρ1 hρσ ha).1),
        s6_comm_cube ((s6_factA i j hij ρ b hρ3 hρ1 hρσ hb).1)⟩
    have hz1 := no3 _ hz hz3
    rw [← base_one, base_injective] at hz1
    have hcomm : ∀ c : Equiv.Perm (Fin 5), ρ * c * ρ⁻¹ * c⁻¹ = 1 → c * ρ = ρ * c := fun c h =>
      (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h)).symm
    have hρa : a * ρ = ρ * a := hcomm a hz1.1
    have hρb : b * ρ = ρ * b := hcomm b hz1.2
    have hx4 : (base a b) ^ 4 ∈ N := N.pow_mem hx 4
    have h4 : ((base a b) ^ 4) ^ 3 = 1 := by
      rw [← pow_mul, show (4 * 3 : ℕ) = 12 from rfl, s6_base_pow, ← base_one, base_injective]
      exact ⟨((s6_factA i j hij ρ a hρ3 hρ1 hρσ ha).2 hρa).1,
        ((s6_factA i j hij ρ b hρ3 hρ1 hρσ hb).2 hρb).1⟩
    have h41 := no3 _ hx4 h4
    rw [s6_base_pow, ← base_one, base_injective] at h41
    exact ⟨a, b, ((s6_factA i j hij ρ a hρ3 hρ1 hρσ ha).2 hρa).2 h41.1,
      ((s6_factA i j hij ρ b hρ3 hρ1 hρσ hb).2 hρb).2 h41.2, rfl⟩
  · exfalso
    have hz := h1ρ _ hx
    rw [s6_commutator_tau] at hz
    have hz3 : (base ρ (b * ρ⁻¹ * b⁻¹)) ^ 3 = 1 := by
      rw [s6_base_pow, ← base_one, base_injective]
      refine ⟨hρ3, ?_⟩
      rw [conj_pow, inv_pow, hρ3, inv_one]
      group
    have hz1 := no3 _ hz hz3
    rw [← base_one, base_injective] at hz1
    exact hρ1 hz1.1

theorem s6_N_bound_e4 (N : Subgroup (Wr2 (Equiv.Perm (Fin 5))))
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (hQ : ∀ x ∈ N, x * base (Equiv.swap i j) (Equiv.swap i j) =
      base (Equiv.swap i j) (Equiv.swap i j) * x)
    (hconj : ∀ p q : Equiv.Perm (Fin 5), p ^ 3 = 1 → q ^ 3 = 1 →
      p * Equiv.swap i j = Equiv.swap i j * p → q * Equiv.swap i j = Equiv.swap i j * q →
      ∀ x ∈ N, base p q * x * (base p q)⁻¹ ∈ N)
    (hsgn : ∀ x ∈ N, sgnProd x = 1) :
    ∀ x ∈ N, x = 1 ∨ x = base (Equiv.swap i j) (Equiv.swap i j) := by
  intro x hx
  obtain ⟨s, s', hs, hs', rfl⟩ := s6_N_bound i j hij N h2 hQ hconj x hx
  have h := hsgn _ hx
  rw [sgnProd_base] at h
  have hsw : Equiv.Perm.sign (Equiv.swap i j) = -1 := Equiv.Perm.sign_swap hij
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl
  · left; exact base_one
  · rw [hsw] at h; simp at h
  · rw [hsw] at h; simp at h
  · right; rfl

theorem s6_card_le (N : Subgroup (Wr2 (Equiv.Perm (Fin 5))))
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (hQ : ∀ x ∈ N, x * base (Equiv.swap i j) (Equiv.swap i j) =
      base (Equiv.swap i j) (Equiv.swap i j) * x)
    (hconj : ∀ p q : Equiv.Perm (Fin 5), p ^ 3 = 1 → q ^ 3 = 1 →
      p * Equiv.swap i j = Equiv.swap i j * p → q * Equiv.swap i j = Equiv.swap i j * q →
      ∀ x ∈ N, base p q * x * (base p q)⁻¹ ∈ N) :
    Nat.card N ≤ 4 := by
  classical
  have hsub : (N : Set (Wr2 (Equiv.Perm (Fin 5)))) ⊆
      ↑({1, base (Equiv.swap i j) 1, base 1 (Equiv.swap i j),
        base (Equiv.swap i j) (Equiv.swap i j)} : Finset (Wr2 (Equiv.Perm (Fin 5)))) := by
    intro x hx
    obtain ⟨s, s', hs, hs', rfl⟩ := s6_N_bound i j hij N h2 hQ hconj x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl
    · left; exact base_one
    · right; right; left; rfl
    · right; left; rfl
    · right; right; right; rfl
  calc Nat.card N = (N : Set (Wr2 (Equiv.Perm (Fin 5)))).ncard := Nat.card_coe_set_eq _
    _ ≤ (↑({1, base (Equiv.swap i j) 1, base 1 (Equiv.swap i j),
        base (Equiv.swap i j) (Equiv.swap i j)} : Finset (Wr2 (Equiv.Perm (Fin 5)))) :
        Set (Wr2 (Equiv.Perm (Fin 5)))).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ 4 := by
        rw [Set.ncard_coe_finset]
        exact Finset.card_le_four

theorem s6_card_le_e4 (N : Subgroup (Wr2 (Equiv.Perm (Fin 5))))
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (hQ : ∀ x ∈ N, x * base (Equiv.swap i j) (Equiv.swap i j) =
      base (Equiv.swap i j) (Equiv.swap i j) * x)
    (hconj : ∀ p q : Equiv.Perm (Fin 5), p ^ 3 = 1 → q ^ 3 = 1 →
      p * Equiv.swap i j = Equiv.swap i j * p → q * Equiv.swap i j = Equiv.swap i j * q →
      ∀ x ∈ N, base p q * x * (base p q)⁻¹ ∈ N)
    (hsgn : ∀ x ∈ N, sgnProd x = 1) :
    Nat.card N ≤ 2 := by
  classical
  have hsub : (N : Set (Wr2 (Equiv.Perm (Fin 5)))) ⊆
      ↑({1, base (Equiv.swap i j) (Equiv.swap i j)} : Finset (Wr2 (Equiv.Perm (Fin 5)))) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact s6_N_bound_e4 i j hij N h2 hQ hconj hsgn x hx
  calc Nat.card N = (N : Set (Wr2 (Equiv.Perm (Fin 5)))).ncard := Nat.card_coe_set_eq _
    _ ≤ (↑({1, base (Equiv.swap i j) (Equiv.swap i j)} : Finset (Wr2 (Equiv.Perm (Fin 5)))) :
        Set (Wr2 (Equiv.Perm (Fin 5)))).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ 2 := by
        rw [Set.ncard_coe_finset]
        exact Finset.card_le_two

end Bound

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
