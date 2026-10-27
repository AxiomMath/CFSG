module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Orbit
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open scoped Classical

variable {G : Type*} [Group G] [Fintype G]

structure FinalData (E N : Subgroup G) (t : G) (F1 F2 F3 : Finset G) : Prop where
  card_E : Nat.card E = 64
  sq : ∀ x ∈ E, x * x = 1
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  t_mem : t ∈ E
  t_ne : t ≠ 1
  E_le : E ≤ N
  norm : ∀ n ∈ N, ∀ x ∈ E, n * x * n⁻¹ ∈ E
  cent : ∀ n ∈ N, (∀ x ∈ E, n * x = x * n) → n ∈ E
  card_N0 : Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 7680
  mem_F : ∀ x, (x ∈ F1 ∨ x ∈ F2 ∨ x ∈ F3) ↔ (x ∈ E ∧ x ≠ 1 ∧ x ≠ t)
  disj12 : Disjoint F1 F2
  disj13 : Disjoint F1 F3
  disj23 : Disjoint F2 F3
  card1 : F1.card = 30
  card2 : F2.card = 12
  card3 : F3.card = 20
  tmul1 : ∀ x ∈ F1, t * x ∈ F1
  tmul2 : ∀ x ∈ F2, t * x ∈ F2
  tmul3 : ∀ x ∈ F3, t * x ∈ F3
  trans1 : ∀ x ∈ F1, ∀ y ∈ F1,
    ∃ n ∈ N, n * t = t * n ∧ (n * x * n⁻¹ = y ∨ n * x * n⁻¹ = t * y)
  trans2 : ∀ x ∈ F2, ∀ y ∈ F2,
    ∃ n ∈ N, n * t = t * n ∧ (n * x * n⁻¹ = y ∨ n * x * n⁻¹ = t * y)
  trans3 : ∀ x ∈ F3, ∀ y ∈ F3,
    ∃ n ∈ N, n * t = t * n ∧ (n * x * n⁻¹ = y ∨ n * x * n⁻¹ = t * y)
  fix2 : ∀ n ∈ N, n * t = t * n → (∀ x ∈ F2, n * x * n⁻¹ = x) → n ∈ E
  odd1 : ∃ z ∈ F1, Odd (conjOrb N z).card ∧ Odd (conjOrb N (t * z)).card
  nonfixed : ∃ n ∈ N, n * t * n⁻¹ ≠ t
  outer : ∀ n ∈ N, n * t * n⁻¹ ≠ t → n * t * n⁻¹ ∈ F2 ∨ n * t * n⁻¹ ∈ F3

omit [Group G] [Fintype G] in
theorem pair0 {p q : Prop} [Decidable p] [Decidable q]
    (h : (if p then 1 else 0) + (if q then 1 else 0) = 0) : ¬ p ∧ ¬ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] at h ⊢

omit [Group G] [Fintype G] in
theorem pair1 {p q : Prop} [Decidable p] [Decidable q]
    (h : (if p then 1 else 0) + (if q then 1 else 0) = 1) : (p ↔ ¬ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] at h ⊢

omit [Group G] [Fintype G] in
theorem pair2 {p q : Prop} [Decidable p] [Decidable q]
    (h : (if p then 1 else 0) + (if q then 1 else 0) = 2) : p ∧ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] at h ⊢

namespace FinalData

variable {E N : Subgroup G} {t : G} {F1 F2 F3 : Finset G} (h : FinalData E N t F1 F2 F3)
include h

theorem t_sq : t * t = 1 := h.sq t h.t_mem

theorem mem_E_of_mem_conjOrb {x : G} (hx : x ∈ conjOrb N t) : x ∈ E := by
  obtain ⟨n, hn, rfl⟩ := mem_conjOrb.1 hx
  exact h.norm n hn t h.t_mem

theorem one_notMem_conjOrb : (1 : G) ∉ conjOrb N t := by
  intro hx
  obtain ⟨n, hn, h1⟩ := mem_conjOrb.1 hx
  apply h.t_ne
  have : n * t * n⁻¹ = 1 := h1.symm
  calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
    _ = 1 := by rw [this]; group

theorem conjOrb_subset {x : G} (hx : x ∈ conjOrb N t) : x = t ∨ x ∈ F2 ∨ x ∈ F3 := by
  by_cases hxt : x = t
  · exact Or.inl hxt
  · obtain ⟨n, hn, rfl⟩ := mem_conjOrb.1 hx
    exact Or.inr (h.outer n hn hxt)

theorem card_N : Nat.card N = (conjOrb N t).card * 7680 := by
  have := card_conjOrb_mul N t
  rw [h.card_N0] at this
  exact this.symm

theorem false_of_card_21 (hF2 : ∀ x ∈ F2, x ∉ conjOrb N t) (hF3 : ∀ x ∈ F3, x ∈ conjOrb N t)
    (hcard : (conjOrb N t).card = 21) : False := by
  set Ω := conjOrb N t with hΩ
  have hΩ3 : ∀ x ∈ Ω, x ≠ t → x ∈ F3 := by
    intro x hx hxt
    rcases h.conjOrb_subset hx with h1 | h1 | h1
    · exact absurd h1 hxt
    · exact absurd hx (hF2 x h1)
    · exact h1
  have hclosed : ∀ x ∈ Ω, ∀ w ∈ Ω, x * w = 1 ∨ x * w ∈ Ω := by
    intro x hx w hw
    obtain ⟨n, hn, rfl⟩ := mem_conjOrb.1 hx
    have hw' : n⁻¹ * w * n ∈ Ω := by
      have := conj_mem_conjOrb (N.inv_mem hn) hw
      simpa using this
    by_cases hwt : n⁻¹ * w * n = t
    · left
      have hw2 : w = n * t * n⁻¹ := by
        calc w = n * (n⁻¹ * w * n) * n⁻¹ := by group
          _ = n * t * n⁻¹ := by rw [hwt]
      rw [hw2]
      calc n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
        _ = 1 := by rw [h.t_sq]; group
    · right
      have h3 : n⁻¹ * w * n ∈ F3 := hΩ3 _ hw' hwt
      have h4 : t * (n⁻¹ * w * n) ∈ Ω := hF3 _ (h.tmul3 _ h3)
      have h5 := conj_mem_conjOrb hn h4
      rw [show n * t * n⁻¹ * w = n * (t * (n⁻¹ * w * n)) * n⁻¹ by group]
      exact h5
  let S : Subgroup G :=
    { carrier := {x | x = 1 ∨ x ∈ Ω}
      mul_mem' := by
        rintro a b (rfl | ha) (rfl | hb)
        · left; simp
        · right; simpa using hb
        · right; simpa using ha
        · rcases hclosed a ha b hb with h1 | h1
          · exact Or.inl h1
          · exact Or.inr h1
      one_mem' := Or.inl rfl
      inv_mem' := by
        rintro a (rfl | ha)
        · left; simp
        · right
          have : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h.sq a (h.mem_E_of_mem_conjOrb ha))
          rwa [this] }
  have hSE : S ≤ E := by
    rintro x (rfl | hx)
    · exact E.one_mem
    · exact h.mem_E_of_mem_conjOrb hx
  have hSc : Nat.card S = 22 := by
    have h1 : (S : Set G) = ↑(insert (1 : G) Ω) := by
      ext x
      simp [S]
    have h2 : Nat.card S = (S : Set G).ncard := Nat.card_coe_set_eq (S : Set G)
    rw [h2, h1, Set.ncard_coe_finset, Finset.card_insert_of_notMem h.one_notMem_conjOrb, hcard]
  have := Subgroup.card_dvd_of_le hSE
  rw [hSc, h.card_E] at this
  omega

end FinalData

omit [Fintype G] in
theorem false_of_double_count (Ω Y : Finset G) (hΩ2 : ∀ x ∈ Ω, x * x = 1)
    (hY2 : ∀ y ∈ Y, y * y = 1 ∧ y ≠ 1) (hΩc : Ω.card = 27) (hYc : Y.card = 6)
    (hW : ∀ x ∈ Ω, (Ω.filter fun w => x * w ∈ Y).card = 6) : False := by
  have h1 : ∑ x ∈ Ω, (Ω.filter fun w => x * w ∈ Y).card = 27 * 6 := by
    rw [Finset.sum_congr rfl hW]
    simp [hΩc]
  have h2 : ∀ x ∈ Ω, (Ω.filter fun w => x * w ∈ Y).card = (Y.filter fun y => x * y ∈ Ω).card := by
    intro x hx
    refine Finset.card_nbij' (fun w => x * w) (fun y => x * y) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_coe, Finset.mem_filter] at hw ⊢
      refine ⟨hw.2, ?_⟩
      rw [← mul_assoc, hΩ2 x hx, one_mul]
      exact hw.1
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
      refine ⟨hy.2, ?_⟩
      rw [← mul_assoc, hΩ2 x hx, one_mul]
      exact hy.1
    · intro w _
      simp [← mul_assoc, hΩ2 x hx]
    · intro y _
      simp [← mul_assoc, hΩ2 x hx]
  have h3 : ∑ x ∈ Ω, (Y.filter fun y => x * y ∈ Ω).card =
      ∑ y ∈ Y, (Ω.filter fun x => x * y ∈ Ω).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h4 : ∀ y ∈ Y, (Ω.filter fun x => x * y ∈ Ω).card ≤ 26 := by
    intro y hy
    have heven : Even (Ω.filter fun x => x * y ∈ Ω).card := by
      refine even_card_of_mul_right _ y (hY2 y hy).1 (hY2 y hy).2 ?_
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      refine ⟨hx.2, ?_⟩
      rw [mul_assoc, (hY2 y hy).1, mul_one]
      exact hx.1
    have hle : (Ω.filter fun x => x * y ∈ Ω).card ≤ 27 := hΩc ▸ Finset.card_filter_le _ _
    obtain ⟨k, hk⟩ := heven
    omega
  have h5 : ∑ y ∈ Y, (Ω.filter fun x => x * y ∈ Ω).card ≤ ∑ y ∈ Y, 26 := Finset.sum_le_sum h4
  have h6 : 27 * 6 = ∑ y ∈ Y, (Ω.filter fun x => x * y ∈ Ω).card := by
    rw [← h1, Finset.sum_congr rfl h2, h3]
  have h7 : ∑ y ∈ Y, 26 = 6 * 26 := by simp [hYc]
  omega

end CFSG.EvenSporadicStandard.M22Std
