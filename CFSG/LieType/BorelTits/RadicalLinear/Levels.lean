module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Fintype.Prod

public section

namespace CFSG.LieType.BorelTits.RadicalLinear

variable {ι : Type*} [Fintype ι]

@[expose] noncomputable def levelsCard (ℓ : ι → ℕ) : ℕ :=
  (Finset.univ.image ℓ).card

@[expose] noncomputable def levels (ℓ : ι → ℕ) : Fin (levelsCard ℓ) ↪o ℕ :=
  (Finset.univ.image ℓ).orderEmbOfFin rfl

@[expose] noncomputable def levelCount (ℓ : ι → ℕ) (i : Fin (levelsCard ℓ)) : ℕ :=
  (Finset.univ.filter fun a => ℓ a = levels ℓ i).card

private theorem levels_eq_orderEmbOfFin (ℓ : ι → ℕ) :
    levels ℓ = (Finset.univ.image ℓ).orderEmbOfFin
      (rfl : (Finset.univ.image ℓ).card = levelsCard ℓ) :=
  rfl

private theorem range_levels (ℓ : ι → ℕ) :
    Set.range (levels ℓ) = Finset.univ.image ℓ := by
  rw [levels_eq_orderEmbOfFin]
  exact Finset.range_orderEmbOfFin _ rfl

private theorem levels_mem (ℓ : ι → ℕ) (i : Fin (levelsCard ℓ)) :
    levels ℓ i ∈ Finset.univ.image ℓ := by
  have h : levels ℓ i ∈ Set.range (levels ℓ) := Set.mem_range_self i
  rwa [range_levels] at h

private theorem sum_comp_levels {M : Type*} [AddCommMonoid M] (ℓ : ι → ℕ) (f : ℕ → M) :
    ∑ i, f (levels ℓ i) = ∑ y ∈ Finset.univ.image ℓ, f y := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ (Finset.univ.image ℓ)
    (rfl : (Finset.univ.image ℓ).card = levelsCard ℓ)]
  rw [Finset.sum_map, ← levels_eq_orderEmbOfFin]
  rfl

theorem exists_eq_levels (ℓ : ι → ℕ) (i : Fin (levelsCard ℓ)) : ∃ a, ℓ a = levels ℓ i := by
  have h := levels_mem ℓ i
  simpa using h

theorem exists_levels_eq (ℓ : ι → ℕ) (a : ι) : ∃ i, levels ℓ i = ℓ a := by
  have h : ℓ a ∈ Set.range (levels ℓ) := by
    rw [range_levels]
    exact Finset.mem_image_of_mem ℓ (Finset.mem_univ a)
  exact h

theorem one_le_levelCount (ℓ : ι → ℕ) (i : Fin (levelsCard ℓ)) : 1 ≤ levelCount ℓ i := by
  obtain ⟨a, ha⟩ := exists_eq_levels ℓ i
  rw [levelCount]
  exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩

theorem card_subtype_eq_levelCount (ℓ : ι → ℕ) (i : Fin (levelsCard ℓ)) :
    Fintype.card {a // ℓ a = levels ℓ i} = levelCount ℓ i := by
  rw [Fintype.card_subtype (fun a : ι => ℓ a = levels ℓ i)]
  rfl

theorem sum_levelCount (ℓ : ι → ℕ) : ∑ i, levelCount ℓ i = Fintype.card ι := by
  rw [show (∑ i, levelCount ℓ i) =
      ∑ i, (Finset.univ.filter fun a => ℓ a = levels ℓ i).card from rfl]
  rw [sum_comp_levels ℓ (fun y => (Finset.univ.filter fun a => ℓ a = y).card)]
  rw [← Finset.card_eq_sum_card_image ℓ Finset.univ, Finset.card_univ]

theorem two_le_levelsCard {ℓ : ι → ℕ} (h : ∃ c a, ℓ c < ℓ a) : 2 ≤ levelsCard ℓ := by
  obtain ⟨c, a, hca⟩ := h
  have h1 : ℓ c ∈ Finset.univ.image ℓ := Finset.mem_image_of_mem ℓ (Finset.mem_univ c)
  have h2 : ℓ a ∈ Finset.univ.image ℓ := Finset.mem_image_of_mem ℓ (Finset.mem_univ a)
  have hlt : 1 < levelsCard ℓ := by
    simpa [levelsCard] using
      Finset.one_lt_card.mpr ⟨ℓ c, h1, ℓ a, h2, ne_of_lt hca⟩
  omega

private theorem card_filter_lt_swap (ℓ : ι → ℕ) :
    (Finset.univ.filter fun p : ι × ι => ℓ p.1 < ℓ p.2).card =
      (Finset.univ.filter fun p : ι × ι => ℓ p.2 < ℓ p.1).card := by
  refine Finset.card_equiv (Equiv.prodComm ι ι) ?_
  intro p
  simpa [Equiv.prodComm_apply] using Iff.rfl

private theorem card_filter_eq_levels (ℓ : ι → ℕ) :
    (Finset.univ.filter fun p : ι × ι => ℓ p.1 = ℓ p.2).card =
      ∑ i, levelCount ℓ i ^ 2 := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun p : ι × ι => ℓ p.1 = ℓ p.2)
    (t := Finset.univ.image ℓ) (f := fun p : ι × ι => ℓ p.1)
    (fun p _ => Finset.mem_image_of_mem ℓ (Finset.mem_univ p.1))
  rw [hfib]
  rw [show (∑ i, levelCount ℓ i ^ 2) =
      ∑ i, (Finset.univ.filter fun a => ℓ a = levels ℓ i).card ^ 2 from rfl]
  rw [sum_comp_levels ℓ
    (fun y => (Finset.univ.filter fun a => ℓ a = y).card ^ 2)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hset : (Finset.univ.filter fun p : ι × ι => ℓ p.1 = ℓ p.2).filter
        (fun p => ℓ p.1 = y) =
      (Finset.univ.filter fun a => ℓ a = y) ×ˢ
        (Finset.univ.filter fun a => ℓ a = y) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨h12, h1y⟩
      exact ⟨h1y, by rw [← h12]; exact h1y⟩
    · rintro ⟨h1y, h2y⟩
      exact ⟨h1y.trans h2y.symm, h1y⟩
  rw [hset, Finset.card_product, sq]

theorem card_filter_lt (ℓ : ι → ℕ) :
    (Finset.univ.filter fun p : ι × ι => ℓ p.1 < ℓ p.2).card =
      (Fintype.card ι ^ 2 - ∑ i, levelCount ℓ i ^ 2) / 2 := by
  classical
  set A : ℕ := (Finset.univ.filter fun p : ι × ι => ℓ p.1 < ℓ p.2).card with hA
  set B : ℕ := (Finset.univ.filter fun p : ι × ι => ℓ p.2 < ℓ p.1).card with hB
  set D : ℕ := (Finset.univ.filter fun p : ι × ι => ℓ p.1 = ℓ p.2).card with hD
  set E : ℕ := ∑ i, levelCount ℓ i ^ 2 with hE
  have hAB : A = B := by
    rw [hA, hB]
    exact card_filter_lt_swap ℓ
  have hDE : D = E := by
    rw [hD, hE]
    exact card_filter_eq_levels ℓ
  have hsum : A + B + D = Fintype.card ι ^ 2 := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ι × ι))) (p := fun p : ι × ι => ℓ p.1 < ℓ p.2)
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ.filter fun p : ι × ι => ¬ ℓ p.1 < ℓ p.2))
      (p := fun p : ι × ι => ℓ p.2 < ℓ p.1)
    have hB' : (Finset.univ.filter fun p : ι × ι => ¬ ℓ p.1 < ℓ p.2).filter
        (fun p => ℓ p.2 < ℓ p.1) =
        (Finset.univ.filter fun p : ι × ι => ℓ p.2 < ℓ p.1) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro p _
      omega
    have hD' : (Finset.univ.filter fun p : ι × ι => ¬ ℓ p.1 < ℓ p.2).filter
        (fun p => ¬ ℓ p.2 < ℓ p.1) =
        (Finset.univ.filter fun p : ι × ι => ℓ p.1 = ℓ p.2) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro p _
      omega
    rw [hB', hD'] at h2
    rw [← hA] at h1
    rw [← hB, ← hD] at h2
    rw [← h2, Finset.card_univ] at h1
    have hcard : Fintype.card (ι × ι) = Fintype.card ι ^ 2 := by
      rw [Fintype.card_prod, pow_two]
    omega
  have h2A : A * 2 = Fintype.card ι ^ 2 - E := by omega
  calc
    A = A * 2 / 2 := by rw [Nat.mul_div_cancel A (n := 2) (by omega)]
    _ = (Fintype.card ι ^ 2 - E) / 2 := by rw [h2A]
    _ = (Fintype.card ι ^ 2 - ∑ i, levelCount ℓ i ^ 2) / 2 := by rw [hE]

theorem levels_zero_le {ℓ : ι → ℕ} (h : 0 < levelsCard ℓ) (a : ι) : levels ℓ ⟨0, h⟩ ≤ ℓ a := by
  obtain ⟨j, hj⟩ := exists_levels_eq ℓ a
  rw [← hj]
  haveI : NeZero (levelsCard ℓ) := ⟨by omega⟩
  exact (levels ℓ).le_iff_le.mpr (Fin.zero_le j)

theorem le_levels_last {ℓ : ι → ℕ} (h : 0 < levelsCard ℓ) (a : ι) :
    ℓ a ≤ levels ℓ ⟨levelsCard ℓ - 1, Nat.sub_lt h Nat.one_pos⟩ := by
  obtain ⟨j, hj⟩ := exists_levels_eq ℓ a
  rw [← hj]
  exact (levels ℓ).le_iff_le.mpr (by
    rw [Fin.le_iff_val_le_val]
    simp only [Fin.val_mk]
    omega)

end CFSG.LieType.BorelTits.RadicalLinear
