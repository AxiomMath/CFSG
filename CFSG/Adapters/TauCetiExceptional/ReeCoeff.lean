module

public import CFSG.Quasithin.Background.G2UColumns

public section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U

@[expose] def colXc (j : ℕ) (i : Fin Tag.G2.rank) : Label .G2 → Label .G2 → ℤ
  | .inl l, x => if j = 0 then ind ℤ (.inl l) x
      else if j = 1 then ((Tag.G2.cartan l i).natAbs : ℤ) * rv ℤ (Pi.single i 1) x else 0
  | .inr α, x =>
    if α.1 = Pi.single i 1 then (if j = 0 then ind ℤ (.inr α) x else 0)
    else if α.1 = -Pi.single i 1 then
      (if j = 0 then ind ℤ (.inr α) x else if j = 1 then ind ℤ (.inl i) x
        else if j = 2 then rv ℤ (Pi.single i 1) x else 0)
    else if j ≤ su i α.1 then
      ((sd i α.1 + j).choose j : ℤ) * rv ℤ (α.1 + (j : ℤ) • Pi.single i 1) x else 0

@[expose] def colYc (j : ℕ) (i : Fin Tag.G2.rank) : Label .G2 → Label .G2 → ℤ
  | .inl l, x => if j = 0 then ind ℤ (.inl l) x
      else if j = 1 then ((Tag.G2.cartan l i).natAbs : ℤ) * rv ℤ (-Pi.single i 1) x else 0
  | .inr α, x =>
    if α.1 = -Pi.single i 1 then (if j = 0 then ind ℤ (.inr α) x else 0)
    else if α.1 = Pi.single i 1 then
      (if j = 0 then ind ℤ (.inr α) x else if j = 1 then ind ℤ (.inl i) x
        else if j = 2 then rv ℤ (-Pi.single i 1) x else 0)
    else if j ≤ sd i α.1 then
      ((su i α.1 + j).choose j : ℤ) * rv ℤ (α.1 - (j : ℤ) • Pi.single i 1) x else 0

theorem su_le_three : ∀ v ∈ rootList, ∀ i, su i v ≤ 3 := by
  decide

theorem sd_le_three : ∀ v ∈ rootList, ∀ i, sd i v ≤ 3 := by
  decide

variable {R : Type*} [CommRing R]

theorem cast_ind (a x : Label .G2) : ((ind ℤ a x : ℤ) : R) = ind R a x :=
  map_ind (Int.castRingHom R) a x

theorem cast_rv (β : Fin Tag.G2.rank → ℤ) (x : Label .G2) : ((rv ℤ β x : ℤ) : R) = rv R β x :=
  map_rv (Int.castRingHom R) β x

theorem sum_range_four_of_le {n : ℕ} (hn : n ≤ 3) (f : ℕ → R) :
    ∑ j ∈ Finset.range 4, (if j ≤ n then f j else 0) = ∑ j ∈ Finset.range (n + 1), f j := by
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (show n + 1 ≤ 4 by omega))
    fun j _ hj => by rw [ite_eq_right (by simp only [Finset.mem_range] at hj; omega)]]
  exact Finset.sum_congr rfl fun j hj => by
    rw [ite_eq_left (by simp only [Finset.mem_range] at hj; omega)]

theorem colX_eq_sum (i : Fin Tag.G2.rank) (c : R) (b x : Label .G2) :
    colX R i c b x = ∑ j ∈ Finset.range 4, c ^ j * (colXc j i b x : R) := by
  rcases b with l | α
  · simp only [colX, colXc, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [cast_ind, cast_rv]
    ring
  · simp only [colX, colXc]
    by_cases h1 : α.1 = Pi.single i 1
    · simp only [h1, ite_true, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [cast_ind]
    · by_cases h2 : α.1 = -Pi.single i 1
      · simp only [h2] at h1 ⊢
        simp only [h1, ite_true, ite_false, Finset.sum_range_succ, Finset.sum_range_zero]
        norm_num [cast_ind, cast_rv]
      · simp only [h1, h2, ite_false]
        have hle := su_le_three α.1 (mem_rootList_of_isRoot α.2) i
        have e : ∀ j, c ^ j * (((if j ≤ su i α.1 then ((sd i α.1 + j).choose j : ℤ) *
            rv ℤ (α.1 + (j : ℤ) • Pi.single i 1) x else 0 : ℤ)) : R) =
            if j ≤ su i α.1 then ((sd i α.1 + j).choose j : R) * c ^ j *
              rv R (α.1 + (j : ℤ) • Pi.single i 1) x else 0 := fun j => by
          split_ifs
          · push_cast [cast_rv]
            ring
          · simp
        simp only [e]
        rw [sum_range_four_of_le hle]

theorem colY_eq_sum (i : Fin Tag.G2.rank) (c : R) (b x : Label .G2) :
    colY R i c b x = ∑ j ∈ Finset.range 4, c ^ j * (colYc j i b x : R) := by
  rcases b with l | α
  · simp only [colY, colYc, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [cast_ind, cast_rv]
    ring
  · simp only [colY, colYc]
    by_cases h1 : α.1 = -Pi.single i 1
    · simp only [h1, ite_true, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [cast_ind]
    · by_cases h2 : α.1 = Pi.single i 1
      · simp only [h2] at h1 ⊢
        simp only [h1, ite_true, ite_false, Finset.sum_range_succ, Finset.sum_range_zero]
        norm_num [cast_ind, cast_rv]
      · simp only [h1, h2, ite_false]
        have hle := sd_le_three α.1 (mem_rootList_of_isRoot α.2) i
        have e : ∀ j, c ^ j * (((if j ≤ sd i α.1 then ((su i α.1 + j).choose j : ℤ) *
            rv ℤ (α.1 - (j : ℤ) • Pi.single i 1) x else 0 : ℤ)) : R) =
            if j ≤ sd i α.1 then ((su i α.1 + j).choose j : R) * c ^ j *
              rv R (α.1 - (j : ℤ) • Pi.single i 1) x else 0 := fun j => by
          split_ifs
          · push_cast [cast_rv]
            ring
          · simp
        simp only [e]
        rw [sum_range_four_of_le hle]

end CFSG.TauCetiBridge.Ree
