module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Minor
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LieType.SpecialLinear

open Matrix
open ExteriorModel

@[expose] noncomputable def extTwistFun (n i j : ℕ) (F : Type*) [Field F] [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin n) F) :
    Matrix (Set.powersetCard (Fin n) i) (Set.powersetCard (Fin n) i) F :=
  fun s t ↦ minor ((g : Matrix (Fin n) (Fin n) F).map (iterateFrobenius F 2 j)) s t

@[expose] noncomputable def extTwist (n i j : ℕ) (F : Type*) [Field F] [CharP F 2] :
    Matrix.SpecialLinearGroup (Fin n) F →*
      Matrix (Set.powersetCard (Fin n) i) (Set.powersetCard (Fin n) i) F where
  toFun := extTwistFun n i j F
  map_one' := by
    ext s t
    simp only [extTwistFun, SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero _) (map_one _),
      minor_one, Matrix.one_apply]
  map_mul' g h := by
    ext s t
    simp only [extTwistFun, SpecialLinearGroup.coe_mul, Matrix.map_mul, minor_mul,
      Matrix.mul_apply]

variable {n i j : ℕ} {F : Type*} [Field F] [CharP F 2]

@[expose] def extUnit (n i : ℕ) (F : Type*) [Field F] (a b : Fin n) :
    Matrix (Set.powersetCard (Fin n) i) (Set.powersetCard (Fin n) i) F :=
  fun s t ↦
    if b ∈ (t : Finset (Fin n)) ∧ a ∉ (t : Finset (Fin n)) ∧
        (s : Finset (Fin n)) = insert a ((t : Finset (Fin n)).erase b) then 1 else 0

omit [CharP F 2] in
theorem minor_one_add_single_eq_extUnit (h2 : (2 : F) = 0)
    {a b : Fin n} (hab : a ≠ b) (x : F) :
    minor (1 + Matrix.single a b x : Matrix (Fin n) (Fin n) F) =
      (1 : Matrix (Set.powersetCard (Fin n) i) (Set.powersetCard (Fin n) i) F) +
        x • extUnit n i F a b := by
  ext s t
  rw [minor_one_add_single h2 hab x]
  by_cases hst : s = t
  · subst hst
    have hnot : ¬ (b ∈ (s : Finset (Fin n)) ∧ a ∉ (s : Finset (Fin n)) ∧
        (s : Finset (Fin n)) = insert a ((s : Finset (Fin n)).erase b)) := by
      rintro ⟨-, ha, heq⟩
      have hmem : a ∈ insert a ((s : Finset (Fin n)).erase b) := Finset.mem_insert_self _ _
      rw [← heq] at hmem
      exact ha hmem
    simp [extUnit, hnot, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  · rw [if_neg hst]
    by_cases hcond : b ∈ (t : Finset (Fin n)) ∧ a ∉ (t : Finset (Fin n)) ∧
        (s : Finset (Fin n)) = insert a ((t : Finset (Fin n)).erase b)
    · rw [if_pos hcond]
      simp [extUnit, hcond, hst, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    · rw [if_neg hcond]
      simp [extUnit, hcond, hst, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem extTwist_transvection {a b : Fin n} (hab : a ≠ b) (t : F) :
    extTwist n i j F (SpecialLinearGroup.transvection hab t) =
      (1 : Matrix (Set.powersetCard (Fin n) i) (Set.powersetCard (Fin n) i) F) +
        iterateFrobenius F 2 j t • extUnit n i F a b := by
  have h2 : (2 : F) = 0 := by
    have h : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
    simpa using h
  have hmap : ((SpecialLinearGroup.transvection hab t : Matrix (Fin n) (Fin n) F).map
      (iterateFrobenius F 2 j)) =
      (1 : Matrix (Fin n) (Fin n) F) + Matrix.single a b (iterateFrobenius F 2 j t) := by
    rw [SpecialLinearGroup.transvection_coe, Matrix.map_add (iterateFrobenius F 2 j) (map_add _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single]
  change extTwistFun n i j F (SpecialLinearGroup.transvection hab t) =
    (1 : Matrix (Set.powersetCard (Fin n) i) (Set.powersetCard (Fin n) i) F) +
      iterateFrobenius F 2 j t • extUnit n i F a b
  rw [show extTwistFun n i j F (SpecialLinearGroup.transvection hab t) =
      minor ((SpecialLinearGroup.transvection hab t : Matrix (Fin n) (Fin n) F).map
        (iterateFrobenius F 2 j)) from rfl]
  rw [hmap, minor_one_add_single_eq_extUnit h2 hab]



omit [CharP F 2] in
theorem extUnit_mul_extUnit {a b : Fin n} (hab : a ≠ b) :
    extUnit n i F a b * extUnit n i F b a =
      Matrix.diagonal (fun t : Set.powersetCard (Fin n) i ↦
        if a ∈ (t : Finset (Fin n)) ∧ b ∉ (t : Finset (Fin n)) then 1 else 0) := by
  classical
  ext s t
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hcond : a ∈ (t : Finset (Fin n)) ∧ b ∉ (t : Finset (Fin n))
  · have htcard : (t : Finset (Fin n)).card = i := Set.powersetCard.card_eq t
    have hcard : (insert b ((t : Finset (Fin n)).erase a)).card = i := by
      rw [Finset.card_insert_of_notMem (by simp [hcond.2]),
        Finset.card_erase_of_mem hcond.1, htcard]
      exact Nat.succ_pred_eq_of_pos (by
        rw [← htcard]
        exact Finset.card_pos.mpr ⟨a, hcond.1⟩)
    let u : Set.powersetCard (Fin n) i :=
      ⟨insert b ((t : Finset (Fin n)).erase a), hcard⟩
    have hu : (u : Finset (Fin n)) = insert b ((t : Finset (Fin n)).erase a) := rfl
    have hbu : b ∈ (u : Finset (Fin n)) := by
      rw [hu]
      exact Finset.mem_insert_self _ _
    have hau : a ∉ (u : Finset (Fin n)) := by
      rw [hu]
      simp [hab]
    have herase : (u : Finset (Fin n)).erase b = (t : Finset (Fin n)).erase a := by
      rw [hu, Finset.erase_insert (by simp [hcond.2])]
    have hfirst : extUnit n i F a b s u = if s = t then 1 else 0 := by
      have hsub : (s : Finset (Fin n)) = insert a ((u : Finset (Fin n)).erase b) ↔ s = t := by
        rw [herase, Finset.insert_erase hcond.1]
        exact ⟨Subtype.ext, fun h ↦ congrArg Subtype.val h⟩
      simp [extUnit, hbu, hau, hsub]
    have hsecond : extUnit n i F b a u t = 1 := by
      simp [extUnit, hcond, hu]
    rw [Finset.sum_eq_single u ?_ (by simp)]
    · rw [hfirst, hsecond, mul_one]
      by_cases hst : s = t <;> simp [hst, hcond]
    · intro x _ hx
      have hne : (x : Finset (Fin n)) ≠ insert b ((t : Finset (Fin n)).erase a) := by
        intro hxu
        exact hx (Subtype.ext hxu)
      have hnot : ¬ (a ∈ (t : Finset (Fin n)) ∧ b ∉ (t : Finset (Fin n)) ∧
          (x : Finset (Fin n)) = insert b ((t : Finset (Fin n)).erase a)) := by
        rintro ⟨-, -, hxeq⟩
        exact hne hxeq
      have hx2 : extUnit n i F b a x t = 0 := by
        simp [extUnit, hnot]
      rw [hx2, mul_zero]
  · rw [Finset.sum_eq_zero]
    · by_cases hst : s = t
      · subst hst
        rw [if_neg hcond]
        simp
      · rw [if_neg hst]
    · intro x _
      have hnot : ¬ (a ∈ (t : Finset (Fin n)) ∧ b ∉ (t : Finset (Fin n)) ∧
          (x : Finset (Fin n)) = insert b ((t : Finset (Fin n)).erase a)) := by
        rintro ⟨ha, hb, -⟩
        exact hcond ⟨ha, hb⟩
      have hx2 : extUnit n i F b a x t = 0 := by
        simp [extUnit, hnot]
      rw [hx2, mul_zero]

end CFSG.LieType.SpecialLinear
