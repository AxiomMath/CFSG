module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameCondBasic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open CFSG.EvenSporadicStandard.Wong77.Module

namespace GoodFrame

variable {X : Type*} [Group X] (F : GoodFrame X)

theorem commute_of_mem_closure {x y : X} (hx : x ∈ Subgroup.closure (Set.range F.pt))
    (hy : y ∈ Subgroup.closure (Set.range F.pt)) : x * y = y * x := by
  have hle : Subgroup.closure (Set.range F.pt) ≤ F.φ.range :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact ⟨eVec i, rfl⟩)
  obtain ⟨u, rfl⟩ := hle hx
  obtain ⟨v, rfl⟩ := hle hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem wprod_single_add_single (i j : Fin 23) :
    F.wprod (Pi.single i 1 + Pi.single j 1) = F.pt i * F.pt j :=
  F.wprod_add _ _

theorem pt_zero_mem_closure_pairs :
    F.pt 0 ∈ Subgroup.closure {x | ∃ a ∈ Set.range F.pt, ∃ b ∈ Set.range F.pt, a * b = x} := by
  set H := Subgroup.closure {x | ∃ a ∈ Set.range F.pt, ∃ b ∈ Set.range F.pt, a * b = x}
  let K : Subgroup (Multiplicative Word) := H.comap F.φ
  have hpair : ∀ i j : Fin 23,
      Multiplicative.ofAdd (Pi.single i 1 + Pi.single j 1 : Word) ∈ K := by
    intro i j
    show F.wprod (Pi.single i 1 + Pi.single j 1) ∈ H
    rw [wprod_single_add_single]
    exact Subgroup.subset_closure ⟨F.pt i, ⟨i, rfl⟩, F.pt j, ⟨j, rfl⟩, rfl⟩
  have hsum : Multiplicative.ofAdd (allOnes + Pi.single 0 1 : Word) ∈ K := by
    have h : (allOnes + Pi.single 0 1 : Word) = ∑ k : Fin 11,
        (Pi.single (⟨2 * k.val + 1, by omega⟩ : Fin 23) 1 +
          Pi.single (⟨2 * k.val + 2, by omega⟩ : Fin 23) 1) := by
      decide
    rw [h, ofAdd_sum]
    exact Subgroup.prod_mem K fun k _ => hpair _ _
  have hsum' : F.wprod (allOnes + Pi.single 0 1) ∈ H := hsum
  rw [F.wprod_add, F.wprod_allOnes, one_mul] at hsum'
  exact hsum'

theorem closure_range_pt_eq :
    Subgroup.closure (Set.range F.pt) =
      Subgroup.closure {x | ∃ a ∈ Set.range F.pt, ∃ b ∈ Set.range F.pt, a * b = x} := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨i, rfl⟩
    have h1 : F.pt i * F.pt 0 ∈
        Subgroup.closure {x | ∃ a ∈ Set.range F.pt, ∃ b ∈ Set.range F.pt, a * b = x} :=
      Subgroup.subset_closure ⟨F.pt i, ⟨i, rfl⟩, F.pt 0, ⟨0, rfl⟩, rfl⟩
    have := mul_mem h1 F.pt_zero_mem_closure_pairs
    rwa [mul_assoc, F.pt_mul_self, mul_one] at this
  · rintro _ ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    exact mul_mem (Subgroup.subset_closure ⟨i, rfl⟩) (Subgroup.subset_closure ⟨j, rfl⟩)

theorem pair_eq_of_single_add_eq {i j i' j' : Fin 23} (hij : i ≠ j)
    (h : (Pi.single i 1 + Pi.single j 1 : Word) = Pi.single i' 1 + Pi.single j' 1) :
    (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  have hi : i = i' ∨ i = j' := by
    by_contra hcon
    push Not at hcon
    have := congrFun h i
    simp [hij, hcon.1, hcon.2] at this
  have hj : j = i' ∨ j = j' := by
    by_contra hcon
    push Not at hcon
    have := congrFun h j
    simp [hij.symm, hcon.1, hcon.2] at this
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact absurd (hi.trans hj.symm) hij
  · exact Or.inl ⟨hi, hj⟩
  · exact Or.inr ⟨hi, hj⟩
  · exact absurd (hi.trans hj.symm) hij

theorem pair_inj : ∀ a ∈ Set.range F.pt, ∀ b ∈ Set.range F.pt, ∀ a' ∈ Set.range F.pt,
    ∀ b' ∈ Set.range F.pt, a ≠ b → a' ≠ b' → a * b = a' * b' →
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨i', rfl⟩ _ ⟨j', rfl⟩ hne _ hab
  have hij : i ≠ j := fun h => hne (by rw [h])
  have hw : (Pi.single i 1 + Pi.single j 1 : Word) = Pi.single i' 1 + Pi.single j' 1 := by
    refine F.eq_of_wprod_eq ?_ ?_
    · rw [wprod_single_add_single, wprod_single_add_single]
      exact hab
    · have h1 := hammingNorm_add_single_le (Pi.single i 1) j
      have h2 := hammingNorm_add_single_le (Pi.single i' 1) j'
      rw [hammingNorm_single] at h1 h2
      omega
  rcases pair_eq_of_single_add_eq hij hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

theorem closure_ne_range :
    {x | x ∈ Subgroup.closure (Set.range F.pt) ∧ x ≠ 1} ≠ Set.range F.pt := by
  intro h
  have hx : F.pt 0 * F.pt 1 ∈ {x | x ∈ Subgroup.closure (Set.range F.pt) ∧ x ≠ 1} := by
    refine ⟨mul_mem (Subgroup.subset_closure ⟨0, rfl⟩) (Subgroup.subset_closure ⟨1, rfl⟩),
      fun h1 => ?_⟩
    have hw := F.eq_of_wprod_eq (v := Pi.single 0 1 + Pi.single 1 1) (w := 0)
      (by rw [wprod_single_add_single, F.wprod_zero]; exact h1) (by
        have h2 := hammingNorm_add_single_le (Pi.single 0 1) 1
        rw [hammingNorm_single] at h2
        rw [hammingNorm_zero]
        omega)
    have := congrFun hw 0
    simp at this
  rw [h] at hx
  obtain ⟨m, hm⟩ := hx
  have hw := F.eq_of_wprod_eq (v := Pi.single m 1) (w := Pi.single 0 1 + Pi.single 1 1)
    (by rw [wprod_single_add_single]; exact hm) (by
      have h2 := hammingNorm_add_single_le (Pi.single 0 1) 1
      rw [hammingNorm_single] at h2
      rw [hammingNorm_single]
      omega)
  have h0 : m = 0 := by
    by_contra hne
    have := congrFun hw 0
    simp [Ne.symm hne] at this
  have h1 : m = 1 := by
    by_contra hne
    have := congrFun hw 1
    simp [Ne.symm hne] at this
  exact absurd (h0.symm.trans h1) (by decide)

end GoodFrame

end CFSG.EvenSporadicStandard.TwoFi22
