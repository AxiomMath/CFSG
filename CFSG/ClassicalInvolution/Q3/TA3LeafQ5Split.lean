module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Gen

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

@[expose] def SmallG2Ne3 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f ≠ 3 ∧ LieModel F .G2 0 p f

@[expose] def SmallD4Ne3 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f ≠ 3 ∧ LieModel F .trialityD4 0 p f

@[expose] def SmallL4Ne3 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧ p ^ f ≠ 3 ∧ LieModel F .PSL 4 p f

@[expose] def SmallU4Ne3 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧ p ^ f ≠ 3 ∧ LieModel F .PSU 4 p f

@[expose] def SmallL5Ne3 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ p ^ f ≠ 3 ∧ LieModel F .PSL 5 p f

theorem SmallSimpleLeaf.g2_of_split (h₃ : SmallSimpleLeaf fun F _ => LieModel F .G2 0 3 1)
    (h : SmallSimpleLeaf SmallG2Ne3) : SmallSimpleLeaf SmallG2 := by
  refine smallSimpleLeaf_of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem SmallSimpleLeaf.d4_of_split (h₃ : SmallSimpleLeaf fun F _ => LieModel F .trialityD4 0 3 1)
    (h : SmallSimpleLeaf SmallD4Ne3) : SmallSimpleLeaf SmallD4 := by
  refine smallSimpleLeaf_of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem SmallSimpleLeaf.l4_of_split (h₃ : SmallSimpleLeaf fun F _ => LieModel F .PSL 4 3 1)
    (h : SmallSimpleLeaf SmallL4Ne3) : SmallSimpleLeaf SmallL4 := by
  refine smallSimpleLeaf_of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, hc, h3, hm⟩

theorem SmallSimpleLeaf.u4_of_split (h₃ : SmallSimpleLeaf fun F _ => LieModel F .PSU 4 3 1)
    (h : SmallSimpleLeaf SmallU4Ne3) : SmallSimpleLeaf SmallU4 := by
  refine smallSimpleLeaf_of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, hc, h3, hm⟩

theorem SmallSimpleLeaf.l5_of_split (h₃ : SmallSimpleLeaf fun F _ => LieModel F .PSL 5 3 1)
    (h : SmallSimpleLeaf SmallL5Ne3) : SmallSimpleLeaf SmallL5 := by
  refine smallSimpleLeaf_of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hc, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, hc, h3, hm⟩

end CFSG.ClassicalInvolution.Q3.TA3
