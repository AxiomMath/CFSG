module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalData

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

structure ThLocalWitness2 {F : Type*} [Group F] (B A Aa : Subgroup F) (b : F) : Prop where
  Aa_le : Aa ≤ B
  Aa_comm : ∀ x ∈ Aa, ∀ y ∈ Aa, x * y = y * x
  Aa_card : Nat.card Aa = 2 ^ 8
  Aa_exp : ∀ x ∈ Aa, x ^ 4 = 1
  A_eq_sq : ∀ y, y ∈ A ↔ ∃ x ∈ Aa, x ^ 2 = y
  Aa_unique : ∀ Y : Subgroup F, Y ≤ B → (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y = 2 ^ 8 →
    Y = Aa
  b_mem : b ∈ B
  b_not_mem : b ∉ Aa
  b_sq : b ^ 2 = 1
  b_inv : ∀ x ∈ Aa, b * x * b⁻¹ = x⁻¹

variable {F F' : Type*} [Group F] [Group F']

theorem ThLocalWitness2.map_equiv (e : F ≃* F') {B A Aa : Subgroup F'} {b : F'}
    (W : ThLocalWitness2 B A Aa b) :
    ThLocalWitness2 (B.map (e.symm : F' →* F)) (A.map (e.symm : F' →* F))
      (Aa.map (e.symm : F' →* F)) (e.symm b) := by
  have hmem : ∀ K : Subgroup F', ∀ x : F, x ∈ K.map (e.symm : F' →* F) ↔ e x ∈ K := fun K x => by
    simpa using Subgroup.mem_map_equiv (f := e.symm) (K := K) (x := x)
  refine ⟨Subgroup.map_mono W.Aa_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hmem] at hx hy
    exact e.injective (by simpa using W.Aa_comm _ hx _ hy)
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact W.Aa_card
  · intro x hx
    rw [hmem] at hx
    exact e.injective (by simpa using W.Aa_exp _ hx)
  · intro y
    rw [hmem, W.A_eq_sq]
    constructor
    · rintro ⟨x', hx', hxy⟩
      refine ⟨e.symm x', (hmem Aa _).2 (by simpa using hx'), e.injective ?_⟩
      simpa using hxy
    · rintro ⟨x, hx, hxy⟩
      rw [hmem] at hx
      exact ⟨e x, hx, by rw [← hxy]; simp⟩
  · intro Y hYB hYc hYcard
    set Y' : Subgroup F' := Y.map (e : F →* F') with hY'
    have hmemY : ∀ x' : F', x' ∈ Y' ↔ e.symm x' ∈ Y := fun x' => by
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro h
        exact ⟨e.symm x', h, by simp⟩
    have h1 : Y' ≤ B := fun x' hx' => by
      have := (hmem B _).1 (hYB ((hmemY x').1 hx'))
      simpa using this
    have h2 : ∀ x ∈ Y', ∀ y ∈ Y', x * y = y * x := fun x hx y hy => by
      have := hYc _ ((hmemY x).1 hx) _ ((hmemY y).1 hy)
      simpa using congrArg e this
    have h3 : Nat.card Y' = 2 ^ 8 := by
      rw [hY', Subgroup.card_map_of_injective e.injective]
      exact hYcard
    have h4 := W.Aa_unique Y' h1 h2 h3
    ext x
    rw [hmem, ← h4, hmemY]
    simp
  · exact (hmem B _).2 (by simpa using W.b_mem)
  · intro h
    exact W.b_not_mem (by simpa using (hmem Aa _).1 h)
  · rw [← map_pow, W.b_sq, map_one]
  · intro x hx
    rw [hmem] at hx
    apply e.injective
    simpa using W.b_inv _ hx

end CFSG.EvenSporadicStandard.ThStd
