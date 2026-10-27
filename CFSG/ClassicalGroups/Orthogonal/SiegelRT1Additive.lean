module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

theorem exists_ne_zero_ne_one_of_four_le_card {K : Type*} [Field K] (hq : 4 ≤ Nat.card K) :
    ∃ ε : K, ε ≠ 0 ∧ ε ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsub : ∀ s : K, s = 0 ∨ s = 1 := fun s => by
    by_cases hs : s = 0
    · exact Or.inl hs
    · exact Or.inr (hcon s hs)
  have hle : Nat.card K ≤ Nat.card Bool :=
    Nat.card_le_card_of_surjective (fun b : Bool => if b then (1 : K) else 0) fun s => by
      rcases hsub s with h | h
      · exact ⟨false, by simp [h]⟩
      · exact ⟨true, by simp [h]⟩
  have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  omega

theorem exists_pairing_eq_one_and_ne_zero_ne_one {K N : Type*} [Field K]
    [AddCommGroup N] [Module K N] {B : LinearMap.BilinForm K N} (hBnd : B.Nondegenerate)
    (hq : 4 ≤ Nat.card K) {x y : N} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    ∃ z : N, ∃ ε : K, B x z = 1 ∧ B y z = ε ∧ ε ≠ 0 ∧ ε ≠ 1 := by
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : N, B x z₀ = 1 := by
    obtain ⟨z₁, hz₁⟩ : ∃ z₁ : N, B x z₁ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (hBnd.1 x hcon)
    exact ⟨(B x z₁)⁻¹ • z₁, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hz₁]⟩
  by_cases hind : LinearIndependent K ![x, y]
  · obtain ⟨ε, hε0, hε1⟩ := exists_ne_zero_ne_one_of_four_le_card hq
    have hsurj : Function.Surjective (LinearMap.prod (B x) (B y)) := by
      rw [← LinearMap.range_eq_top]
      by_contra hne
      obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
      have hz : ∀ z : N, f (B x z, B y z) = 0 := fun z =>
        LinearMap.mem_ker.mp (hf (LinearMap.mem_range_self (LinearMap.prod (B x) (B y)) z))
      have hfp : ∀ s t : K, f (s, t) = s * f (1, 0) + t * f (0, 1) := by
        intro s t
        have hst : ((s, t) : K × K) = s • ((1 : K), (0 : K)) + t • ((0 : K), (1 : K)) := by
          ext <;> simp
        rw [hst, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have hw : f (1, 0) • x + f (0, 1) • y = 0 := by
        refine hBnd.1 _ fun z => ?_
        have h := hz z
        rw [hfp] at h
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        linear_combination h
      obtain ⟨ha, hb⟩ := LinearIndependent.pair_iff.mp hind _ _ hw
      refine hf0 (LinearMap.ext fun p => ?_)
      obtain ⟨s, t⟩ := p
      rw [LinearMap.zero_apply, hfp s t, ha, hb, mul_zero, mul_zero, add_zero]
    obtain ⟨z, hz⟩ := hsurj (1, ε)
    have hz' : (B x z, B y z) = (1, ε) := hz
    exact ⟨z, ε, (Prod.mk.inj hz').1, (Prod.mk.inj hz').2, hε0, hε1⟩
  ·
    rw [LinearIndependent.pair_iff' hx] at hind
    push Not at hind
    obtain ⟨μ, hμ⟩ := hind
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hy (by rw [← hμ, zero_smul])
    have hμ1 : μ ≠ 1 := by
      rintro rfl
      exact hxy (by rw [← hμ, one_smul])
    refine ⟨z₀, μ, hz₀, ?_, hμ0, hμ1⟩
    rw [← hμ]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hz₀, mul_one]

theorem add_of_add_of_form_ne_zero {K N V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup N] [Module K N] [FiniteDimensional K N] [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K N} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    (hq : 4 ≤ Nat.card K) (F : N → V) (h0 : F 0 = 0)
    (hadd : ∀ x y, B x y ≠ 0 → F (x + y) = F x + F y) (x y : N) :
    F (x + y) = F x + F y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hN : ∀ v : N, v + v = 0 := fun v => by rw [← two_smul K v, h2, zero_smul]
  have hV : ∀ v : V, v + v = 0 := fun v => by rw [← two_smul K v, h2, zero_smul]
  by_cases hx0 : x = 0
  · rw [hx0, zero_add, h0, zero_add]
  by_cases hy0 : y = 0
  · rw [hy0, add_zero, h0, add_zero]
  by_cases hxy : x = y
  · rw [hxy, hN y, h0, hV (F y)]
  by_cases hBxy : B x y ≠ 0
  · exact hadd x y hBxy
  push Not at hBxy
  obtain ⟨z, ε, hxz, hyz, hε0, hε1⟩ :=
    exists_pairing_eq_one_and_ne_zero_ne_one hBnd hq hx0 hy0 hxy
  have hA : B x (y + z) ≠ 0 := by
    rw [map_add, hBxy, hxz, zero_add]
    exact one_ne_zero
  have hC : B (x + y) z ≠ 0 := by
    rw [map_add, LinearMap.add_apply, hxz, hyz]
    intro h
    apply hε1
    linear_combination h - h2
  have hD : B y z ≠ 0 := by
    rw [hyz]
    exact hε0
  have e1 := hadd x (y + z) hA
  have e2 := hadd y z hD
  have e3 := hadd (x + y) z hC
  have e3' : F (x + (y + z)) = F (x + y) + F z := by
    rw [← add_assoc]
    exact e3
  have key : F (x + y) + F z = (F x + F y) + F z := by
    calc F (x + y) + F z = F (x + (y + z)) := e3'.symm
      _ = F x + F (y + z) := e1
      _ = F x + (F y + F z) := by rw [e2]
      _ = (F x + F y) + F z := (add_assoc _ _ _).symm
  exact add_right_cancel key

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
