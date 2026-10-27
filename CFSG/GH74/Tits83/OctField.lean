module

public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ5
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.Tits83

universe u

section Field

variable {G : Type u} [Group G]

structure OctField (U : ℤ → Subgroup G) where
  K : Type u
  [fld : Field K]
  σ : K →+* K
  σ_sq : ∀ t, σ (σ t) = t ^ 2
  X : ℤ → K → G
  X' : ℤ → K → G
  X_mem : ∀ j t, X j t ∈ U j
  X'_mem : ∀ j t, Even j → X' j t ∈ U j
  bij_odd : ∀ j, Odd j → Function.Bijective (fun t => (⟨X j t, X_mem j t⟩ : U j))
  bij_even : ∀ j (hj : Even j), Function.Bijective
    (fun p : K × K =>
      (⟨X j p.1 * X' j p.2, (U j).mul_mem (X_mem j p.1) (X'_mem j p.2 hj)⟩ : U j))

attribute [instance] OctField.fld

theorem OctField.charP {U : ℤ → Subgroup G} (c : OctField U) : CharP c.K 2 := by
  have h2 : (2 : c.K) = 0 := by
    have h := c.σ_sq 2
    rw [map_ofNat, map_ofNat] at h
    linear_combination -h
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)

theorem OctField.finite [Finite G] {U : ℤ → Subgroup G} (c : OctField U) : Finite c.K :=
  Finite.of_injective _ (c.bij_odd 1 odd_one).1

theorem OctField.one_lt_card [Finite G] {U : ℤ → Subgroup G} (c : OctField U) :
    1 < Nat.card c.K := by
  haveI := c.finite
  exact (Finite.one_lt_card_iff_nontrivial).2 inferInstance

theorem OctField.exists_odd [Finite G] {U : ℤ → Subgroup G} (c : OctField U) :
    ∃ f : ℕ, Odd f ∧ Nat.card c.K = 2 ^ f := by
  haveI := c.finite
  haveI := c.charP
  haveI := Fintype.ofFinite c.K
  by_cases h2 : 2 < Nat.card c.K
  · obtain ⟨a, -, ha, -⟩ :=
      CFSG.Quasithin.Ch3E213M.G41.CTwo.exists_eq_pow_of_comp_eq_sq c.σ c.σ_sq h2
    exact ⟨2 * a + 1, odd_two_mul_add_one a, ha⟩
  · have h1 := c.one_lt_card
    exact ⟨1, odd_one, by omega⟩

theorem OctField.card_odd {U : ℤ → Subgroup G} (c : OctField U) {j : ℤ} (hj : Odd j) :
    Nat.card (U j) = Nat.card c.K :=
  (Nat.card_eq_of_bijective _ (c.bij_odd j hj)).symm

theorem OctField.card_even {U : ℤ → Subgroup G} (c : OctField U) {j : ℤ} (hj : Even j) :
    Nat.card (U j) = Nat.card c.K ^ 2 := by
  rw [pow_two, ← Nat.card_prod]
  exact (Nat.card_eq_of_bijective _ (c.bij_even j hj)).symm

theorem OctField.parity_absurd [Finite G] {G' : Type u} [Group G'] [Finite G']
    {U : ℤ → Subgroup G} {U' : ℤ → Subgroup G'} (c : OctField U) (c' : OctField U')
    (h1 : Nat.card c.K = Nat.card c'.K ^ 2) (h2 : Nat.card c.K ^ 2 = Nat.card c'.K) : False := by
  have hk := c.one_lt_card
  have e : Nat.card c.K = Nat.card c.K ^ 4 := by
    calc Nat.card c.K = Nat.card c'.K ^ 2 := h1
      _ = (Nat.card c.K ^ 2) ^ 2 := by rw [h2]
      _ = Nat.card c.K ^ 4 := by ring
  have : Nat.card c.K ^ 2 ≤ Nat.card c.K := by
    calc Nat.card c.K ^ 2 ≤ Nat.card c.K ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ = Nat.card c.K := e.symm
  nlinarith

end Field

end CFSG.GH74.Tits83
