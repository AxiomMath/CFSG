module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

private lemma card_le_fixed_sq {E : Type*} [CommGroup E] [Finite E]
    (hE : ∀ x : E, x * x = 1) (σ : E →* E) (hσ : ∀ x, σ (σ x) = x) :
    Nat.card E ≤ Nat.card ↥(MonoidHom.eqLocus σ (MonoidHom.id E)) ^ 2 := by
  let ν : E →* E :=
    { toFun := fun u => u * σ u
      map_one' := by simp
      map_mul' := fun u v => by
        rw [map_mul]
        exact mul_mul_mul_comm u v (σ u) (σ v) }
  have hker : ν.ker = MonoidHom.eqLocus σ (MonoidHom.id E) := by
    ext u
    rw [MonoidHom.mem_ker]
    show u * σ u = 1 ↔ σ u = u
    constructor
    · intro h
      have : σ u = u⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact (inv_eq_of_mul_eq_one_right (hE u))
    · intro h
      rw [h]
      exact hE u
  have hrange : ν.range ≤ MonoidHom.eqLocus σ (MonoidHom.id E) := by
    rintro _ ⟨u, rfl⟩
    show σ (u * σ u) = u * σ u
    rw [map_mul, hσ, mul_comm]
  have h1 := Subgroup.card_ker_mul_card_range ν
  rw [hker] at h1
  have h3 : Nat.card ν.range ≤ Nat.card ↥(MonoidHom.eqLocus σ (MonoidHom.id E)) :=
    Subgroup.card_le_of_le hrange
  rw [← h1, sq]
  exact Nat.mul_le_mul_left _ h3

theorem exists_fixed_subgroup_of_commuting_involutions {E : Type*} [CommGroup E] [Finite E]
    (hE : ∀ x : E, x * x = 1) (hcard : Nat.card E = 2 ^ 6) (α β : E →* E)
    (hα : ∀ x, α (α x) = x) (hβ : ∀ x, β (β x) = x) (hαβ : ∀ x, α (β x) = β (α x)) :
    ∃ F : Subgroup E, 4 ≤ Nat.card F ∧ ∀ x ∈ F, α x = x ∧ β x = x := by
  let C : Subgroup E := MonoidHom.eqLocus α (MonoidHom.id E)
  have hCexp : ∀ x : C, x * x = 1 := fun x => Subtype.ext (hE (x : E))
  have hβC : ∀ x : C, β (x : E) ∈ C := by
    intro x
    show α (β (x : E)) = β (x : E)
    rw [hαβ]
    exact congrArg β x.2
  let β₁ : C →* C :=
    { toFun := fun x => (⟨β (x : E), hβC x⟩ : C)
      map_one' := by
        apply Subtype.ext
        show β (1 : E) = 1
        rw [map_one]
      map_mul' := by
        intro x y
        apply Subtype.ext
        show β ((x : E) * (y : E)) = β (x : E) * β (y : E)
        rw [map_mul] }
  have hβ₁ : ∀ x : C, β₁ (β₁ x) = x := by
    intro x
    apply Subtype.ext
    show β (β (x : E)) = (x : E)
    exact hβ (x : E)
  let D : Subgroup C := MonoidHom.eqLocus β₁ (MonoidHom.id C)
  have hE_le_C : Nat.card E ≤ Nat.card C ^ 2 := card_le_fixed_sq hE α hα
  have hC_le_D : Nat.card C ≤ Nat.card D ^ 2 := card_le_fixed_sq hCexp β₁ hβ₁
  have hD4 : 2 ^ 6 ≤ Nat.card D ^ 4 := by
    calc
      2 ^ 6 = Nat.card E := hcard.symm
      _ ≤ Nat.card C ^ 2 := hE_le_C
      _ ≤ (Nat.card D ^ 2) ^ 2 := by
        rw [pow_two, pow_two]
        exact Nat.mul_le_mul hC_le_D hC_le_D
      _ = Nat.card D ^ 4 := by rw [← pow_mul]
  have hmap_card : Nat.card (D.map C.subtype) = Nat.card D :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hdvd : Nat.card D ∣ 2 ^ 6 := by
    have h := Subgroup.card_subgroup_dvd_card (D.map C.subtype)
    rwa [hmap_card, hcard] at h
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hpow : 2 ^ 6 ≤ 2 ^ (4 * k) := by
    have h := hD4
    rw [hk] at h
    rw [← pow_mul, Nat.mul_comm k 4] at h
    exact h
  have h6 : 6 ≤ 4 * k := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).1 hpow
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_not_le h)
    have h4 : 4 * k ≤ 4 := by
      simpa using Nat.mul_le_mul_left 4 hk1
    exact absurd (le_trans h6 h4) (by decide)
  have hDge4 : 4 ≤ Nat.card D := by
    rw [hk]
    calc
      4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_of_le (by decide : 1 < (2 : ℕ)) hk2
  refine ⟨D.map C.subtype, ?_, ?_⟩
  · rw [hmap_card]
    exact hDge4
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact ⟨d.2, congrArg Subtype.val hd⟩

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
