module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8AData

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

theorem conjTo_sq_of_conjTo {ζ z₀ m : X} (hT : ∀ g ∈ S.data.T, g ^ 4 = 1 → g ^ 2 ≠ 1 → g ^ 2 = z₀)
    (hζ4 : ζ ^ 4 = 1) (hζ2 : ζ ^ 2 ≠ 1) (hm : ConjTo S.t m) (hmζ : m * ζ = ζ * m) :
    ConjTo z₀ (ζ ^ 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := hm
  have hpow : ∀ (a b : X) (n : ℕ), (a * b * a⁻¹) ^ n = a * b ^ n * a⁻¹ := fun a b n => by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_pow]
  set ζ' := g⁻¹ * ζ * g with hζ'
  have hζ'eq : ζ' = g⁻¹ * ζ * g⁻¹⁻¹ := by rw [hζ', inv_inv]
  have hζ't : ζ' * S.t = S.t * ζ' := by
    calc ζ' * S.t = g⁻¹ * (ζ * (g * S.t * g⁻¹)) * g := by rw [hζ']; group
      _ = g⁻¹ * ((g * S.t * g⁻¹) * ζ) * g := by rw [hmζ]
      _ = S.t * ζ' := by rw [hζ']; group
  have hζ'4 : ζ' ^ 4 = 1 := by rw [hζ'eq, hpow, hζ4]; group
  have hP : IsPGroup 2 (zpowers ζ') := by
    have hdvd : orderOf ζ' ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hζ'4)
    obtain ⟨i, -, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi'])
  have hPt : zpowers ζ' ≤ centralizer ({S.t} : Set X) := by
    rw [zpowers_le, mem_centralizer_singleton_iff]
    exact hζ't
  obtain ⟨h, -, hhT⟩ := S.data.exists_conj_le_T hP hPt
  have hmem : h * ζ' * h⁻¹ ∈ S.data.T := hhT ⟨ζ', mem_zpowers _, rfl⟩
  have h4 : (h * ζ' * h⁻¹) ^ 4 = 1 := by rw [hpow, hζ'4]; group
  have h2 : (h * ζ' * h⁻¹) ^ 2 ≠ 1 := by
    rw [hpow, hζ'eq, hpow]
    intro h0
    apply hζ2
    calc ζ ^ 2 = g * h⁻¹ * (h * (g⁻¹ * ζ ^ 2 * g⁻¹⁻¹) * h⁻¹) * h * g⁻¹ := by group
      _ = 1 := by rw [h0]; group
  have hz := hT _ hmem h4 h2
  refine ⟨g * h⁻¹, ?_⟩
  rw [← hz, hpow, hζ'eq, hpow]
  group

theorem false_of_cyclic_four [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) (P : Sylow 2 X)
    {ζ z₀ : X} (hT : ∀ g ∈ S.data.T, g ^ 4 = 1 → g ^ 2 ≠ 1 → g ^ 2 = z₀)
    (hζ4 : ζ ^ 4 = 1) (hζ2 : ζ ^ 2 ≠ 1)
    (hnorm : ∀ p ∈ (P : Subgroup X), p * ζ * p⁻¹ = ζ ∨ p * ζ * p⁻¹ = ζ⁻¹)
    (htP : S.t ∈ (P : Subgroup X)) (hinv : S.t * ζ * S.t⁻¹ = ζ⁻¹)
    (hz : ¬ ConjTo z₀ (ζ ^ 2)) : False := by
  set M : Subgroup X := (P : Subgroup X) ⊓ centralizer ({ζ} : Set X) with hM
  have hMP : M ≤ P := inf_le_left
  have hne : ζ ≠ ζ⁻¹ := by
    intro h
    apply hζ2
    calc ζ ^ 2 = ζ * ζ := pow_two ζ
      _ = ζ * ζ⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel ζ
  have hmemM : ∀ p ∈ (P : Subgroup X), p ∈ M ↔ p * ζ * p⁻¹ = ζ := by
    intro p hp
    rw [hM, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      rw [h]
      group
    · intro h
      refine ⟨hp, ?_⟩
      calc p * ζ = p * ζ * p⁻¹ * p := by group
        _ = ζ * p := by rw [h]
  have hindex : M.relIndex P = 2 := by
    rw [relIndex, index_eq_two_iff]
    refine ⟨⟨S.t, htP⟩, fun b => ?_⟩
    obtain ⟨b, hb⟩ := b
    rw [mem_subgroupOf, mem_subgroupOf]
    simp only [Subgroup.coe_mul]
    rw [hmemM _ (mul_mem hb htP), hmemM _ hb]
    have hconj : b * S.t * ζ * (b * S.t)⁻¹ = (b * ζ * b⁻¹)⁻¹ := by
      calc b * S.t * ζ * (b * S.t)⁻¹ = b * (S.t * ζ * S.t⁻¹) * b⁻¹ := by group
        _ = (b * ζ * b⁻¹)⁻¹ := by rw [hinv]; group
    rw [hconj]
    rcases hnorm b hb with h | h
    · rw [h]
      exact Or.inr ⟨rfl, hne.symm⟩
    · rw [h, inv_inv]
      exact Or.inl ⟨rfl, hne.symm⟩
  refine false_of_transfer (S := S) hX P hMP hindex fun m hm hmt => ?_
  have hmζ : m * ζ = ζ * m := mem_centralizer_singleton_iff.mp hm.2
  exact hz (conjTo_sq_of_conjTo hT hζ4 hζ2 hmt hmζ)

end Sec8

end CFSG.ComponentClassification.HSFLit
