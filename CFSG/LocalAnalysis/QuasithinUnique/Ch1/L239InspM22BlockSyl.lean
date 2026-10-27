module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22BlockMax

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open scoped Pointwise
open MulAction

section Syl

variable {n : ℕ} {M : Subgroup (Equiv.Perm (Fin n))}

theorem map_stab_of_conj {B₀ : Finset (Fin n)} (α : MulAut ↥M) (g : Equiv.Perm (Fin n))
    (hαg : ∀ x : ↥M, ((α x : ↥M) : Equiv.Perm (Fin n)) = g * (x : Equiv.Perm (Fin n)) * g⁻¹) :
    (stabilizer ↥M B₀).map α.toMonoidHom = stabilizer ↥M (g • B₀) := by
  ext y
  have key : ∀ x : ↥M, (α x) • (g • B₀) = g • (x • B₀) := by
    intro x
    show ((α x : ↥M) : Equiv.Perm (Fin n)) • (g • B₀) = g • ((x : Equiv.Perm (Fin n)) • B₀)
    rw [hαg, mul_smul, mul_smul, inv_smul_smul]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_stabilizer_iff]
    show (α x) • (g • B₀) = g • B₀
    rw [key]
    have : x • B₀ = B₀ := hx
    rw [this]
  · intro hy
    refine ⟨α.symm y, (mem_stabilizer_iff.2 ?_ : α.symm y ∈ stabilizer ↥M B₀), by simp⟩
    rw [mem_stabilizer_iff] at hy
    have := key (α.symm y)
    rw [MulEquiv.apply_symm_apply, hy] at this
    exact (smul_left_cancel g this).symm

theorem factorization_two_mul (e u : ℕ) (hu : ¬ 2 ∣ u) : (2 ^ e * u).factorization 2 = e := by
  have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hu0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hu]
  simp

theorem exists_sylow_inv {B₀ : Finset (Fin n)} {H R₁ R₂ : List (Finset (Fin n))} {c₁ c₂ : ℕ}
    (h : BlockOrbits M B₀ H R₁ R₂ c₁ c₂)
    (hsame₁ : ∀ B ∈ R₁, ∀ B' ∈ R₁, ∃ q ∈ stabilizer ↥M B₀, q • B = B')
    (hsame₂ : ∀ B ∈ R₂, ∀ B' ∈ R₂, ∃ q ∈ stabilizer ↥M B₀, q • B = B')
    {e u u' : ℕ} (hX : Nat.card ↥M = 2 ^ e * u) (hu : ¬ 2 ∣ u)
    (hKc : Nat.card (stabilizer ↥M B₀) = 2 ^ e * u') (hu' : ¬ 2 ∣ u')
    (hd₁ : ¬ 2 ^ e ∣ (2 ^ e * u') / R₁.length) (hd₂ : ¬ 2 ^ e ∣ (2 ^ e * u') / R₂.length)
    (hAut : ∀ α : MulAut ↥M, ∃ B' ∈ H,
      (stabilizer ↥M B₀).map α.toMonoidHom = stabilizer ↥M B') :
    ∃ S₀ : Subgroup ↥M, IsPGroup 2 S₀ ∧ ¬ 2 ∣ S₀.index ∧
      ∀ α : MulAut ↥M, S₀.map α.toMonoidHom = S₀ →
        (stabilizer ↥M B₀).map α.toMonoidHom = stabilizer ↥M B₀ := by
  classical
  set K₀ := stabilizer ↥M B₀ with hK₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥K₀) := inferInstance
  set S₀ : Subgroup ↥M := (P : Subgroup ↥K₀).map K₀.subtype with hS₀
  have hPcard : Nat.card P = 2 ^ e := by
    rw [P.card_eq_multiplicity, hKc, factorization_two_mul e u' hu']
  have hS₀card : Nat.card S₀ = 2 ^ e := by
    rw [hS₀, Subgroup.card_map_of_injective K₀.subtype_injective]
    exact hPcard
  have hSK : S₀ ≤ K₀ := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  refine ⟨S₀, P.isPGroup'.map K₀.subtype, ?_, ?_⟩
  · have h1 := Subgroup.card_mul_index S₀
    rw [hS₀card, hX] at h1
    have h2 : S₀.index = u := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]
    exact hu
  · intro α hα
    obtain ⟨B', hB'H, hK⟩ := hAut α
    have hSle : S₀ ≤ stabilizer ↥M B' := by
      rw [← hK]
      calc S₀ = S₀.map α.toMonoidHom := hα.symm
        _ ≤ K₀.map α.toMonoidHom := Subgroup.map_mono hSK
    have hB' : B' = B₀ :=
      eq_of_sylow_fix h hsame₁ hsame₂ hKc hd₁ hd₂ hSK (hS₀card ▸ dvd_refl _) hB'H hSle
    rw [hK, hB']

end Syl

end CFSG.QuasithinUnique.Vol2Native.L239
