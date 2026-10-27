module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Triv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

section RelIndex

theorem relIndex_mul_card_of_le {Ω : Type*} [Group Ω] {C D : Subgroup Ω} (h : C ≤ D) :
    C.relIndex D * Nat.card C = Nat.card D := by
  have := Subgroup.relIndex_mul_card (H := C) (K := D)
  rwa [inf_eq_left.2 h] at this

theorem relIndex_eq_of_card {Ω Ω' : Type*} [Group Ω] [Group Ω'] [Finite Ω] [Finite Ω']
    {C D : Subgroup Ω} {C' D' : Subgroup Ω'} (h : C ≤ D) (h' : C' ≤ D')
    (hC : Nat.card C' = Nat.card C) (hD : Nat.card D' = Nat.card D) :
    C'.relIndex D' = C.relIndex D := by
  have h1 := relIndex_mul_card_of_le h
  have h2 := relIndex_mul_card_of_le h'
  rw [hC, hD] at h2
  have hpos : 0 < Nat.card C := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)

theorem relIndex_eq_one_or_eq_prime {p : ℕ} (hp : p.Prime) {Ω : Type*} [Group Ω] [Finite Ω]
    {C D : Subgroup Ω} (hD : IsPGroup p D) (hle : C.relIndex D ≤ p) :
    C.relIndex D = 1 ∨ C.relIndex D = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hD.exists_card_eq
  have hdvd : C.relIndex D ∣ p ^ n := hn ▸ Subgroup.relIndex_dvd_card C D
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · left; simpa using hk
    · right; simpa using hk
  · exfalso
    have h1 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
    have h2 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega

end RelIndex

section Lift

theorem mem_of_map_mem_of_isPGroup {A Ω : Type} [Group A] [Finite A] [Group Ω] {p : ℕ} (hp : p.Prime)
    (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker) {B D : Subgroup A} (hB : IsPGroup p B) (hDB : D ≤ B)
    {b : A} (hb : b ∈ B) (h : π b ∈ D.map π) : b ∈ D := by
  obtain ⟨d, hd, hdb⟩ := h
  have hker : d⁻¹ * b ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdb, inv_mul_cancel]
  have hbd : d⁻¹ * b ∈ B ⊓ π.ker := ⟨B.mul_mem (B.inv_mem (hDB hd)) hb, hker⟩
  rw [inf_ker_eq_bot' hp π hN hB, Subgroup.mem_bot] at hbd
  rw [← inv_mul_eq_one.1 hbd]
  exact hd

end Lift

section Omega

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem s2019OmegaLE_of_omega {p : ℕ} (hp : p.Prime) {S B D J : Subgroup Ω}
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥) (hBel : IsElemAbelian p B)
    (h : S2019Omega p S B D J) :
    B ⊓ centModSubgroup p S ≠ ⊥ → D ≤ B → B ⊓ centModSubgroup p S ≤ D →
      (B ⊓ centModSubgroup p S).relIndex D ≤ p → p ^ 2 * Nat.card D ≤ Nat.card B →
      GLAPComponent p (S ⊓ Subgroup.centralizer (D : Set Ω)) J →
      B ≤ Subgroup.normalizer (J : Set Ω) → (∀ b ∈ B, CentMod p J b ↔ b ∈ D) →
      ∀ T : Subgroup Ω, T ≤ S → IsPGroup 2 T → J ≤ Subgroup.normalizer (T : Set Ω) →
        ⁅T, J⁆ = ⊥ := by
  intro hC hDB hCD hrel hD hJ hBJ hcm T hTS hT2 hJT
  have hDp : IsPGroup p D := (isPGroup_of_isElemAbelian hBel).to_le hDB
  rcases relIndex_eq_one_or_eq_prime hp hDp hrel with h1 | h1
  · have hDC : D ≤ B ⊓ centModSubgroup p S := Subgroup.relIndex_eq_one.1 h1
    have hJS : J = S := eq_of_glaPComponent_of_le_centMod hSq hSp (hDC.trans inf_le_right) hJ
    rw [hJS] at hJT ⊢
    exact commutator_eq_bot_of_normalizer_self hSq hTS hT2 hJT
  · exact h hC hDB hCD h1 hD hJ hBJ hcm T hTS hT2 hJT

end Omega

end CFSG.LocalAnalysis.GLTheoremA.S2019

end
