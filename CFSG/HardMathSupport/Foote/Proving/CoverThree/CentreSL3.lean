module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Proving

public theorem natCard_center_SL3_eq_natCard_rootsOfUnity (F : Type*) [Field F] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) =
      Nat.card (rootsOfUnity 3 F) := by
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 3) (R := F)
  have h3 : max (Fintype.card (Fin 3)) 1 = 3 := by simp
  rw [h3] at e
  exact Nat.card_congr e.toEquiv

public theorem natCard_rootsOfUnity_three_of_three_dvd (F : Type*) [Field F] [Fintype F]
    (h : 3 ∣ Fintype.card F - 1) : Nat.card (rootsOfUnity 3 F) = 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Fintype.card Fˣ = Fintype.card F - 1 := Fintype.card_units F
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 (hcard ▸ h)
  have hgmem : g ∈ rootsOfUnity 3 F :=
    (mem_rootsOfUnity 3 g).2 (by rw [← hg]; exact pow_orderOf_eq_one g)
  have hge : Nat.card (Subgroup.zpowers g) ≤ Nat.card (rootsOfUnity 3 F) :=
    Subgroup.card_le_of_le ((Subgroup.zpowers_le).2 hgmem)
  rw [Nat.card_zpowers, hg] at hge
  have hle : Nat.card (rootsOfUnity 3 F) ≤ 3 := card_rootsOfUnity (k := 3) (R := F)
  omega

public theorem natCard_rootsOfUnity_three_of_not_three_dvd (F : Type*) [Field F] [Fintype F]
    (h : ¬ 3 ∣ Fintype.card F - 1) : Nat.card (rootsOfUnity 3 F) = 1 := by
  classical
  have hcard : Fintype.card Fˣ = Fintype.card F - 1 := Fintype.card_units F
  have hbot : rootsOfUnity 3 F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rw [mem_rootsOfUnity] at hx
    have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx
    have h2 : orderOf x ∣ Fintype.card F - 1 := by
      rw [← hcard, ← Nat.card_eq_fintype_card]
      exact orderOf_dvd_natCard x
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h0 | h0
    · exact orderOf_eq_one_iff.1 h0
    · exact absurd (h0 ▸ h2) h
  rw [hbot, Subgroup.card_bot]

public theorem natCard_center_SL3_field (F : Type*) [Field F] [Fintype F] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) =
      Nat.gcd 3 (Fintype.card F - 1) := by
  rw [natCard_center_SL3_eq_natCard_rootsOfUnity]
  by_cases h : 3 ∣ Fintype.card F - 1
  · rw [natCard_rootsOfUnity_three_of_three_dvd F h, Nat.gcd_eq_left h]
  · rw [natCard_rootsOfUnity_three_of_not_three_dvd F h]
    exact (show Nat.gcd 3 (Fintype.card F - 1) = 1 from
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm

public theorem natCard_PSL3_mul_gcd (F : Type*) [Field F] [Fintype F] :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) * Nat.gcd 3 (Fintype.card F - 1) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) := by
  have h := Subgroup.card_mul_index (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F))
  rw [natCard_center_SL3_field] at h
  rw [mul_comm]
  exact h

end CFSG.HardMathSupport.Foote.Proving
