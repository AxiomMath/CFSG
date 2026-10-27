module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.QTGen4.Ku

theorem orderOf_ne_nine_of_exponent_three {K : Type*} [Group K] [Finite K]
    (hmax : ∀ Q : Subgroup K, IsPGroup 3 Q → Nat.card Q ≤ 9)
    {P : Subgroup K} (hP : Nat.card P = 9) (hPexp : ∀ p ∈ P, p ^ 3 = 1) (c : K) :
    orderOf c ≠ 9 := by
  intro hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (Subgroup.zpowers c) = 9 := by rw [Nat.card_zpowers, hc]
  have hQ3 : IsPGroup 3 (Subgroup.zpowers c) := by
    rw [IsPGroup.iff_card]; exact ⟨2, by rw [hcard]; norm_num⟩
  have hP3 : IsPGroup 3 P := by
    rw [IsPGroup.iff_card]; exact ⟨2, by rw [hP]; norm_num⟩
  obtain ⟨SQ, hSQ⟩ := hQ3.exists_le_sylow
  obtain ⟨SP, hSP⟩ := hP3.exists_le_sylow
  have hSQcard : Nat.card (SQ : Subgroup K) ≤ 9 := hmax _ SQ.isPGroup'
  have hSPcard : Nat.card (SP : Subgroup K) ≤ 9 := hmax _ SP.isPGroup'
  have hQS : Subgroup.zpowers c = (SQ : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hSQ (by rw [hcard]; exact hSQcard)
  have hPS : P = (SP : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hSP (by rw [hP]; exact hSPcard)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K SQ SP
  have hcS : c ∈ (SQ : Set K) := by
    have h := Subgroup.mem_zpowers c
    rw [hQS] at h
    exact h
  have hmem' : g * c * g⁻¹ ∈ (SP : Subgroup K) := by
    rw [← hg]
    show g * c * g⁻¹ ∈ ((g • SQ : Sylow 3 K) : Set K)
    rw [Sylow.coe_smul]
    exact Set.smul_mem_smul_set hcS
  have hmem : g * c * g⁻¹ ∈ P := by
    rw [hPS]
    exact hmem'
  have hPexp' := hPexp _ hmem
  have hc3 : c ^ 3 ≠ 1 := by
    intro h3
    have hdvd : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rw [hc] at hdvd
    norm_num at hdvd
  have hconj3 : (g * c * g⁻¹) ^ 3 = 1 := hPexp'
  rw [conj_pow] at hconj3
  apply hc3
  have h := congrArg (fun y => g⁻¹ * y * g) hconj3
  simpa [mul_assoc] using h

end CFSG.GH74.QTGen4.Ku
