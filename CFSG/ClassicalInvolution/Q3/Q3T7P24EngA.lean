module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A01
public import CFSG.ClassicalInvolution.Asc77.AscT7EInv

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7E
open CFSG.ClassicalInvolution.Asc77.T7E
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem involution_cases_of {K K' : Subgroup G} {z : G} (hΩ : HypOmegaMod Ω) (hK : K ∈ Ω)
    (hK'tw : K' ∈ twinSet Ω K) (hKK' : K' ≠ K) (hz : IsUniqueInvolution K z)
    {S : Sylow 2 G} {R R' : Subgroup G} (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hRS : R ≤ (S : Subgroup G)) (hR'S : R' ≤ (S : Subgroup G)) {b b' u : G} (hb : b ∈ R)
    (hb' : b' ∈ R') (ob : orderOf b = 4) (ob' : orderOf b' = 4) (huK : u ∈ K ⊔ K')
    (huS : u ∈ (S : Subgroup G)) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hub : u * b = b * u) (hub' : u * b' = b' * u) : u = b * b' ∨ u = z * (b * b') := by
  have hK' : K' ∈ Ω := hK'tw.1
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'tw
  have hRK : R ≤ K := hR.1
  have hR'K' : R' ≤ K' := hR'.1
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hKK'.symm hz hz' hRK hR'K'
    (S.isPGroup'.to_le (sup_le hRS hR'S))

  have hsyl : IsSylow2In (R ⊔ R') (K ⊔ K') := T7A.isSylow2In_sup_of_twin hΩ hK hK' hKK' hz hz'
    hR hR' hc
  have hle : R ⊔ R' ≤ (S : Subgroup G) ⊓ (K ⊔ K') := le_inf (sup_le hRS hR'S) hsyl.1
  have hpg : IsPGroup 2 ↥((S : Subgroup G) ⊓ (K ⊔ K')) := S.isPGroup'.to_le inf_le_left
  have heq : (S : Subgroup G) ⊓ (K ⊔ K') = R ⊔ R' := hsyl.2.2 _ inf_le_right hpg hle
  have huRR : u ∈ R ⊔ R' := heq ▸ (⟨huS, huK⟩ : u ∈ (S : Subgroup G) ⊓ (K ⊔ K'))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left R R'
    (T7A.le_normalizer_of_commutes hc)] at huRR
  obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := huRR
  have hρK : ρ ∈ K := hRK hρ
  have hρ'K : ρ' ∈ K' := hR'K' hρ'
  have hc1 : ρ * ρ' = ρ' * ρ := hc ρ hρ ρ' hρ'
  have hbK : b ∈ K := hRK hb
  have hb'K : b' ∈ K' := hR'K' hb'
  have hbb : b * b = z := T7A.sq_eq_of_orderOf_four hz hbK ob
  have hb'b' : b' * b' = z := T7A.sq_eq_of_orderOf_four hz' hb'K ob'
  have hz2 : z * z = 1 := hz.sq
  have hzc : ∀ x ∈ K, z * x = x * z := fun x hx => hz.commute_of_mem hx
  have hzc' : ∀ x ∈ K', z * x = x * z := fun x hx => hz'.commute_of_mem hx

  have hsq : (ρ * ρ) * (ρ' * ρ') = 1 := by
    calc (ρ * ρ) * (ρ' * ρ') = (ρ * ρ') * (ρ * ρ') := by
          calc (ρ * ρ) * (ρ' * ρ') = ρ * (ρ * ρ') * ρ' := by group
            _ = ρ * (ρ' * ρ) * ρ' := by rw [hc1]
            _ = (ρ * ρ') * (ρ * ρ') := by group
      _ = 1 := hu2

  have hρ2 : (ρ * ρ) * (ρ * ρ) = 1 := by
    have hmem : ρ * ρ ∈ K' := by
      have : ρ * ρ = (ρ' * ρ')⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact K'.inv_mem (K'.mul_mem hρ'K hρ'K)
    have hA : IsPGroup 2 (Subgroup.zpowers (ρ * ρ)) :=
      (hR.2.1).to_le (Subgroup.zpowers_le.mpr (R.mul_mem hρ hρ))
    have hcard := hΩ.card_le_two_of_le_inf hK hK' hKK'.symm hA
      (Subgroup.zpowers_le.mpr (K.mul_mem hρK hρK)) (Subgroup.zpowers_le.mpr hmem)
    rw [Nat.card_zpowers] at hcard
    have hdvd : orderOf (ρ * ρ) ∣ 2 := by
      have h2 : orderOf (ρ * ρ) = 1 ∨ orderOf (ρ * ρ) = 2 := by
        have := orderOf_pos (ρ * ρ)
        omega
      rcases h2 with h | h
      · rw [h]; exact one_dvd 2
      · rw [h]
    have := orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [pow_two] at this
    exact this
  rcases hz.unique (ρ * ρ) (K.mul_mem hρK hρK) hρ2 with h1 | h1
  ·
    exfalso
    have hρ'2 : ρ' * ρ' = 1 := by rw [h1, one_mul] at hsq; exact hsq
    have e1 : ρ = 1 ∨ ρ = z := hz.unique ρ hρK h1
    have e2 : ρ' = 1 ∨ ρ' = z := hz'.unique ρ' hρ'K hρ'2
    rcases e1 with h₁ | h₁ <;> rcases e2 with h₂ | h₂
    · exact hu1 (by rw [h₁, h₂]; exact mul_one 1)
    · exact huz (by rw [h₁, h₂]; exact one_mul z)
    · exact huz (by rw [h₁, h₂]; exact mul_one z)
    · exact hu1 (by rw [h₁, h₂]; exact hz2)
  ·
    have hρ'2 : ρ' * ρ' = z := by
      rw [h1] at hsq
      have : ρ' * ρ' = z⁻¹ := eq_inv_of_mul_eq_one_right hsq
      rwa [inv_eq_of_mul_eq_one_left hz2] at this

    have hρb : ρ * b = b * ρ := by
      have h2 : ρ' * b = b * ρ' := (hc b hb ρ' hρ').symm
      have : ρ * ρ' * b = b * (ρ * ρ') := hub
      calc ρ * b = ρ * (b * ρ') * ρ'⁻¹ := by group
        _ = ρ * (ρ' * b) * ρ'⁻¹ := by rw [h2]
        _ = (ρ * ρ' * b) * ρ'⁻¹ := by group
        _ = (b * (ρ * ρ')) * ρ'⁻¹ := by rw [this]
        _ = b * ρ := by group
    have hρ'b' : ρ' * b' = b' * ρ' := by
      have h2 : ρ * b' = b' * ρ := hc ρ hρ b' hb'
      have : ρ * ρ' * b' = b' * (ρ * ρ') := hub'
      calc ρ' * b' = ρ⁻¹ * (ρ * ρ' * b') := by group
        _ = ρ⁻¹ * (b' * (ρ * ρ')) := by rw [this]
        _ = ρ⁻¹ * ((b' * ρ) * ρ') := by group
        _ = ρ⁻¹ * ((ρ * b') * ρ') := by rw [h2]
        _ = b' * ρ' := by group
    have e1 := eq_or_eq_mul_of_commute hz hbK hρK hbb h1 hρb.symm
    have e2 := eq_or_eq_mul_of_commute hz' hb'K hρ'K hb'b' hρ'2 hρ'b'.symm
    have hbz : b * z = z * b := (hzc b hbK).symm
    have hb'z : b' * z = z * b' := (hzc' b' hb'K).symm
    rcases e1 with h₁ | h₁ <;> rcases e2 with h₂ | h₂ <;> rw [h₁, h₂]
    · exact Or.inl rfl
    · right
      calc b * (z * b') = (b * z) * b' := by group
        _ = (z * b) * b' := by rw [hbz]
        _ = z * (b * b') := by group
    · right
      group
    · left
      calc z * b * (z * b') = z * (b * z) * b' := by group
        _ = z * (z * b) * b' := by rw [hbz]
        _ = (z * z) * b * b' := by group
        _ = b * b' := by rw [hz2, one_mul]
end T7E
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
