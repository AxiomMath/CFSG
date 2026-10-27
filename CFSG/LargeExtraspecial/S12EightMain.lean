module

public import CFSG.LargeExtraspecial.S12EightE
public import CFSG.LargeExtraspecial.S12EightD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem timmesfeld_12_8 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 4 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.CXbar12 g = ⊥ ∨ S.IsReducible12 := by
  have hn3 : 3 ≤ S.width := by omega
  by_cases hC : S.CXbar12 g = ⊥
  · exact Or.inl hC
  right
  obtain ⟨z, hz, hz1, hz3⟩ := exists_pow_three_CXbar12 haQ hne hn3 ht htA hC
  rcases fixSpace_eq_bot_or_isReducible12 haQ hne hn3 ht htA hz hz1 hz3 with hz0 | h
  · exfalso
    obtain ⟨hzρ, hzρe⟩ := CXbar12_le_Mbar hz
    obtain ⟨x, hx, hxz⟩ : ∃ x ∈ S.Lbar g, x * z * x⁻¹ = z ^ 2 := by
      by_contra hc
      push Not at hc
      have hzC : z ∈ S.Mbar ⊓ centralizer (S.Lbar g : Set S.O) := by
        refine ⟨CXbar12_le_Mbar hz, mem_centralizer_iff.mpr fun ℓ hℓ => ?_⟩
        rcases conj_eq_or_CXbar12 haQ hne hn3 ht htA hz hz1 hz3 (S.Lbar_le_Mbar g hℓ) with
          h | h
        · calc ℓ * z = ℓ * z * ℓ⁻¹ * ℓ := by group
            _ = z * ℓ := by rw [h]
        · exact absurd h (hc ℓ hℓ)
      obtain ⟨k, hk⟩ := S.timmesfeld_12_4_2 haQ hne hn3 ⟨z, hzC⟩
      have hk' : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have h2 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
      have hcop : Nat.Coprime (orderOf z) 3 :=
        Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k (by norm_num))
      exact hz1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h2))
    by_cases hbQa : ((hzρ : G) * g) * S.z * ((hzρ : G) * g)⁻¹ ∈ S.Qa g
    · exact S.s12_eight_caseA haQ hne hn3 ht htA hz hz0 hzρ hzρe hx hxz hbQa
    · exact S.s12_eight_caseB haQ hne hn ht htA hz hz1 hz0 hz3 hzρ hzρe hx hxz hbQa
  · exact h

end Setting

end CFSG.LargeExtraspecial
