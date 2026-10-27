module

public import CFSG.LargeExtraspecial.AS35QIxBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G]

theorem three_dvd_orderOf {y w : G} (h3 : y ^ 3 * w = w * y ^ 3) (h1 : y * w ≠ w * y) :
    3 ∣ orderOf y := by
  by_contra hndvd
  have hcop : Nat.gcd 3 (orderOf y) = 1 :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hndvd).symm)
  have hy : y ∈ zpowers (y ^ 3) := mem_zpowers_pow_iff.mpr hcop
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
  apply h1
  rw [← hk]
  exact (Commute.zpow_left h3 k).eq

theorem not_two_element {f b w : G} (hf : f * f = 1) (hb : b * b = 1)
    (h3 : (f * b) ^ 3 * w = w * (f * b) ^ 3) (h1 : (f * b) * w ≠ w * (f * b)) (n : ℕ) :
    (f * b * f⁻¹ * b⁻¹) ^ (2 ^ n) ≠ 1 := by
  intro h
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [hfi, hbi, show f * b * f * b = (f * b) ^ 2 by rw [pow_two]; group, ← pow_mul] at h
  have hd := orderOf_dvd_of_pow_eq_one h
  have h3d := (three_dvd_orderOf h3 h1).trans hd
  rw [← pow_succ'] at h3d
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d)
  omega

variable [Finite G] {S : Setting G}

namespace IxSetup

variable (T : IxSetup S)

theorem t_mem_zConj : T.t ∈ S.zConj (S.HAt T.g) :=
  S.mem_zConj_of_mem_ESet T.hgD.1 rfl

theorem z_mem_zConj : S.z ∈ S.zConj (S.HAt T.g) := Asc77.self_mem_conjIn _ _

end IxSetup

end CFSG.LargeExtraspecial.AS35QIx
