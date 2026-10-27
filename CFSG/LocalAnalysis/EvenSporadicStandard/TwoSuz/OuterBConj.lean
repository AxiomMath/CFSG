module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Suz
public import Certificates.Certificate15030

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Recognition.SuzMultiplier
open CFSG.EvenSporadicStandard.HypOne.Suz (cover_suzM)
open CFSG.ComponentClassification.RankTwoSporadic.Suz (exists_conj_suzInv_zero)
open CFSG.Sporadic.Recognition.CoverTransfer (sq_eq_sq_of_conj)
open scoped commutatorElement

section Classes

theorem exists_conj_suzGenP_d_suzInv_zero :
    ∃ c ∈ suzM, c * suzInv 0 * c⁻¹ = suzGenP 3 :=
  exists_conj_suzInv_zero (suzGenP_mem 3) (orderOf_suzGenP_d Certificates.certificate15030)
    (fix1782_suzGenP_d Certificates.certificate15030)

theorem sq_class_dichotomy {L : Type} [Group L] (q : L →* suzM) {v : L} (hsq : q v * q v = 1)
    (hne : q v ≠ 1) :
    (∃ h : suzM, q v = h * suzGen suzD * h⁻¹) ∨
      ∃ c ∈ suzM, ((q v : suzM) : Equiv.Perm (Fin 1782)) = c * suzInv 1 * c⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf ((q v : suzM) : Equiv.Perm (Fin 1782)) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hne (Subtype.ext h1)
    have := congrArg Subtype.val hsq
    rwa [Subgroup.coe_mul, Subgroup.coe_one, ← sq] at this
  obtain ⟨r, hr, c, hc, hvc⟩ := cover_suzM _ (q v).2 h2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    obtain ⟨c₀, hc₀, hd⟩ := exists_conj_suzGenP_d_suzInv_zero
    refine ⟨⟨c * c₀⁻¹, suzM.mul_mem hc (suzM.inv_mem hc₀)⟩, Subtype.ext ?_⟩
    rw [hvc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    show _ = c * c₀⁻¹ * suzGenP 3 * (c * c₀⁻¹)⁻¹
    rw [← hd]
    group
  · exact Or.inr ⟨c, hc, hvc⟩

end Classes

end CFSG.EvenSporadicStandard.TwoSuz
