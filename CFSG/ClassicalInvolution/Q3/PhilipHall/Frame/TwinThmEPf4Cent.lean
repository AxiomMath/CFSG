module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotAEmpty
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotCongr
import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0C
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace TwinThmE

section Cent

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {X : Subgroup G} [X.Normal]

theorem centQuotGen (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hXc : X ≤ Subgroup.center G) (hmeet : ∀ J ∈ Ω, J ⊓ X = ⊥) : CentQuotGen Ω X :=
  CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.centQuotGen hΩ hq8 hXc hmeet

theorem q8_quot_cent
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hmeet : ∀ J ∈ Ω, J ⊓ X = ⊥) :
    ∀ L ∈ quotFamily Ω X, ∃ P : Subgroup (G ⧸ X),
      IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2) := by
  exact CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.q8_quot_cent hq8 hmeet

theorem classicalClause_quot_cent (hΩ : HypOmegaGen Ω) (hΩ' : HypOmegaGen (quotFamily Ω X))
    (hcls : Q3CL.ClassicalClause Ω) (hX2 : IsPGroup 2 ↥X) (hmeet : ∀ J ∈ Ω, J ⊓ X = ⊥) :
    Q3CL.ClassicalClause (quotFamily Ω X) where
  subnormal := by
    rintro _ ⟨K, hK, rfl⟩
    obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 K hK
    have hz' := AscQuot.isUniqueInvolution_map_mk (hmeet K hK) hz
    exact ⟨QuotientGroup.mk' X z, hz'.mem,
      orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one,
      CentQ.isSubnormal_centralizer_gen hΩ' (map_mem_quotFamily hK) hz'⟩
  commOdd := by
    rintro _ ⟨J, hJ, rfl⟩ ub ab bb hub hub2 hubb hab hbb hau hbu
    obtain ⟨u, huJ, hu, hu2⟩ := exists_isPGroup_lift_of_mem_map hub hub2
    obtain ⟨a0, ha0J, rfl⟩ := hab
    obtain ⟨b0, hb0J, rfl⟩ := hbb
    subst hu
    have huu : u * u ≠ 1 := fun h => hubb (by rw [← map_mul, h, map_one])
    have hcl : ∀ a ∈ J, QuotientGroup.mk' X a * QuotientGroup.mk' X u =
        QuotientGroup.mk' X u * QuotientGroup.mk' X a → a * u = u * a := by
      intro a haJ hc
      have hx : a * u * a⁻¹ * u⁻¹ ∈ J ⊓ X := by
        refine ⟨?_, ?_⟩
        · exact J.mul_mem (J.mul_mem (J.mul_mem haJ huJ) (J.inv_mem haJ)) (J.inv_mem huJ)
        · apply (QuotientGroup.eq_one_iff _).mp
          change QuotientGroup.mk' X (a * u * a⁻¹ * u⁻¹) = 1
          simp only [map_mul, map_inv]
          rw [hc]
          group
      rw [hmeet J hJ, Subgroup.mem_bot] at hx
      calc a * u = (a * u * a⁻¹ * u⁻¹) * (u * a) := by group
        _ = u * a := by rw [hx, one_mul]
    have hc := hcls.commOdd J hJ u a0 b0 huJ hu2 huu ha0J hb0J (hcl a0 ha0J hau)
      (hcl b0 hb0J hbu)
    have hodd : Odd (Nat.card ↥(X ⊓ J)) := by
      rw [inf_comm, hmeet J hJ, Subgroup.card_bot]
      exact odd_one
    have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' X) hc
    rw [← oddCoreOf_map_mk_of_odd hodd] at hmem
    simpa only [map_mul, map_inv] using hmem

theorem two_quot_cent (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hmeet : ∀ J ∈ Ω, J ⊓ X = ⊥) :
    ∀ L ∈ quotFamily Ω X, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L) := by
  exact CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.two_quot_cent h2 hmeet

end Cent

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
