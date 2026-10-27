module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

theorem isExtraspecial_two_of_sq_comm_mem_center {P : Type*} [Group P]
    (hZ : Nat.card (center P) = 2) (hsq : ∀ x : P, x ^ 2 ∈ center P)
    (hcomm : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ center P) (hnt : ∃ x : P, x ∉ center P) :
    CFSG.IsExtraspecial 2 P where
  center_order_p := hZ
  quotient_elementary_abelian := by
    have : IsMulCommutative (P ⧸ Subgroup.center P) := ⟨⟨fun a b => by
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using hcomm b⁻¹ a⁻¹⟩⟩
    refine ⟨?_⟩
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (fun g => ?_)
    induction g using QuotientGroup.induction_on with | H g => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hsq g
  quotient_nontrivial := by
    obtain ⟨g, hg⟩ := hnt
    refine ⟨⟨1, (g : P ⧸ Subgroup.center P), ?_⟩⟩
    intro h1
    apply hg
    exact (QuotientGroup.eq_one_iff g).1 h1.symm

end CFSG.EvenSporadicStandard.HNRecog.Harada
