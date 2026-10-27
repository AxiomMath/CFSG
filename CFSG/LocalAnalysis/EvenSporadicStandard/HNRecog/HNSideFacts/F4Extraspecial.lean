module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial

public section

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open Subgroup

theorem isExtraspecial_two_of_central_involution {G : Type*} [Group G] {Q : Subgroup G} {z : G}
    (hzQ : z ∈ Q) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzc : ∀ y ∈ Q, z * y = y * z)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ zpowers z)
    (hsq : ∀ x ∈ Q, x ^ 2 ∈ zpowers z)
    (hcentre : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x ∈ zpowers z)
    (hnc : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x) :
    CFSG.IsExtraspecial 2 ↥Q := by
  let z' : ↥Q := ⟨z, hzQ⟩
  have hz'2 : z' ^ 2 = 1 := Subtype.ext (by simpa [z', pow_two] using hz2)
  have hz'1 : z' ≠ 1 := fun h => hz1 (by simpa [z'] using congrArg Subtype.val h)
  have hz'cent : z' ∈ Subgroup.center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hzc g.1 g.2).symm
  have hle : Subgroup.zpowers z' ≤ Subgroup.center ↥Q := Subgroup.zpowers_le.mpr hz'cent
  have hge : Subgroup.center ↥Q ≤ Subgroup.zpowers z' := by
    intro x hx
    have hxcomm : ∀ y ∈ Q, (x : G) * y = y * (x : G) := by
      intro y hy
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx (⟨y, hy⟩ : ↥Q))).symm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcentre x.1 x.2 hxcomm)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      simpa [z'] using hk⟩
  have hcenter_eq : Subgroup.center ↥Q = Subgroup.zpowers z' := le_antisymm hge hle
  have hord : orderOf z' = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hz'2 hz'1
  have hcard : Nat.card (Subgroup.center ↥Q) = 2 := by
    rw [hcenter_eq, Nat.card_zpowers, hord]
  have hcen : ∀ w : ↥Q, (w : G) ∈ Subgroup.zpowers z → w ∈ Subgroup.center ↥Q := by
    intro w hw
    rw [hcenter_eq]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      simpa [z'] using hk⟩
  have hcommQ : ∀ a b : ↥Q ⧸ Subgroup.center ↥Q, a * b = b * a := by
    intro a b
    refine QuotientGroup.induction_on a fun x => QuotientGroup.induction_on b fun y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine hcen _ ?_
    have h := hcomm (y⁻¹) (y⁻¹).2 (x⁻¹) (x⁻¹).2
    simpa [mul_assoc] using h
  have hexp : Monoid.exponent (↥Q ⧸ Subgroup.center ↥Q) ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun g => ?_
    refine QuotientGroup.induction_on g fun x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine hcen _ ?_
    simpa [pow_two] using hsq x x.2
  have hnontriv : Nontrivial (↥Q ⧸ Subgroup.center ↥Q) := by
    obtain ⟨q, hq, r, hr, hqr⟩ := hnc
    refine nontrivial_of_ne (QuotientGroup.mk (⟨q, hq⟩ : ↥Q)) 1 fun h => hqr ?_
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h
    exact (congrArg Subtype.val (h ⟨r, hr⟩)).symm
  haveI : IsMulCommutative (↥Q ⧸ Subgroup.center ↥Q) := IsMulCommutative.of_comm hcommQ
  exact ⟨hcard, CFSG.IsElementaryAbelian.mk hexp, hnontriv⟩

end CFSG.EvenSporadicStandard.HNRecog.SideF4
