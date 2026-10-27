module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup

theorem isExtraspecial_two_of_central_data {C : Type} [Group C] (Q : Subgroup C)
    [Q.Normal] (z : C) (hzQ : z ∈ Q) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hzc : ∀ c : C, c * z = z * c) (hsq : ∀ q ∈ Q, q * q ∈ Subgroup.zpowers z)
    (hcomm : ∀ q ∈ Q, ∀ r ∈ Q, q * r * q⁻¹ * r⁻¹ ∈ Subgroup.zpowers z)
    (hnonab : ∃ q ∈ Q, ∃ r ∈ Q, q * r ≠ r * q)
    (hirr : ∀ M : Subgroup C, M ≤ Q → (∀ c : C, ∀ y ∈ M, c * y * c⁻¹ ∈ M) →
      M ≤ Subgroup.zpowers z ∨ M = Q) :
    CFSG.IsExtraspecial 2 ↥Q := by
  have memM : ∀ y : C, y ∈ (center ↥Q).map Q.subtype ↔
      ∃ _ : y ∈ Q, ∀ q ∈ Q, q * y = y * q := by
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨y'.2, fun q hq => congrArg Subtype.val (mem_center_iff.1 hy' ⟨q, hq⟩)⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨y, hy⟩, mem_center_iff.2 fun g => Subtype.ext (h g g.2), rfl⟩
  have hMQ : (center ↥Q).map Q.subtype ≤ Q := map_subtype_le _
  have hMnorm : ∀ c : C, ∀ y ∈ (center ↥Q).map Q.subtype,
      c * y * c⁻¹ ∈ (center ↥Q).map Q.subtype := by
    intro c y hy
    obtain ⟨hyQ, hy⟩ := (memM y).1 hy
    refine (memM _).2 ⟨Normal.conj_mem inferInstance y hyQ c, fun q hq => ?_⟩
    have hq' : c⁻¹ * q * c ∈ Q := by simpa using Normal.conj_mem inferInstance q hq c⁻¹
    have h := hy _ hq'
    calc q * (c * y * c⁻¹) = c * (c⁻¹ * q * c * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * q * c)) * c⁻¹ := by rw [h]
      _ = c * y * c⁻¹ * q := by group
  have hne : (center ↥Q).map Q.subtype ≠ Q := by
    intro h
    obtain ⟨q, hq, r, hr, hqr⟩ := hnonab
    have hqM : q ∈ (center ↥Q).map Q.subtype := by rw [h]; exact hq
    obtain ⟨_, hqc⟩ := (memM q).1 hqM
    exact hqr (hqc r hr).symm
  have hzM : z ∈ (center ↥Q).map Q.subtype := (memM z).2 ⟨hzQ, fun q _ => hzc q⟩
  have hMeq : (center ↥Q).map Q.subtype = zpowers z :=
    le_antisymm ((hirr _ hMQ hMnorm).resolve_right hne) (zpowers_le.2 hzM)
  have hord : orderOf z = 2 :=
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hcard : Nat.card (center ↥Q) = 2 := by
    rw [← hord, ← Nat.card_zpowers, ← hMeq]
    exact (card_map_of_injective Q.subtype_injective).symm
  have hcen : ∀ w : ↥Q, (w : C) ∈ zpowers z → w ∈ center ↥Q := by
    intro w hw
    rw [← hMeq] at hw
    exact (mem_map_iff_mem Q.subtype_injective).1 hw
  have hcommQ : ∀ a b : ↥Q ⧸ center ↥Q, a * b = b * a := by
    intro a b
    refine QuotientGroup.induction_on a fun x => QuotientGroup.induction_on b fun y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine hcen _ ?_
    have h := hcomm (y⁻¹ : ↥Q) (y⁻¹).2 (x⁻¹ : ↥Q) (x⁻¹).2
    simpa [mul_assoc] using h
  have hexp : Monoid.exponent (↥Q ⧸ center ↥Q) ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun g => ?_
    refine QuotientGroup.induction_on g fun x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine hcen _ ?_
    simpa [pow_two] using hsq x x.2
  have hnontriv : Nontrivial (↥Q ⧸ center ↥Q) := by
    obtain ⟨q, hq, r, hr, hqr⟩ := hnonab
    refine nontrivial_of_ne (QuotientGroup.mk (⟨q, hq⟩ : ↥Q)) 1 fun h => hqr ?_
    rw [QuotientGroup.eq_one_iff, mem_center_iff] at h
    exact (congrArg Subtype.val (h ⟨r, hr⟩)).symm
  have : IsMulCommutative (↥Q ⧸ center ↥Q) := IsMulCommutative.of_comm hcommQ
  exact ⟨hcard, CFSG.IsElementaryAbelian.mk hexp, hnontriv⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81
