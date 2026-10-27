module

public import CFSG.ClassicalInvolution.Q3.TL3LeafClass

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

theorem natCard_quot_oddCore_eq {L P : Subgroup G}
    (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) (hP : IsSylow2In P L) :
    Nat.card (↥L ⧸ classicalInvolutionOddCore ↥L) = Nat.card P := by
  have hO : Odd (Nat.card (classicalInvolutionOddCore ↥L)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥L
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hL : Nat.card ↥L = 2 ^ k * Nat.card (classicalInvolutionOddCore ↥L) := by
    rw [← hk]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hPc : Nat.card P = 2 ^ (Nat.card ↥L).factorization 2 := natCard_eq_pow_of_isSylow2In hP
  have hf : (Nat.card ↥L).factorization 2 = k := by
    have h0 : Nat.card (classicalInvolutionOddCore ↥L) ≠ 0 := Nat.card_pos.ne'
    have h1 : (Nat.card (classicalInvolutionOddCore ↥L)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hO)
        (even_iff_two_dvd.mpr h))
    rw [hL, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) h0, Finsupp.add_apply, h1,
      add_zero, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  rw [hk, hPc, hf]

noncomputable def sylowToQuot (L P : Subgroup G) :
    ↥(P.subgroupOf L) →* ↥L ⧸ classicalInvolutionOddCore ↥L :=
  (QuotientGroup.mk' (classicalInvolutionOddCore ↥L)).comp (P.subgroupOf L).subtype

theorem sylowToQuot_bijective {L P : Subgroup G}
    (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) (hP : IsSylow2In P L) :
    Function.Bijective (sylowToQuot L P) := by
  have hinj : Function.Injective (sylowToQuot L P) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : ((x : ↥L)) ∈ classicalInvolutionOddCore ↥L := (QuotientGroup.eq_one_iff _).mp hx
    have hxP : ((x : ↥L) : G) ∈ P := x.2
    have h2x : IsPGroup 2 (Subgroup.zpowers ((x : ↥L) : G)) :=
      hP.2.1.to_le (Subgroup.zpowers_le.mpr hxP)
    have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L)
      (mem_oddCoreOf_iff.mpr ⟨(x : ↥L).2, hxO⟩) h2x
    exact Subtype.ext (Subtype.ext h1)
  refine hinj.bijective_of_nat_card_le ?_
  rw [natCard_quot_oddCore_eq h2 hP]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv).symm.le

noncomputable def quotOddCoreEquiv {L P : Subgroup G}
    (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) (hP : IsSylow2In P L) :
    (↥L ⧸ classicalInvolutionOddCore ↥L) ≃* ↥P :=
  (MulEquiv.ofBijective _ (sylowToQuot_bijective h2 hP)).symm.trans
    (Subgroup.subgroupOfEquivOfLe hP.1)

theorem commOdd_of_quat {L P : Subgroup G}
    (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) (hP : IsSylow2In P L) {m : ℕ}
    [NeZero m] (e : ↥P ≃* QuaternionGroup m) {u a b : G} (hu : u ∈ L)
    (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (huu : u * u ≠ 1) (ha : a ∈ L) (hb : b ∈ L)
    (hau : a * u = u * a) (hbu : b * u = u * b) :
    a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf L := by
  let eQ : (↥L ⧸ classicalInvolutionOddCore ↥L) ≃* QuaternionGroup m :=
    (quotOddCoreEquiv h2 hP).trans e
  let φ : ↥L →* QuaternionGroup m :=
    eQ.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥L))
  have hφ1 : ∀ x : ↥L, φ x = 1 → (x : G) ∈ oddCoreOf L := by
    intro x hx
    have h1 : eQ (QuotientGroup.mk' (classicalInvolutionOddCore ↥L) x) = 1 := hx
    rw [MulEquiv.map_eq_one_iff] at h1
    exact mem_oddCoreOf_iff.mpr ⟨x.2, (QuotientGroup.eq_one_iff x).mp h1⟩
  have huu' : φ ⟨u, hu⟩ * φ ⟨u, hu⟩ ≠ 1 := by
    intro h1
    rw [← map_mul] at h1
    have h3 := hφ1 _ h1
    apply huu
    have h2' : IsPGroup 2 (Subgroup.zpowers (u * u)) :=
      hu2.to_le (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.mem_zpowers u)
        (Subgroup.mem_zpowers u)))
    exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) h3 h2'
  have hau' : φ ⟨a, ha⟩ * φ ⟨u, hu⟩ = φ ⟨u, hu⟩ * φ ⟨a, ha⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hau)
  have hbu' : φ ⟨b, hb⟩ * φ ⟨u, hu⟩ = φ ⟨u, hu⟩ * φ ⟨b, hb⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hbu)
  have hc := quaternionGroup_comm_of_comm huu' hau' hbu'
  have hc' : φ (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥L)⁻¹ * (⟨b, hb⟩ : ↥L)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc]
    group
  simpa using hφ1 _ hc'

end CFSG.ClassicalInvolution.Q3.TL4
