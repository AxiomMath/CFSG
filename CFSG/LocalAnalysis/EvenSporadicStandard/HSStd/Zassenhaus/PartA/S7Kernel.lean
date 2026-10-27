module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Map

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Kernel

variable {T : Type} [Group T] [Finite T]

omit [Finite T] in
theorem eq_one_of_pGroup_two_odd {V : Subgroup T} (hV : IsPGroup 2 V) {v : T} (hv : v ∈ V)
    (hodd : Odd (orderOf v)) : v = 1 := by
  obtain ⟨k, hk⟩ := hV ⟨v, hv⟩
  have hk' : v ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd : orderOf v ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rw [hi] at hodd
  have : i = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 hodd) (by rw [Nat.even_pow]; exact ⟨even_two, hne⟩)
  rw [this, pow_zero] at hi
  exact orderOf_eq_one_iff.1 hi

theorem oddCore_disjoint_of_pGroup (F : Subgroup T) [F.Normal] (hF2 : IsPGroup 2 F) :
    ∀ f ∈ F, f ∈ Open.fusionOddCore T → f = 1 := by
  intro f hf ho
  have h1 : Odd (orderOf f) :=
    Odd.of_dvd_nat (natCard_fusionOddCore_odd' T) (Subgroup.orderOf_dvd_natCard _ ho)
  exact eq_one_of_pGroup_two_odd hF2 hf h1

theorem oddCore_comm_of_pGroup (F : Subgroup T) [F.Normal] (hF2 : IsPGroup 2 F) :
    ∀ f ∈ F, ∀ a ∈ Open.fusionOddCore T, f * a = a * f := by
  intro f hf a ha
  have h1 : f * a * f⁻¹ * a⁻¹ ∈ Open.fusionOddCore T := by
    have : f * a * f⁻¹ ∈ Open.fusionOddCore T :=
      (inferInstance : (Open.fusionOddCore T).Normal).conj_mem a ha f
    exact mul_mem this (inv_mem ha)
  have h2 : f * a * f⁻¹ * a⁻¹ ∈ F := by
    have : a * f⁻¹ * a⁻¹ ∈ F := (inferInstance : F.Normal).conj_mem _ (inv_mem hf) a
    have e : f * a * f⁻¹ * a⁻¹ = f * (a * f⁻¹ * a⁻¹) := by group
    rw [e]
    exact mul_mem hf this
  have h3 := oddCore_disjoint_of_pGroup F hF2 _ h2 h1
  calc f * a = (f * a * f⁻¹ * a⁻¹) * (a * f) := by group
    _ = a * f := by rw [h3, one_mul]

theorem ker_xhatMap_le_sup (F : Subgroup T) [F.Normal] (hF2 : IsPGroup 2 F)
    (hodd : ∀ g : T, Odd (orderOf g) → ∀ f ∈ F, g * f = f * g) :
    (xhatMap F).ker ≤ F ⊔ Open.fusionOddCore T := by
  obtain ⟨K, hK⟩ : ∃ K : Subgroup T, K = (xhatMap F).ker := ⟨_, rfl⟩
  rw [← hK]
  have hKn : K.Normal := hK ▸ MonoidHom.normal_ker _
  have hFK : F ≤ K := hK ▸ le_ker_xhatMap F
  have hKeq : K = (Open.fusionOddCore (T ⧸ F)).comap (QuotientGroup.mk' F) := by
    ext x
    rw [hK, mem_ker_xhatMap]
    rfl
  have hcardK : Nat.card K = Nat.card F * Nat.card (Open.fusionOddCore (T ⧸ F)) := by
    rw [hKeq, natCard_comap_of_surjective' (QuotientGroup.mk' F) (QuotientGroup.mk'_surjective F),
      QuotientGroup.ker_mk']
  have hOodd : Odd (Nat.card (Open.fusionOddCore (T ⧸ F))) := natCard_fusionOddCore_odd' _
  have hNcard : Nat.card (F.subgroupOf K) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFK).toEquiv
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have hindex : (F.subgroupOf K).index = Nat.card (Open.fusionOddCore (T ⧸ F)) := by
    have h1 := Subgroup.card_mul_index (F.subgroupOf K)
    rw [hNcard, hcardK] at h1
    exact Nat.eq_of_mul_eq_mul_left hFpos h1
  have hcop : Nat.Coprime (Nat.card (F.subgroupOf K)) (F.subgroupOf K).index := by
    rw [hNcard, hindex]
    obtain ⟨a, ha⟩ := hF2.exists_card_eq
    rw [ha]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hOodd)
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hH'card : Nat.card H' = Nat.card (Open.fusionOddCore (T ⧸ F)) := by
    have h1 := hH'.card_mul_card
    rw [hNcard, hcardK] at h1
    exact Nat.eq_of_mul_eq_mul_left hFpos h1
  let H : Subgroup T := H'.map K.subtype
  have hHcard : Odd (Nat.card H) := by
    have : Nat.card H = Nat.card H' := Subgroup.card_map_of_injective K.subtype_injective
    rw [this, hH'card]
    exact hOodd
  have hHodd : ∀ x ∈ H, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat hHcard (Subgroup.orderOf_dvd_natCard H hx)
  have hHK : ∀ x ∈ H, x ∈ K := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hdec : ∀ x ∈ K, ∃ f ∈ F, ∃ h ∈ H, x = f * h := by
    intro x hx
    obtain ⟨⟨a, b⟩, hab⟩ := hH'.2 ⟨x, hx⟩
    have hx' : x = (a.1 : T) * (b.1 : T) := (congrArg Subtype.val hab).symm
    exact ⟨a.1, a.2, b.1, ⟨b.1, b.2, rfl⟩, hx'⟩
  have hclaim : ∀ x ∈ K, Odd (orderOf x) → x ∈ H := by
    intro x hx hxo
    obtain ⟨f, hf, h, hh, rfl⟩ := hdec x hx
    have hc : Commute f h := (hodd h (hHodd h hh) f hf).symm
    have hpow : (f * h) ^ orderOf (f * h) = 1 := pow_orderOf_eq_one _
    rw [hc.mul_pow] at hpow
    have h1 : f ^ orderOf (f * h) = (h ^ orderOf (f * h))⁻¹ := eq_inv_of_mul_eq_one_left hpow
    have h2 : f ^ orderOf (f * h) ∈ H := by
      rw [h1]
      exact H.inv_mem (H.pow_mem hh _)
    have h3 : f ^ orderOf (f * h) = 1 :=
      eq_one_of_pGroup_two_odd hF2 (F.pow_mem hf _) (hHodd _ h2)
    have h4 : Odd (orderOf f) :=
      Odd.of_dvd_nat hxo (orderOf_dvd_of_pow_eq_one h3)
    have h5 : f = 1 := eq_one_of_pGroup_two_odd hF2 hf h4
    rw [h5, one_mul]
    exact hh
  have hHn : H.Normal :=
    ⟨fun h hh g => by
      apply hclaim
      · exact hKn.conj_mem h (hHK h hh) g
      · have : orderOf (g * h * g⁻¹) = orderOf h := by
          have := MulEquiv.orderOf_eq (MulAut.conj g) h
          rwa [MulAut.conj_apply] at this
        rw [this]
        exact hHodd h hh⟩
  have hle : H ≤ Open.fusionOddCore T := le_fusionOddCore_of_odd' hHcard
  intro x hx
  obtain ⟨f, hf, h, hh, rfl⟩ := hdec x hx
  exact Subgroup.mul_mem_sup hf (hle hh)

end Kernel

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
