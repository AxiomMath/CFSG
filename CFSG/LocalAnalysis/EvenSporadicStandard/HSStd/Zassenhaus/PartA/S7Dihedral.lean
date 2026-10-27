module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Lam
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFusionHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerI1I2

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.EvenSporadicStandard.HSStd

theorem eight_dvd_card_centralizer_of_sigma {X : Type} [Group X] [Finite X] {t y c k : X}
    (ht : orderOf t = 2) (hS : SigmaConfig t y c k) :
    8 ∣ Nat.card ↥(centralizer ({y} : Set X)) := by
  obtain ⟨-, hyL, hc3, hk2, hk1, -, -, -, hyk, -, hkc, hkc', hkk'⟩ := hS
  have ht2 : t * t = 1 := mul_self_of_orderOf_two ht
  have hty : y * t = t * y := by
    obtain ⟨l, -, rfl⟩ := hyL
    exact mem_centralizer_singleton_iff.1 l.2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hcinv : c ≠ c⁻¹ := by
    intro h
    have h2 : c ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.2 h
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hc3] at this
    omega
  have htk : t ≠ k := by
    intro h
    rw [← h] at hkc hkc'
    rw [hkc] at hkc'
    have e1 : t * c⁻¹ * t⁻¹ = c := by
      calc t * c⁻¹ * t⁻¹ = (t * c * t⁻¹)⁻¹ := by group
        _ = (c⁻¹)⁻¹ := by rw [hkc]
        _ = c := inv_inv c
    have e2 : t * c⁻¹ * t⁻¹ = c⁻¹ := by
      calc t * c⁻¹ * t⁻¹ = c⁻¹ * t * t⁻¹ := by rw [hkc']
        _ = c⁻¹ := by group
    exact hcinv (e1.symm.trans e2)
  set k' : X := t * k * t⁻¹ with hk'
  have hk'2 : k' * k' = 1 := by
    calc k' * k' = t * (k * k) * t⁻¹ := by rw [hk']; group
      _ = 1 := by rw [hk2]; group
  have hk'1 : k' ≠ 1 := by
    intro h
    apply hk1
    have : t * k * t⁻¹ = 1 := h
    calc k = t⁻¹ * (t * k * t⁻¹) * t := by group
      _ = 1 := by rw [this]; group
  have hk'k : k' ≠ k := by
    intro h
    have hkt : t * k * t⁻¹ = k := h
    have hkt' : t⁻¹ * k * t = k := by
      calc t⁻¹ * k * t = t⁻¹ * (t * k * t⁻¹) * t := by rw [hkt]
        _ = k := by group
    have e1 : k * (t * c * t⁻¹) * k⁻¹ = (t * c * t⁻¹)⁻¹ := by
      calc k * (t * c * t⁻¹) * k⁻¹
          = t * ((t⁻¹ * k * t) * c * (t⁻¹ * k * t)⁻¹) * t⁻¹ := by group
        _ = t * (k * c * k⁻¹) * t⁻¹ := by rw [hkt']
        _ = t * c⁻¹ * t⁻¹ := by rw [hkc]
        _ = (t * c * t⁻¹)⁻¹ := by group
    have e2 : k * (t * c * t⁻¹) * k⁻¹ = t * c * t⁻¹ := by
      calc k * (t * c * t⁻¹) * k⁻¹ = (t * c * t⁻¹) * k * k⁻¹ := by rw [hkc']
        _ = t * c * t⁻¹ := by group
    have e3 : t * c * t⁻¹ = (t * c * t⁻¹)⁻¹ := e2.symm.trans e1
    apply hcinv
    calc c = t⁻¹ * (t * c * t⁻¹) * t := by group
      _ = t⁻¹ * (t * c * t⁻¹)⁻¹ * t := by rw [← e3]
      _ = c⁻¹ := by group
  have htk' : t ≠ k' := by
    intro h
    apply htk
    have h1 : t * k * t⁻¹ = t := h.symm
    have h2 : t * k = t * t := mul_inv_eq_iff_eq_mul.1 h1
    exact (mul_left_cancel h2).symm
  have hkk'c : Commute k k' := hkk'
  have htkk' : t ≠ k * k' := by
    intro h
    apply hk'k
    have e1 : t * k * t⁻¹ = k := by
      rw [h]
      exact (Commute.mul_left (Commute.refl k) hkk'c.symm).mul_inv_cancel
    exact e1
  have hkk'1 : k * k' ≠ 1 := by
    intro h
    apply hk'k
    have : k' = k⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, hkinv]
  have hkkk' : k ≠ k * k' := by
    intro h
    apply hk'1
    have : k * 1 = k * k' := by rw [mul_one]; exact h
    exact (mul_left_cancel this).symm
  have hk'kk' : k' ≠ k * k' := by
    intro h
    apply hk1
    have : 1 * k' = k * k' := by rw [one_mul]; exact h
    exact (mul_right_cancel this).symm
  have hV : ∀ x, x ∈ Vsub k k' ↔ x = 1 ∨ x = k ∨ x = k' ∨ x = k * k' :=
    fun x => mem_Vsub_iff hk2 hk'2 hkk'
  have hVcard : Nat.card ↥(Vsub k k') = 4 := by
    have hset : (Vsub k k' : Set X) = {1, k, k', k * k'} := by
      ext x
      simp only [SetLike.mem_coe, hV, Set.mem_insert_iff, Set.mem_singleton_iff]
    have n1 : (1 : X) ∉ ({k, k', k * k'} : Set X) := by
      rintro (h | h | h)
      · exact hk1 h.symm
      · exact hk'1 h.symm
      · exact hkk'1 h.symm
    have n2 : k ∉ ({k', k * k'} : Set X) := by
      rintro (h | h)
      · exact hk'k h.symm
      · exact hkkk' h
    have h0 : Nat.card ↥(Vsub k k') = Set.ncard (Vsub k k' : Set X) :=
      Nat.card_coe_set_eq (Vsub k k' : Set X)
    rw [h0, hset, Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_pair hk'kk']
  have htV : t ∉ Vsub k k' := by
    rw [hV]
    rintro (h | h | h | h)
    exacts [ht1 h, htk h, htk' h, htkk' h]
  have hnorm_t : ∀ x ∈ Vsub k k', t * x * t⁻¹ ∈ Vsub k k' := by
    intro x hx
    rw [hV] at hx ⊢
    rcases hx with h | h | h | h <;> rw [h]
    · left; group
    · exact Or.inr (Or.inr (Or.inl hk'.symm))
    · refine Or.inr (Or.inl ?_)
      calc t * k' * t⁻¹ = (t * t) * k * (t⁻¹ * t⁻¹) := by rw [hk']; group
        _ = k := by rw [ht2, htinv, ht2]; group
    · refine Or.inr (Or.inr (Or.inr ?_))
      have hk'conj : t * k' * t⁻¹ = k := by
        calc t * k' * t⁻¹ = (t * t) * k * (t⁻¹ * t⁻¹) := by rw [hk']; group
          _ = k := by rw [ht2, htinv, ht2]; group
      calc t * (k * k') * t⁻¹ = (t * k * t⁻¹) * (t * k' * t⁻¹) := by group
        _ = k' * k := by rw [← hk', hk'conj]
        _ = k * k' := hkk'.symm
  have hVn : zpowers t ≤ normalizer ((Vsub k k' : Subgroup X) : Set X) := by
    rw [zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hnorm_t x, fun hx => ?_⟩
    have := hnorm_t _ hx
    have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
        _ = x := by rw [ht2, htinv, ht2]; group
    rwa [e] at this
  set H : Subgroup X := Vsub k k' ⊔ zpowers t with hH
  have hVH : Vsub k k' ≤ H := le_sup_left
  haveI hnormH : ((Vsub k k').subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVH]
    exact sup_le Subgroup.le_normalizer hVn
  let τ : ↥H := ⟨t, (le_sup_right : zpowers t ≤ H) (mem_zpowers t)⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ2 : (QuotientGroup.mk τ : ↥H ⧸ (Vsub k k').subgroupOf H) ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul]
    rw [QuotientGroup.eq_one_iff]
    have : τ * τ = 1 := Subtype.ext ht2
    rw [this]
    exact one_mem _
  have hτ1 : (QuotientGroup.mk τ : ↥H ⧸ (Vsub k k').subgroupOf H) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    exact htV h
  have hord : orderOf (QuotientGroup.mk τ : ↥H ⧸ (Vsub k k').subgroupOf H) = 2 :=
    orderOf_eq_prime hτ2 hτ1
  have h2dvd : 2 ∣ Nat.card (↥H ⧸ (Vsub k k').subgroupOf H) := by
    rw [← hord]; exact orderOf_dvd_natCard _
  have hHcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Vsub k k').subgroupOf H)
  have hVsub : Nat.card ↥((Vsub k k').subgroupOf H) = 4 := by
    rw [← hVcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv
  have h8H : 8 ∣ Nat.card H := by
    rw [hHcard, hVsub]
    obtain ⟨j, hj⟩ := h2dvd
    rw [hj]
    exact ⟨j, by ring⟩
  have hty_c : Commute y t := hty
  have hyk_c : Commute y k := hyk
  have hyk'_c : Commute y k' := (hty_c.mul_right hyk_c).mul_right hty_c.inv_right
  have hHC : H ≤ centralizer ({y} : Set X) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.2 hyk_c.symm.eq
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.2 hyk'_c.symm.eq
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.2 hty_c.symm.eq
  exact h8H.trans (Subgroup.card_dvd_of_le hHC)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
