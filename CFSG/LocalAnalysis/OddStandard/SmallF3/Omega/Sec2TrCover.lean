module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

structure OddCentralCover {A P : Type*} [Group A] [Group P] (ρ : A →* P) : Prop where
  surjective : Function.Surjective ρ
  ker_le_center : ρ.ker ≤ center A
  odd_card_ker : Odd (Nat.card ρ.ker)

namespace OddCentralCover

variable {A P : Type*} [Group A] [Group P] {ρ : A →* P}

theorem eq_one_of_mul_self_eq_one (h : OddCentralCover ρ) {n : A} (hn : n ∈ ρ.ker)
    (hnn : n * n = 1) : n = 1 := by
  have h2 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hnn)
  have hk : orderOf n ∣ Nat.card ρ.ker := Subgroup.orderOf_dvd_natCard ρ.ker hn
  have hcop : Nat.Coprime 2 (Nat.card ρ.ker) := Nat.coprime_two_left.mpr h.odd_card_ker
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 hk)

theorem eq_of_mul_self_eq_one (h : OddCentralCover ρ) {a b : A} (ha : a * a = 1)
    (hb : b * b = 1) (hab : ρ a = ρ b) : a = b := by
  have hn : a⁻¹ * b ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have hc : a⁻¹ * b ∈ center A := h.ker_le_center hn
  have hb' : b = a * (a⁻¹ * b) := by group
  have hnn : (a⁻¹ * b) * (a⁻¹ * b) = 1 := by
    calc (a⁻¹ * b) * (a⁻¹ * b) = (a * a) * ((a⁻¹ * b) * (a⁻¹ * b)) := by rw [ha, one_mul]
      _ = a * (a * (a⁻¹ * b)) * (a⁻¹ * b) := by group
      _ = a * ((a⁻¹ * b) * a) * (a⁻¹ * b) := by rw [mem_center_iff.mp hc a]
      _ = (a * (a⁻¹ * b)) * (a * (a⁻¹ * b)) := by group
      _ = b * b := by rw [← hb']
      _ = 1 := hb
  have := h.eq_one_of_mul_self_eq_one hn hnn
  rwa [inv_mul_eq_one] at this

theorem pow_card_ker (h : OddCentralCover ρ) {a : A} (haa : ρ a * ρ a = 1) :
    a ^ Nat.card ρ.ker * a ^ Nat.card ρ.ker = 1 ∧ ρ (a ^ Nat.card ρ.ker) = ρ a := by
  have hker : a * a ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul]; exact haa
  obtain ⟨j, hj⟩ := h.odd_card_ker
  have hpow : (a * a) ^ Nat.card ρ.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard ρ.ker hker)
  refine ⟨?_, ?_⟩
  · calc a ^ Nat.card ρ.ker * a ^ Nat.card ρ.ker = a ^ (2 * Nat.card ρ.ker) := by
          rw [two_mul, pow_add]
      _ = (a ^ 2) ^ Nat.card ρ.ker := pow_mul a 2 _
      _ = 1 := by rw [pow_two]; exact hpow
  · have hz2 : (ρ a) ^ 2 = 1 := by rw [pow_two]; exact haa
    rw [map_pow, hj, pow_succ, pow_mul, hz2, one_pow, one_mul]

theorem exists_mul_self_eq_one_lift (h : OddCentralCover ρ) {z : P} (hz : z * z = 1) :
    ∃ w : A, w * w = 1 ∧ ρ w = z := by
  obtain ⟨a, rfl⟩ := h.surjective z
  exact ⟨a ^ Nat.card ρ.ker, (h.pow_card_ker hz).1, (h.pow_card_ker hz).2⟩

theorem pow_card_ker_eq (h : OddCentralCover ρ) {w x : A} (hw : w * w = 1) (hx : ρ x = ρ w) :
    x ^ Nat.card ρ.ker = w := by
  have hn : w⁻¹ * x ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]
  have hc : w⁻¹ * x ∈ center A := h.ker_le_center hn
  have hx' : x = w * (w⁻¹ * x) := by group
  have hcomm : Commute w (w⁻¹ * x) := mem_center_iff.mp hc w
  obtain ⟨j, hj⟩ := h.odd_card_ker
  have hnk : (w⁻¹ * x) ^ Nat.card ρ.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard ρ.ker hn)
  have hw2 : w ^ 2 = 1 := by rw [pow_two]; exact hw
  have hwk : w ^ Nat.card ρ.ker = w := by
    rw [hj, pow_succ, pow_mul, hw2, one_pow, one_mul]
  calc x ^ Nat.card ρ.ker = (w * (w⁻¹ * x)) ^ Nat.card ρ.ker := by rw [← hx']
    _ = w ^ Nat.card ρ.ker * (w⁻¹ * x) ^ Nat.card ρ.ker := hcomm.mul_pow _
    _ = w := by rw [hnk, mul_one, hwk]

theorem centralizer_singleton_eq_comap (h : OddCentralCover ρ) {w : A} (hw : w * w = 1) :
    centralizer ({w} : Set A) = (centralizer ({ρ w} : Set P)).comap ρ := by
  ext a
  rw [mem_comap, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro ha
    rw [← map_mul, ← map_mul, ha]
  · intro ha
    have hww : (a * w * a⁻¹) * (a * w * a⁻¹) = 1 := by
      calc (a * w * a⁻¹) * (a * w * a⁻¹) = a * (w * w) * a⁻¹ := by group
        _ = 1 := by rw [hw]; group
    have himg : ρ (a * w * a⁻¹) = ρ w := by
      rw [map_mul, map_mul, map_inv, ha, mul_assoc, mul_inv_cancel, mul_one]
    have heq := h.eq_of_mul_self_eq_one hww hw himg
    rw [mul_inv_eq_iff_eq_mul] at heq
    exact heq

theorem map_centralizer_singleton (h : OddCentralCover ρ) {w : A} (hw : w * w = 1) :
    (centralizer ({w} : Set A)).map ρ = centralizer ({ρ w} : Set P) := by
  rw [h.centralizer_singleton_eq_comap hw, map_comap_eq_self_of_surjective h.surjective]

theorem oddCore_eq_ker [Finite A] [Finite P] (h : OddCentralCover ρ) (hP : oddCore P = ⊥) :
    oddCore A = ρ.ker := by
  apply le_antisymm
  · have hn : ((oddCore A).map ρ).Normal := (oddCore_normal (G := A)).map ρ h.surjective
    have hodd : Odd (Nat.card ((oddCore A).map ρ)) :=
      odd_card_oddCore.of_dvd_nat (Subgroup.card_map_dvd _ ρ)
    have hle : (oddCore A).map ρ ≤ oddCore P := le_oddCore_of_normal hn hodd
    rw [hP, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
    exact hle
  · exact le_oddCore_of_normal (MonoidHom.normal_ker ρ) h.odd_card_ker

end OddCentralCover

end CFSG.OddStandard.SmallF3.Omega
