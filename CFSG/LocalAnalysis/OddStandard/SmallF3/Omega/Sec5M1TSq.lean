module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem sec5m1t_sl23_unique_involution {a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)}
    (ha : a * a = 1) (ha1 : a ≠ 1) (hb : b * b = 1) (hb1 : b ≠ 1) : a = b := by
  revert a b
  decide +kernel

theorem sec5m1t_sq_eq {G : Type} [Group G] [Finite G] {L K : Subgroup G} {z q : G}
    (hz2 : orderOf z = 2) (hK : Sl23PocketIn L z K) (hq : q ∈ K) (hq4 : orderOf q = 4) :
    q * q = z := by
  obtain ⟨hzK, hKle, -, ⟨e⟩⟩ := hK
  let a : ↥K := ⟨z, hzK⟩
  let c : ↥K := ⟨q * q, K.mul_mem hq hq⟩
  have hcentral : ∀ y : ↥K, a * y = y * a := fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hKle y.2)).2).symm
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have ha2 : a * a = 1 := Subtype.ext hzz
  have hq2 : orderOf (q * q) = 2 := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hq4]; norm_num), hq4]
  have hc2 : c * c = 1 := by
    apply Subtype.ext
    have h := pow_orderOf_eq_one (q * q)
    rw [hq2, pow_two] at h
    exact h
  have haord : orderOf a = 2 := by rw [Subgroup.orderOf_mk, hz2]
  have hcord : orderOf c = 2 := by rw [Subgroup.orderOf_mk, hq2]
  let ν : ↥K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore ↥K))
  have hker : ∀ u : ↥K, ν u = 1 → u ∈ CFSG.oddCore ↥K := by
    intro u hu
    have h : e (QuotientGroup.mk u : ↥K ⧸ CFSG.oddCore ↥K) = 1 := hu
    exact (QuotientGroup.eq_one_iff u).mp (e.injective (h.trans e.map_one.symm))
  have hodd : ∀ u ∈ CFSG.oddCore ↥K, Odd (orderOf u) := fun u hu =>
    Odd.of_dvd_nat
      (CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.odd_card_oddCore)
      (Subgroup.orderOf_dvd_natCard _ hu)
  have hνa : ν a ≠ 1 := fun h =>
    CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.not_mem_oddCore_of_orderOf_eq_two
      haord (hker a h)
  have hνc : ν c ≠ 1 := fun h =>
    CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.not_mem_oddCore_of_orderOf_eq_two
      hcord (hker c h)
  have hνeq : ν a = ν c :=
    sec5m1t_sl23_unique_involution (by rw [← map_mul, ha2, map_one]) hνa
      (by rw [← map_mul, hc2, map_one]) hνc
  have hmem : a⁻¹ * c ∈ CFSG.oddCore ↥K :=
    hker _ (by rw [map_mul, map_inv, hνeq, inv_mul_cancel])
  have hsq : (a⁻¹ * c) * (a⁻¹ * c) = 1 := by
    have h1 : (a⁻¹ * c) * (a⁻¹ * c) = (a⁻¹ * a⁻¹) * (c * c) := by
      have hac : c * a⁻¹ = a⁻¹ * c := by
        have h := hcentral c
        calc c * a⁻¹ = a⁻¹ * (a * c) * a⁻¹ := by group
          _ = a⁻¹ * (c * a) * a⁻¹ := by rw [h]
          _ = a⁻¹ * c := by group
      calc (a⁻¹ * c) * (a⁻¹ * c) = a⁻¹ * (c * a⁻¹) * c := by group
        _ = a⁻¹ * (a⁻¹ * c) * c := by rw [hac]
        _ = (a⁻¹ * a⁻¹) * (c * c) := by group
    rw [h1, hc2, mul_one, ← mul_inv_rev, ha2, inv_one]
  have hord2 : orderOf (a⁻¹ * c) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have hord1 : orderOf (a⁻¹ * c) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · exact absurd (hodd _ hmem) (by rw [h]; decide)
  have hac : a⁻¹ * c = 1 := orderOf_eq_one_iff.mp hord1
  have hca : c = a := by
    have h := congrArg (fun y => a * y) hac
    simpa using h
  exact congrArg (fun y : ↥K => (y : G)) hca

end CFSG.OddStandard.SmallF3.Omega
