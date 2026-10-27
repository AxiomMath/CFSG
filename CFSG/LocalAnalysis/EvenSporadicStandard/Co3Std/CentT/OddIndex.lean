module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Config
public import CFSG.Sporadic.Co3

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

private theorem factorization_495766656000_two : (495766656000 : ℕ).factorization 2 = 10 := by
  have h : (495766656000 : ℕ) = 2 ^ 10 * 484147125 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (p := 2) (n := 10) Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 484147125), add_zero]

private theorem card_le_card_T₀_of_pgroup_le_A {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {z t : G} {T₀ : Subgroup G} (hcfg : Fin76b.InnerConfig G A z t T₀)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hSA : S ≤ A) : Nat.card S ≤ Nat.card T₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hAm⟩ := hcfg.T₀_odd
  obtain ⟨j, hj⟩ := hS.exists_card_eq
  obtain ⟨k, hk⟩ := hcfg.T₀_pgroup.exists_card_eq
  have hdvd : Nat.card S ∣ Nat.card A := Subgroup.card_dvd_of_le hSA
  rw [hj, hAm, hk] at hdvd
  have hcop : Nat.Coprime (2 ^ j) m := by
    refine Nat.Coprime.pow_left _ ?_
    exact (Nat.coprime_two_left).2 hm
  have hdvd' : 2 ^ j ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right hdvd
  have hjk : j ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd'
  rw [hj, hk]
  exact Nat.pow_le_pow_right (by norm_num) hjk

section Certified


theorem card_T₀_eq {G : Type} [Group G] [Finite G] {A T₀ : Subgroup G} {z t : G}
    (hcfg : Fin76b.InnerConfig G A z t T₀) (hA : IsSporadic ↥A .Co3) :
    Nat.card T₀ = 2 ^ 10 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardA : Nat.card ↥A = 495766656000 := by
    obtain ⟨e⟩ := hA
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Co3.card_Co3
  obtain ⟨m, hm_odd, hm⟩ := hcfg.T₀_odd
  obtain ⟨k, hk⟩ := hcfg.T₀_pgroup.exists_card_eq
  have hkey : 2 ^ k * m = 495766656000 := by
    rw [← hk, hm.symm]
    exact hcardA
  have hk_eq : k = 10 := by
    have hf := congrArg (fun N : ℕ => Nat.factorization N 2) hkey
    have hm_ne : m ≠ 0 := fun h => Nat.not_odd_zero (h ▸ hm_odd)
    rw [Nat.factorization_mul (pow_ne_zero k (by norm_num)) hm_ne, Finsupp.add_apply,
      Nat.factorization_pow_self (p := 2) (n := k) Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hm_odd.not_two_dvd_nat, add_zero,
      factorization_495766656000_two] at hf
    exact hf
  rw [hk, hk_eq]

end Certified

theorem exists_sylow_le_centralizer {G : Type} [Group G] [Finite G] {A T₀ P : Subgroup G}
    {z t x : G} (hcfg : Fin76b.InnerConfig G A z t T₀) (hP : IsPGroup 2 P)
    (hTP : T₀ ⊔ zpowers z ≤ P) (hx : x ∈ P) (hxT : x ∉ T₀ ⊔ zpowers z)
    (hxz : x * z * x⁻¹ = z * t) (hxt : x * t * x⁻¹ = t) :
    ∃ Q : Sylow 2 G, (Q : Subgroup G) ≤ centralizer ({t} : Set G) ∧
      4 * Nat.card T₀ ∣ Nat.card Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardP : 4 * Nat.card T₀ ∣ Nat.card P := by
    have hTP' : T₀ ⊔ zpowers z ≤ P := hTP
    have hrel := Subgroup.relIndex_mul_card (H := T₀ ⊔ zpowers z) (K := P)
    rw [inf_of_le_left hTP'] at hrel
    obtain ⟨j, hj⟩ := hP.exists_card_eq
    have hdvd : (T₀ ⊔ zpowers z).relIndex P ∣ Nat.card P :=
      ⟨Nat.card (T₀ ⊔ zpowers z : Subgroup G), hrel.symm⟩
    rw [hj] at hdvd
    obtain ⟨i, _, hpow⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hne1 : (T₀ ⊔ zpowers z).relIndex P ≠ 1 := by
      intro h1
      exact hxT (Subgroup.relIndex_eq_one.mp h1 hx)
    have hi : i ≠ 0 := by
      intro h0
      exact hne1 (by rw [hpow, h0]; norm_num)
    have h2dvd : 2 ∣ (T₀ ⊔ zpowers z).relIndex P := by
      rw [hpow]
      exact dvd_pow_self 2 hi
    obtain ⟨d, hd⟩ := h2dvd
    refine ⟨d, ?_⟩
    rw [← hrel, hcfg.T_card, hd]
    ring
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  refine ⟨Q, ?_, dvd_trans hcardP (Subgroup.card_dvd_of_le hPQ)⟩
  have hzT : z ∈ T₀ ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  have hzQ : z ∈ (Q : Subgroup G) := hPQ (hTP hzT)
  have hxQ : x ∈ (Q : Subgroup G) := hPQ hx
  haveI : Nontrivial ↥Q :=
    ⟨⟨⟨z, hzQ⟩, ⟨1, (Q : Subgroup G).one_mem⟩,
      fun h => hcfg.z_ne (Subtype.ext_iff.mp h)⟩⟩
  have hcenter : Nontrivial ↥(Subgroup.center ↥Q) := Q.isPGroup'.center_nontrivial
  have hc2 : 2 ∣ Nat.card ↥(Subgroup.center ↥Q) := by
    obtain ⟨n, hn0, hn⟩ :=
      (Q.isPGroup'.to_subgroup (Subgroup.center ↥Q)).nontrivial_iff_card.mp hcenter
    exact hn.symm ▸ dvd_pow_self 2 hn0.ne'
  obtain ⟨c₀, hc₀ord⟩ := exists_prime_orderOf_dvd_card' 2 hc2
  let cQ : ↥Q := (c₀ : ↥Q)
  have hcQord : orderOf cQ = 2 := (Subgroup.orderOf_coe c₀).trans hc₀ord
  have hcQcomm : ∀ q : ↥Q, q * cQ = cQ * q := fun q => Subgroup.mem_center_iff.mp c₀.2 q
  let c : G := (cQ : G)
  have hc_ord : orderOf c = 2 := (Subgroup.orderOf_coe cQ).trans hcQord
  have hc_sq : c * c = 1 := by
    have h := pow_orderOf_eq_one c
    rw [hc_ord] at h
    simpa [pow_two] using h
  have hc_ne : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc_ord
    exact absurd hc_ord (by norm_num)
  have hc_comm_Q : ∀ q : ↥Q, (q : G) * c = c * (q : G) := by
    intro q
    simpa [c] using congrArg Subtype.val (hcQcomm q)
  have hc_cent_z : c ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc_comm_Q ⟨z, hzQ⟩).symm
  have hc_sup : c ∈ A ⊔ zpowers z := by
    rw [← hcfg.cent_eq]
    exact hc_cent_z
  obtain ⟨m, hmA, c', hc'zp, hc_eq⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (A := A) (B := zpowers z)
      (Subgroup.zpowers_le.mpr hcfg.z_cent) hc_sup
  have hc'1_or_z : c' = 1 ∨ c' = z := Fin76b.mem_zpowers_sq_eq_one hcfg.z_sq hc'zp
  have hm_form : m = c ∨ m = c * z := by
    rcases hc'1_or_z with h1 | h1
    · left
      have hcm : c = m := by rw [hc_eq, h1, mul_one]
      exact hcm.symm
    · right
      have hcq : c * z = m := by rw [hc_eq, h1, mul_assoc, hcfg.z_sq, mul_one]
      exact hcq.symm
  have hcz_comm : z * c = c * z := hc_comm_Q ⟨z, hzQ⟩
  have hm_sq : m * m = 1 := by
    rcases hm_form with h | h
    · rw [h]; exact hc_sq
    · rw [h]
      calc (c * z) * (c * z) = c * (z * c) * z := by group
        _ = c * (c * z) * z := by rw [hcz_comm]
        _ = (c * c) * (z * z) := by group
        _ = 1 := by rw [hc_sq, hcfg.z_sq, mul_one]
  have hm_comm_T : ∀ y ∈ T₀, y * m = m * y := by
    intro y hy
    have hyQ : y ∈ (Q : Subgroup G) := hPQ (hTP (mem_sup_left hy))
    have hyc : y * c = c * y := hc_comm_Q ⟨y, hyQ⟩
    have hyz : y * z = z * y := hcfg.z_comm_of_mem_A (hcfg.T₀_le hy)
    rcases hm_form with h | h
    · rw [h]; exact hyc
    · rw [h]
      calc y * (c * z) = (y * c) * z := by group
        _ = (c * y) * z := by rw [hyc]
        _ = c * (y * z) := by group
        _ = c * (z * y) := by rw [hyz]
        _ = (c * z) * y := by group
  have hzp_group : IsPGroup 2 (zpowers m) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact hm_sq)
  have hT0_norm : T₀ ≤ Subgroup.normalizer (zpowers m : Set G) := by
    have hcent : T₀ ≤ Subgroup.centralizer (zpowers m : Set G) := by
      rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_iff.2 hm_comm_T
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hS_pgroup : IsPGroup 2 (T₀ ⊔ zpowers m : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hcfg.T₀_pgroup hzp_group hT0_norm
  have hmT : m ∈ T₀ := by
    have hSle : T₀ ⊔ zpowers m ≤ A :=
      sup_le hcfg.T₀_le (Subgroup.zpowers_le.mpr hmA)
    have hcardS : Nat.card (T₀ ⊔ zpowers m : Subgroup G) ≤ Nat.card T₀ :=
      card_le_card_T₀_of_pgroup_le_A hcfg hS_pgroup hSle
    have hEq : T₀ = T₀ ⊔ zpowers m := Subgroup.eq_of_le_of_card_ge le_sup_left hcardS
    exact hEq.symm ▸ mem_sup_right (mem_zpowers m)
  have hc_eq_t : c = t := by
    rcases hm_form with hmc | hmcz
    · rcases hcfg.center_le m hmT hm_comm_T with hm1 | hmt
      · exact absurd (hmc.symm.trans hm1) hc_ne
      · exact hmc.symm.trans hmt
    · rcases hcfg.center_le m hmT hm_comm_T with hm1 | hmt
      · have hcz1 : c * z = 1 := hmcz.symm.trans hm1
        have hc_eq_z : c = z := by
          rw [← mul_one c, ← hcfg.z_sq, ← mul_assoc, hcz1, one_mul]
        exfalso
        have hxc : c * x = x * c := (hc_comm_Q ⟨x, hxQ⟩).symm
        have hconj : x * c * x⁻¹ = c := by rw [← hxc]; group
        rw [hc_eq_z] at hconj
        have hzt : z * t = z := hxz.symm.trans hconj
        exact hcfg.t_ne (mul_left_cancel (by rw [hzt, mul_one]))
      · have hczt : c * z = t := hmcz.symm.trans hmt
        have hc_eq_tz : c = t * z := by
          rw [← mul_one c, ← hcfg.z_sq, ← mul_assoc, hczt]
        exfalso
        have hxc : c * x = x * c := (hc_comm_Q ⟨x, hxQ⟩).symm
        have hconj : x * c * x⁻¹ = c := by rw [← hxc]; group
        have hxzt : x * (t * z) * x⁻¹ = z := by
          calc x * (t * z) * x⁻¹ = (x * t * x⁻¹) * (x * z * x⁻¹) := by group
            _ = t * (z * t) := by rw [hxt, hxz]
            _ = z := by
              rw [← hcfg.z_comm_of_mem_A hcfg.t_mem_A, ← mul_assoc, hcfg.t_sq, one_mul]
        have hconj' : x * (t * z) * x⁻¹ = t * z := by rw [← hc_eq_tz]; exact hconj
        have htz : t * z = z := hconj'.symm.trans hxzt
        exact hcfg.t_ne (mul_right_cancel (by rw [htz, one_mul]))
  intro q hq
  rw [Subgroup.mem_centralizer_singleton_iff, ← hc_eq_t]
  exact hc_comm_Q ⟨q, hq⟩

end CFSG.EvenSporadicStandard.Co3Std.CentT
