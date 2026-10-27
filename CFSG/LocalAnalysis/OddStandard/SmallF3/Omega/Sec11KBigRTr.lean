module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigRSD
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115cA
import CFSG.Quasithin.Background.A1cTransferVariants

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem s900_central_mem_sylow [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X) {z : G}
    (hzX : z ∈ X) (hz2 : orderOf z = 2) (hzc : ∀ x ∈ X, x * z = z * x) : z ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hP.exists_sylow
  let N : Subgroup ↥X := Subgroup.zpowers (⟨z, hzX⟩ : ↥X)
  have hNcard : Nat.card N = 2 := by
    change Nat.card (Subgroup.zpowers (⟨z, hzX⟩ : ↥X)) = 2
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz2]
  have hN2 : IsPGroup 2 N := IsPGroup.of_card (n := 1) (by rw [hNcard]; norm_num)
  have hzcent : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (by simpa using hzc w.1 w.2)
  have hNcent : N ≤ Subgroup.center ↥X := by
    change Subgroup.zpowers (⟨z, hzX⟩ : ↥X) ≤ Subgroup.center ↥X
    exact Subgroup.zpowers_le.2 hzcent
  haveI : N.Normal := Subgroup.normal_of_le_center hNcent
  have hNS : N ≤ (S : Subgroup ↥X) := IsPGroup.le_sylow_of_normal hN2 S
  have hzS : (⟨z, hzX⟩ : ↥X) ∈ (S : Subgroup ↥X) := hNS (Subgroup.mem_zpowers _)
  rw [← hS]
  exact Subgroup.mem_map_of_mem X.subtype hzS

theorem s900_conj_mem_sylow [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X) {s : G}
    (hsX : s ∈ X) (hs2 : orderOf s = 2) : ∃ y ∈ X, y * s * y⁻¹ ∈ P := by
  have hP2 : IsPGroup 2 (Subgroup.zpowers s) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hs2]
    norm_num
  have hPX : Subgroup.zpowers s ≤ X := Subgroup.zpowers_le.2 hsX
  obtain ⟨Q, hQ, hspQ⟩ := exists_isSylow2Of_ge hP2 hPX
  obtain ⟨a, haX, ha⟩ := IsSylow2Of.exists_conj_mem hP hQ
  have hsQ : s ∈ Q := hspQ (Subgroup.mem_zpowers s)
  have hconj : a⁻¹ * s * a ∈ P := (ha s).1 hsQ
  exact ⟨a⁻¹, X.inv_mem haX, by simpa using hconj⟩

theorem s900_oTwoRes_le_of_squares {X N : Subgroup G} (hsq : ∀ x ∈ X, x ^ 2 ∈ N) :
    oTwoRes X ≤ N := by
  rw [oTwoRes, Subgroup.closure_le]
  rintro x ⟨hxX, m, hm⟩
  have hx1 : x ^ (2 * m + 1) = 1 := by
    rw [← hm]
    exact pow_orderOf_eq_one x
  have hx : x = (x ^ (m + 1)) ^ 2 := by
    rw [← pow_mul]
    calc x = x ^ (2 * m + 1) * x := by rw [hx1, one_mul]
      _ = x ^ ((m + 1) * 2) := by rw [← pow_succ]; congr 1; ring
  rw [hx]
  exact hsq _ (X.pow_mem hxX (m + 1))

theorem s900_oTwoRes_unique_inv [Finite G] {X P : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    (hP : IsSylow2Of P X) (hPsd : Nonempty (↥P ≃* CFSG.Open.SemidihedralGroup n)) {z : G}
    (hzX : z ∈ X) (hz2 : orderOf z = 2) (hzc : ∀ x ∈ X, x * z = z * x) :
    ∀ s ∈ oTwoRes X, orderOf s = 2 → s = z := by
  have hzP : z ∈ P := s900_central_mem_sylow hP hzX hz2 hzc
  have hzcP : ∀ x ∈ P, x * z = z * x := fun x hx => hzc x (hP.1 hx)
  obtain ⟨Q, hQP, hQidx, hQinv⟩ := s900_sd_quaternion hn hPsd hzP hz2 hzcP
  obtain ⟨u, huP, hu2, huz, hconj⟩ := s900_sd_noncentral_conj hn hPsd hzP hz2 hzcP
  have huX : u ∈ X := hP.1 huP
  have hQu : ∀ x ∈ X, x⁻¹ * u * x ∉ Q := by
    intro x hx hxQ
    have hord : orderOf (x⁻¹ * u * x) = 2 := by
      simpa using (sec11c_orderOf_conj x⁻¹ u).trans hu2
    have hxz : x⁻¹ * u * x = z := hQinv _ hxQ hord
    have huz' : u = x * z * x⁻¹ := by
      have h : x * (x⁻¹ * u * x) * x⁻¹ = u := by group
      rw [hxz] at h
      exact h.symm
    have hzx : x * z * x⁻¹ = z := by
      rw [hzc x hx]
      group
    exact huz (huz'.trans hzx)
  obtain ⟨N, _, _, hNsq, huN⟩ :=
    CFSG.Quasithin.thompson_transfer_exists_normal_subgroup hP.1 hP.2.1 hP.2.2 hQP hQidx huX
      hu2 hQu
  have hEN : oTwoRes X ≤ N := s900_oTwoRes_le_of_squares hNsq
  intro s hsE hs2
  by_contra hsz
  have hsX : s ∈ X := sec11c_oTwoRes_le X hsE
  obtain ⟨y, hyX, hyP⟩ := s900_conj_mem_sylow hP hsX hs2
  have hword : orderOf (y * s * y⁻¹) = 2 := by
    rw [sec11c_orderOf_conj y s, hs2]
  have hwz : y * s * y⁻¹ ≠ z := by
    intro hw
    apply hsz
    have hy' : y⁻¹ * (y * s * y⁻¹) * y = s := by group
    rw [hw] at hy'
    rw [← hy']
    calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
      _ = y⁻¹ * (y * z) := by rw [← hzc y hyX]
      _ = z := by group
  obtain ⟨p, hpP, hpconj⟩ := hconj (y * s * y⁻¹) hyP hword hwz
  have hpyX : p * y ∈ X := X.mul_mem (hP.1 hpP) hyX
  have hr : ∀ t ∈ X, (p * y) * t * (p * y)⁻¹ ∈ X := by
    intro t ht
    exact X.mul_mem (X.mul_mem hpyX ht) (X.inv_mem hpyX)
  have hmem : u ∈ oTwoRes X := by
    have h := sec11c_conj_mem_oTwoRes (X := X) (r := p * y) hr hsE
    have heq : (p * y) * s * (p * y)⁻¹ = u := by
      rw [← hpconj]
      group
    rwa [heq] at h
  exact huN (hEN hmem)

end CFSG.OddStandard.SmallF3.Omega
