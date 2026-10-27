module

public import CFSG.ClassicalInvolution.Q3.Basic
import CFSG.ClassicalInvolution.Q3.CoprimeCentralizer

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

namespace SP3

section General

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_not_commute_of_isSubnormal_centralizer_prime {U : Subgroup Y} [U.Normal]
    (hU : IsPGroup 2 U) (hC : Subgroup.centralizer (U : Set Y) ≤ U) {z : Y} (hz : z * z = 1)
    {J : Subgroup Y} (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set Y))) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {g : Y} (hgJ : g ∈ J) {j : ℕ} (hgj : g ^ p ^ j = 1)
    (hg1 : g ≠ 1) : ∃ x ∈ J ⊓ U, g * x ≠ x * g := by
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  by_contra hcon
  push Not at hcon
  set H : Subgroup Y := Subgroup.centralizer ({z} : Set Y) with hHdef
  have hJH : J ≤ H := isSubnormal_le hJ
  have hgH : g ∈ H := hJH hgJ
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hgH
  set A : Subgroup Y := U ⊓ H with hAdef
  have hAH : A ≤ H := inf_le_right
  have hAU : A ≤ U := inf_le_left
  have hAn : (A.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAH]
    intro n h hnA hhH
    exact ⟨Subgroup.Normal.conj_mem inferInstance n hnA.1 h, H.mul_mem (H.mul_mem hhH (hAH hnA))
      (H.inv_mem hhH)⟩
  have hA2 : IsPGroup 2 A := hU.to_le hAU
  have hcop : ¬ p ∣ Nat.card A := by
    obtain ⟨k, hk⟩ := hA2.exists_card_eq
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hP : IsPGroup p (Subgroup.zpowers g) := isPGroup_zpowers hgj
  have hPJ : Subgroup.zpowers g ≤ J := (Subgroup.zpowers_le).mpr hgJ
  have h1 : ⁅A, Subgroup.zpowers g⁆ ≤ J :=
    commutator_le_of_isSubnormal hp hJ hAH hAn hcop hPJ hP
  have hgA : g ∈ Subgroup.normalizer (A : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hfwd : ∀ g' ∈ H, ∀ x ∈ A, g' * x * g'⁻¹ ∈ A := fun g' hg' x hx =>
      ⟨Subgroup.Normal.conj_mem inferInstance x hx.1 g',
        H.mul_mem (H.mul_mem hg' hx.2) (H.inv_mem hg')⟩
    exact ⟨fun hx => hfwd g hgH x hx, fun hx => by
      have := hfwd g⁻¹ (H.inv_mem hgH) _ hx
      simpa [mul_assoc] using this⟩
  have hPnorm : Subgroup.zpowers g ≤ Subgroup.normalizer (A : Set Y) := by
    rw [Subgroup.zpowers_le]; exact hgA
  have h2 : ⁅A, Subgroup.zpowers g⁆ ≤ A :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hPnorm
  have hB : ⁅⁅A, Subgroup.zpowers g⁆, Subgroup.zpowers g⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro b hb x hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hbJU : b ∈ J ⊓ U := ⟨h1 hb, hAU (h2 hb)⟩
    have hc : g * b = b * g := hcon b hbJU
    have hck : Commute b (g ^ k) := (Commute.zpow_right (show Commute b g from hc.symm) k)
    exact commutatorElement_eq_one_iff_mul_comm.mpr hck.eq
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p
    hp (Subgroup.zpowers g) A hP hcop hPnorm
  rw [hidem] at hB
  have hgA' : ∀ x ∈ A, g * x = x * g := by
    intro x hx
    have : ⁅x, g⁆ ∈ ⁅A, Subgroup.zpowers g⁆ :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers g)
    rw [hB, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp this).symm
  set T : Subgroup Y := U ⊔ Subgroup.zpowers z with hT
  have hT2 : IsPGroup 2 T := isPGroup_two_sup_zpowers hU hz
  have hzT : z ∈ T := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hzg : ∀ k : ℤ, g * z ^ k = z ^ k * g := fun k =>
    (Commute.zpow_right (show Commute g z from hgz) k).eq
  have hgT : g ∈ Subgroup.normalizer (T : Set Y) := by
    have hfwd : ∀ g' : Y, (∀ k : ℤ, g' * z ^ k = z ^ k * g') → ∀ y ∈ T, g' * y * g'⁻¹ ∈ T := by
      intro g' hg' y hy
      obtain ⟨n, hn, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have : g' * (n * z ^ k) * g'⁻¹ = (g' * n * g'⁻¹) * z ^ k := by
        calc g' * (n * z ^ k) * g'⁻¹ = (g' * n * g'⁻¹) * (g' * z ^ k * g'⁻¹) := by group
          _ = (g' * n * g'⁻¹) * z ^ k := by rw [hg' k]; group
      rw [this]
      exact T.mul_mem (Subgroup.mem_sup_left (Subgroup.Normal.conj_mem inferInstance n hn g'))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩))
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hfwd g hzg y hy, fun hy => ?_⟩
    have hzg' : ∀ k : ℤ, g⁻¹ * z ^ k = z ^ k * g⁻¹ := by
      intro k
      calc g⁻¹ * z ^ k = g⁻¹ * z ^ k * g * g⁻¹ := by group
        _ = g⁻¹ * (z ^ k * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * z ^ k) * g⁻¹ := by rw [hzg k]
        _ = z ^ k * g⁻¹ := by group
    have := hfwd g⁻¹ hzg' _ hy
    simpa [mul_assoc] using this
  have hall := commute_of_centralizer_le_fixed (p := 2) hT2 hgT hzT hgz
    (m := p ^ j) (Nat.Coprime.pow_left j hcop2) hgj (by
      intro x hx hxz
      obtain ⟨n, hn, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hnz : n * z = z * n := by
        have h3 : n * z ^ k * z = z * (n * z ^ k) := hxz
        have h4 : z ^ k * z = z * z ^ k := by rw [← zpow_one_add, add_comm, zpow_add_one]
        have : n * z * z ^ k = z * n * z ^ k := by
          calc n * z * z ^ k = n * (z * z ^ k) := by group
            _ = n * (z ^ k * z) := by rw [h4]
            _ = n * z ^ k * z := by group
            _ = z * (n * z ^ k) := h3
            _ = z * n * z ^ k := by group
        exact mul_right_cancel this
      have hnA : n ∈ A := ⟨hn, Subgroup.mem_centralizer_singleton_iff.mpr hnz⟩
      calc g * (n * z ^ k) = (g * n) * z ^ k := by group
        _ = (n * g) * z ^ k := by rw [hgA' n hnA]
        _ = n * (g * z ^ k) := by group
        _ = n * (z ^ k * g) := by rw [hzg k]
        _ = (n * z ^ k) * g := by group)
  have hgU : g ∈ Subgroup.centralizer (U : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hall x (Subgroup.mem_sup_left hx)).symm
  have hgU' : g ∈ U := hC hgU
  have h5 : (⟨g, hgU'⟩ : U) ^ p ^ j = 1 := Subtype.ext hgj
  exact hg1 (congrArg Subtype.val
    (eq_one_of_pow_eq_one_of_isPGroup hU (Nat.Coprime.pow_left j hcop2) h5))

theorem oddCore_eq_bot_of_isSubnormal_centralizer {U : Subgroup Y} [U.Normal] (hU : IsPGroup 2 U)
    (hC : Subgroup.centralizer (U : Set Y) ≤ U) {z : Y} (hz : z * z = 1) {L : Subgroup Y}
    (hL : IsSubnormal L (Subgroup.centralizer ({z} : Set Y))) :
    classicalInvolutionOddCore ↥L = ⊥ := by
  by_contra hne
  set N : Subgroup ↥L := classicalInvolutionOddCore ↥L with hN
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card L
  have hNn : N.Normal := inferInstance
  have hNnt : Nontrivial N := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact hne
  have hdvd : ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card N := by
    refine ⟨(Nat.card N).minFac, Nat.minFac_prime ?_, Nat.minFac_dvd _⟩
    have := Finite.one_lt_card (α := N)
    omega
  obtain ⟨p, hp, hpd⟩ := hdvd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hpd)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpd
  set g : Y := ((t : ↥L) : Y) with hg
  have hgJ : g ∈ L := (t : ↥L).2
  have hgp : g ^ p ^ 1 = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    have := congrArg (fun w : N => (((w : ↥L)) : Y)) h
    simpa [hg] using this
  have hg1 : g ≠ 1 := by
    intro h
    have : t = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at ht
    exact hp.one_lt.ne ht
  obtain ⟨x, hx, hnc⟩ := exists_not_commute_of_isSubnormal_centralizer_prime hU hC hz hL hp hp2
    hgJ hgp hg1
  apply hnc
  set x' : ↥L := ⟨x, hx.1⟩ with hx'
  set c : ↥L := (t : ↥L) * x' * (t : ↥L)⁻¹ * x'⁻¹ with hc
  have hcN : c ∈ N := by
    have h1 : x' * (t : ↥L)⁻¹ * x'⁻¹ ∈ N := hNn.conj_mem _ (N.inv_mem t.2) x'
    have h2 := N.mul_mem t.2 h1
    simpa [hc, mul_assoc] using h2
  have hcU : ((c : ↥L) : Y) ∈ U := by
    have : ((c : ↥L) : Y) = (g * x * g⁻¹) * x⁻¹ := by
      simp [hc, hg, hx', mul_assoc]
    rw [this]
    exact U.mul_mem (Subgroup.Normal.conj_mem inferInstance x hx.2 g) (U.inv_mem hx.2)
  obtain ⟨k, hk⟩ := hU ⟨_, hcU⟩
  have hck : c ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hodd : Odd (orderOf c) := hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hcN)
  have hc1 : c = 1 := by
    have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      ((Nat.coprime_two_right.mpr hodd).pow_right k) h2)
  have h3 : (t : ↥L) * x' = x' * (t : ↥L) := by
    calc (t : ↥L) * x' = c * x' * (t : ↥L) := by rw [hc]; group
      _ = x' * (t : ↥L) := by rw [hc1, one_mul]
  exact congrArg Subtype.val h3

end General

end SP3

section Exact

variable {Y : Type} [Group Y] [Finite Y]

theorem IsClassicalMember3.nonempty_equiv_sl2_of_solvable {U : Subgroup Y} [U.Normal]
    (hU : IsPGroup 2 U) (hC : Subgroup.centralizer (U : Set Y) ≤ U) {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember3 L z) : Nonempty (↥L ≃* SL(2, ZMod 3)) := by
  have hz2 : z * z = 1 := by rw [← sq, ← h.orderOf_eq_two]; exact pow_orderOf_eq_one z
  exact h.nonempty_equiv_sl2
    (SP3.oddCore_eq_bot_of_isSubnormal_centralizer hU hC hz2 h.subnormal)

end Exact

end CFSG.ClassicalInvolution.Q3
