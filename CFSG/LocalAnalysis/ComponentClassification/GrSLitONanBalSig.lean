module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalL34

public section

namespace CFSG.ComponentClassification.GrSLit.ONanBal

open Subgroup CFSG.OddStandard CFSG.OddStandard.ONanRec CFSG.OddStandard.ONanRec.F2
  CFSG.ABGLocalTools

theorem odd_eq_one_of_commute_l34
    {Y : Type} [Group Y] (hY : CFSG.Blueprint.LieModel Y .PSL 3 2 2) {t g : Y}
    (ht : orderOf t = 2) (hg : Odd (orderOf g)) (hc : g * t = t * g) : g = 1 := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.L34.equiv_of_lieModel hY
  set y : Equiv.Perm (Fin 42) := (e t : Equiv.Perm (Fin 42)) with hy
  set h : Equiv.Perm (Fin 42) := (e g : Equiv.Perm (Fin 42)) with hh
  have hyo : orderOf y = 2 := by
    rw [hy, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  have hy2 : y ^ 2 = 1 := by rw [← hyo, pow_orderOf_eq_one]
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyo
    omega
  obtain ⟨c, hcP, hcy⟩ := CFSG.GH74.KGroups.L34.one_class_P y (e t).2 hy2 hy1
  have hhy : h * y = y * h := by
    rw [hh, hy, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc]
  have hmem : c⁻¹ * h * c ∈ CFSG.GH74.KGroups.L34.QP.originalSubgroup ⊓
      centralizer ({CFSG.GH74.KGroups.L34.x0} : Set (Equiv.Perm (Fin 42))) := by
    refine mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hcP) (e g).2) hcP, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hx0 : CFSG.GH74.KGroups.L34.x0 = c⁻¹ * y * c := by rw [← hcy]; group
    rw [hx0]
    calc c⁻¹ * h * c * (c⁻¹ * y * c) = c⁻¹ * (h * y) * c := by group
      _ = c⁻¹ * (y * h) * c := by rw [hhy]
      _ = c⁻¹ * y * c * (c⁻¹ * h * c) := by group
  have hdvd : orderOf (c⁻¹ * h * c) ∣ 64 := by
    rw [← CFSG.GH74.KGroups.L34.card_CP, ← Subgroup.orderOf_mk (c⁻¹ * h * c) hmem]
    exact orderOf_dvd_natCard _
  have ho : orderOf (c⁻¹ * h * c) = orderOf g := by
    rw [show c⁻¹ * h * c = MulAut.conj c⁻¹ h by simp, MulEquiv.orderOf_eq,
      hh, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  rw [ho] at hdvd
  have h1 : orderOf g = 1 := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show orderOf g ∣ 2 ^ 6 by norm_num; exact hdvd)
    rcases k with _ | k
    · simpa using hk
    · exfalso
      rw [hk, pow_succ] at hg
      exact (Nat.not_even_iff_odd.mpr hg) (even_iff_two_dvd.mpr (dvd_mul_left 2 _))
  exact orderOf_eq_one_iff.1 h1

theorem conj_pow_odd_of_inv {G : Type} [Group G] {a y : G} (h : a * y * a⁻¹ = y⁻¹) :
    ∀ k : ℕ, a ^ (2 * k + 1) * y * (a ^ (2 * k + 1))⁻¹ = y⁻¹ := by
  have h2 : a * a * y = y * (a * a) := by
    have e : a * a * y * (a * a)⁻¹ = y := by
      calc a * a * y * (a * a)⁻¹ = a * (a * y * a⁻¹) * a⁻¹ := by group
        _ = a * y⁻¹ * a⁻¹ := by rw [h]
        _ = (a * y * a⁻¹)⁻¹ := by group
        _ = y := by rw [h, inv_inv]
    calc a * a * y = a * a * y * (a * a)⁻¹ * (a * a) := by group
      _ = y * (a * a) := by rw [e]
  intro k
  have hc : Commute ((a * a) ^ k) y := Commute.pow_left h2 k
  have e : a ^ (2 * k + 1) = a * (a * a) ^ k := by rw [pow_succ', pow_mul, sq]
  rw [e]
  generalize (a * a) ^ k = b at hc ⊢
  calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by
        rw [mul_inv_rev]
        simp only [mul_assoc]
    _ = a * y * a⁻¹ := by rw [hc.eq, mul_inv_cancel_right]
    _ = y⁻¹ := h

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G}

local notation "𝔵" => xel v1 v2 v3
local notation "𝔷" => invRep v1 v2 v3 s t 0

theorem theta_x_of_mem (D : FusCtx G v1 v2 v3 s t) {k : G} (hk : k ∈ theta 𝔷)
    (hkx : k ∈ centralizer ({𝔵} : Set G)) : k ∈ theta 𝔵 := by
  set Cx := centralizer ({𝔵} : Set G) with hCx
  set N := (theta 𝔷).subgroupOf Cx with hN
  have hNn : N.Normal := by
    refine ⟨fun a ha c => mem_subgroupOf.2 ?_⟩
    have hc : (c : G) ∈ normalizer (centralizer ({𝔷} : Set G) : Set G) :=
      le_normalizer (centralizer_x_le_z D c.2)
    exact conj_mem_oddCore_map hc (mem_subgroupOf.1 ha)
  have hNo : Odd (Nat.card N) := by
    have e : Nat.card N = Nat.card (theta 𝔷 ⊓ Cx : Subgroup G) := by
      rw [← Subgroup.subgroupOf_map_subtype, card_map_of_injective Cx.subtype_injective]
    rw [e]
    exact Odd.of_dvd_nat (odd_card_theta 𝔷) (card_dvd_of_le inf_le_left)
  have hle : N ≤ pPrimeCore 2 Cx := le_sSup ⟨hNn, Nat.coprime_two_left.2 hNo⟩
  exact ⟨⟨k, hkx⟩, hle (mem_subgroupOf.2 hk), rfl⟩

theorem mem_theta_z_of_odd
    (D : FusCtx G v1 v2 v3 s t) (hF : ThmC.ThmCFull) (hone : OneClass G) {w : G}
    (hwW : w ∈ alpW v1 v2 v3) (hw1 : w ≠ 1) (hwz : w ≠ 𝔷) {g : G}
    (hgz : g ∈ centralizer ({𝔷} : Set G)) (hgw : g * w = w * g) (hg : Odd (orderOf g)) :
    g ∈ theta 𝔷 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cz := centralizer ({𝔷} : Set G) with hCz
  set Cx := centralizer ({𝔵} : Set G) with hCx
  set m := orderOf g with hm
  have hwV : w ∈ alpV v1 v2 v3 := D.W_le_V hwW
  have hw2 : w * w = 1 := (D.mem_W_iff.1 hwW).2
  have hwx : w ∈ Cx := mem_centralizer_singleton_iff.2 (D.comm_V hwV D.x_mem_V)
  have hwCz : w ∈ Cz := centralizer_x_le_z D hwx
  obtain ⟨o, ho, hn⟩ := exists_conj_x_mod_theta D hone hgz
  have hoCz : o ∈ Cz := theta_le_centralizer 𝔷 ho
  set n := o * g with hndef
  have hnCz : n ∈ Cz := mul_mem hoCz hgz
  have hnm : n ^ m ∈ theta 𝔷 := by
    obtain ⟨o₀, ho₀, ho₀e⟩ := ho
    have h0 : QuotientGroup.mk' (pPrimeCore 2 Cz) o₀ = 1 := (QuotientGroup.eq_one_iff _).2 ho₀
    have hg1 : (⟨g, hgz⟩ : Cz) ^ m = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow]
      exact pow_orderOf_eq_one g)
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 Cz)) ((o₀ * ⟨g, hgz⟩) ^ m) = 1 := by
      rw [map_pow, map_mul, h0, one_mul, ← map_pow, hg1, map_one]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have ho₀e' : (o₀ : G) = o := ho₀e
    refine ⟨_, h1, ?_⟩
    show (((o₀ * ⟨g, hgz⟩) ^ m : Cz) : G) = n ^ m
    rw [SubgroupClass.coe_pow, Subgroup.coe_mul, ho₀e']
  have hnx : n * 𝔵 * n⁻¹ = 𝔵 := by
    rcases hn with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨j, hj⟩ := hg
      have hb := conj_pow_odd_of_inv h1 j
      rw [← hj] at hb
      have hodd : Odd (orderOf (n ^ m)) := by
        have hd : orderOf (⟨n ^ m, hnm⟩ : theta 𝔷) ∣ Nat.card (theta 𝔷) := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk] at hd
        exact Odd.of_dvd_nat (odd_card_theta 𝔷) hd
      obtain ⟨q, hq⟩ := hodd
      have hb' := conj_pow_odd_of_inv hb q
      rw [← hq, pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hb'
      exact D.x_ne_inv hb'
  have hnCx : n ∈ Cx := mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hnx)
  have hnw : n * w * n⁻¹ * w⁻¹ ∈ theta 𝔷 := by
    have e : n * w * n⁻¹ * w⁻¹ = o * (w * o⁻¹ * w⁻¹) := by
      rw [hndef]
      calc o * g * w * (o * g)⁻¹ * w⁻¹ = o * (g * w) * g⁻¹ * o⁻¹ * w⁻¹ := by group
        _ = o * (w * g) * g⁻¹ * o⁻¹ * w⁻¹ := by rw [hgw]
        _ = o * (w * o⁻¹ * w⁻¹) := by group
    rw [e]
    exact mul_mem ho (conj_mem_oddCore_map (le_normalizer hwCz) (inv_mem ho))
  have hnwx : n * w * n⁻¹ * w⁻¹ ∈ theta 𝔵 :=
    theta_x_of_mem D hnw (mul_mem (mul_mem (mul_mem hnCx hwx) (inv_mem hnCx)) (inv_mem hwx))
  have hnmx : n ^ m ∈ theta 𝔵 := theta_x_of_mem D hnm (pow_mem hnCx m)
  set π : Cx →* KQO 𝔵 := (QuotientGroup.mk' (pPrimeCore 2 (KQ 𝔵))).comp (πQ 𝔵) with hπ
  have hcen : zpowers (zIn 𝔵) ≤ center Cx :=
    zpowers_le.2 (Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext (mem_centralizer_singleton_iff.1 y.2))
  have hcore : pPrimeCore 2 (KQ 𝔵) = (pPrimeCore 2 Cx).map (πQ 𝔵) :=
    CFSG.central_p_subgroup_prime_core_quotient _ hcen D.isPGroup_zpowers_zIn_x
  have hπθ : ∀ k : Cx, (k : G) ∈ theta 𝔵 → π k = 1 := by
    intro k hk
    obtain ⟨k', hk', hkk⟩ := hk
    have e : k' = k := Subtype.ext hkk
    subst e
    rw [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcore]
    exact mem_map_of_mem _ hk'
  set nC : Cx := ⟨n, hnCx⟩
  set wC : Cx := ⟨w, hwx⟩
  have hcomm : π nC * π wC = π wC * π nC := by
    have h1 := hπθ (nC * wC * nC⁻¹ * wC⁻¹) hnwx
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π nC * π wC = π nC * π wC * (π nC)⁻¹ * (π wC)⁻¹ * (π wC * π nC) := by group
      _ = π wC * π nC := by rw [h1, one_mul]
  have hpow : π nC ^ m = 1 := by
    rw [← map_pow]
    exact hπθ (nC ^ m) hnmx
  have hwo : orderOf (π wC) = 2 := by
    have hq1 : πQ 𝔵 wC ≠ 1 := by
      rw [Ne, πQ_eq_one_iff]
      intro h
      rcases D.mem_zpowers_x.1 h with h1 | h1 | h1 | h1
      · exact hw1 h1
      · apply D.rep_ne_one 0
        have h' : w = 𝔵 := h1
        rw [← D.xel_sq, ← h', hw2]
      · exact hwz h1
      · apply D.rep_ne_one 0
        have h' : w = 𝔵⁻¹ := h1
        have e : invRep v1 v2 v3 s t 0 = (w * w)⁻¹ := by
          rw [h', ← mul_inv_rev, inv_inv, D.xel_sq]
        rw [e, hw2, inv_one]
    have hq2 : (πQ 𝔵 wC) ^ 2 = 1 := by
      rw [← map_pow, show wC ^ 2 = 1 from Subtype.ext (by
        rw [SubgroupClass.coe_pow, pow_two]
        exact hw2), map_one]
    have hqo : orderOf (πQ 𝔵 wC) = 2 := orderOf_eq_prime hq2 hq1
    have hqp : IsPGroup 2 (zpowers (πQ 𝔵 wC)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hqo, pow_one])
    rw [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      orderOf_mk_eq (pPrimeCore_two_facts (X := KQ 𝔵)).2 hqp, hqo]
  have hno : Odd (orderOf (π nC)) := Odd.of_dvd_nat hg (orderOf_dvd_of_pow_eq_one hpow)
  have hn1 := odd_eq_one_of_commute_l34 (lieModel_quot_core D hF hone) hwo hno hcomm
  rw [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcore] at hn1
  obtain ⟨o₁, ho₁, ho₁e⟩ := hn1
  have hx : (o₁ : G)⁻¹ * n ∈ zpowers 𝔵 := (πQ_eq_iff o₁ nC).1 ho₁e
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hx
  have hn_eq : n = (o₁ : G) * 𝔵 ^ j := by rw [hj]; group
  have ho₁x : Commute (o₁ : G) 𝔵 := (mem_centralizer_singleton_iff.1 o₁.2)
  have ho₁θ : (o₁ : G) ∈ theta 𝔵 := ⟨o₁, ho₁, rfl⟩
  have hxjm : (𝔵 ^ j) ^ m ∈ theta 𝔵 := by
    have e : (𝔵 ^ j) ^ m = ((o₁ : G) ^ m)⁻¹ * n ^ m := by
      rw [hn_eq, (ho₁x.zpow_right j).mul_pow]
      group
    rw [e]
    exact mul_mem (inv_mem (pow_mem ho₁θ m)) hnmx
  have hxjm1 : (𝔵 ^ j) ^ m = 1 := by
    have hz : (𝔵 ^ j) ^ m ∈ zpowers 𝔵 ⊓ theta 𝔵 :=
      mem_inf.2 ⟨pow_mem (zpow_mem (mem_zpowers 𝔵) j) m, hxjm⟩
    have hp : IsPGroup 2 (zpowers 𝔵) := isPGroup_zpowers_of_pow_two (k := 2) (by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact D.x_pow_four)
    rw [CFSG.RankThree.OddKernel.inf_eq_bot_of_odd hp (odd_card_theta 𝔵), mem_bot] at hz
    exact hz
  have hxj1 : 𝔵 ^ j = 1 := by
    have hd : orderOf (𝔵 ^ j) ∣ m := orderOf_dvd_of_pow_eq_one hxjm1
    have hd4 : orderOf (𝔵 ^ j) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        show (2 : ℕ) ^ 2 = 4 by norm_num, D.x_pow_four, one_zpow])
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd4
    rcases k with _ | k
    · exact orderOf_eq_one_iff.1 (by simpa using hk)
    · exfalso
      rw [hk, pow_succ] at hd
      exact (Nat.not_even_iff_odd.mpr hg) (even_iff_two_dvd.mpr ((dvd_mul_left 2 _).trans hd))
  have hnθ : n ∈ theta 𝔵 := by
    rw [hn_eq, hxj1, mul_one]
    exact ho₁θ
  have hg_eq : g = o⁻¹ * n := by rw [hndef]; group
  rw [hg_eq]
  exact mul_mem (inv_mem ho) (theta_x_le_theta_z D hone hnθ)

end CFSG.ComponentClassification.GrSLit.ONanBal
