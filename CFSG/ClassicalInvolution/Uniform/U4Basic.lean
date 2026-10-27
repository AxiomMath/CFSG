module

public import CFSG.ClassicalInvolution.Asc77.ModOApi
public import CFSG.ClassicalInvolution.Uniform.UOmega4

public section

namespace CFSG.ClassicalInvolution.Uniform.U4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

structure Mem3 (K : Subgroup F) (z : F) : Prop where
  member : IsClassicalMemberU (.sl2 3 1) K z
  intrinsic : IsIntrinsicU (.sl2 3 1) K z

theorem solvableType_three : (MemberType.sl2 3 1).IsSolvableType := by
  show 3 ^ 1 = 3
  norm_num

namespace Mem3

variable {K J : Subgroup F} {z t : F}

omit [Finite F] in
theorem orderOf_eq_two (h : Mem3 K z) : orderOf z = 2 := h.member.orderOf_eq_two

omit [Finite F] in
theorem mem (h : Mem3 K z) : z ∈ K := h.member.mem

omit [Finite F] in
theorem mul_self (h : Mem3 K z) : z * z = 1 := h.member.mul_self

omit [Finite F] in
theorem ne_one (h : Mem3 K z) : z ≠ 1 := h.member.ne_one

omit [Finite F] in
theorem le_centralizer (h : Mem3 K z) : K ≤ Subgroup.centralizer ({z} : Set F) :=
  h.member.le_centralizer

omit [Finite F] in
theorem mul_comm_of_mem (h : Mem3 K z) {k : F} (hk : k ∈ K) : k * z = z * k :=
  (h.member.comm_of_mem hk).symm

omit [Finite F] in
theorem subnormal (h : Mem3 K z) : IsSubnormal K (Subgroup.centralizer ({z} : Set F)) :=
  h.member.subnormal

theorem isUniqueInvolution (h : Mem3 K z) : IsUniqueInvolution K z :=
  h.member.isUniqueInvolution (MemberType.cert_sl2 3 1)

omit [Finite F] in
theorem conj (h : Mem3 K z) (g : F) : Mem3 (conjSub g K) (g * z * g⁻¹) :=
  ⟨h.member.conj g, h.intrinsic.conj g⟩

omit [Finite F] in
theorem conj_of_commute (h : Mem3 K z) {c : F} (hc : c * z = z * c) : Mem3 (conjSub c K) z := by
  have h1 := h.conj c
  have h2 : c * z * c⁻¹ = z := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rwa [h2] at h1

theorem twin_facts {K₁ K₂ : Subgroup F} (h₁ : Mem3 K₁ z) (h₂ : Mem3 K₂ z) (hne : K₁ ≠ K₂) :
    K₂ ≤ Subgroup.normalizer (K₁ : Set F) ∧ K₁ ≤ Subgroup.normalizer (K₂ : Set F) ∧
      ⁅K₁, K₂⁆ ≤ oddCoreOf K₁ ⊓ oddCoreOf K₂ := by
  obtain ⟨a, b, c, -⟩ := twins_of_memberU h₁.member h₂.member h₁.intrinsic h₂.intrinsic hne
  exact ⟨a, b, c⟩

theorem twin_facts_conj (h : Mem3 K z) {c : F} (hc : c * z = z * c) (hne : K ≠ conjSub c K) :
    Mem3 (conjSub c K) z ∧ conjSub c K ≤ Subgroup.normalizer (K : Set F) ∧
      K ≤ Subgroup.normalizer (conjSub c K : Set F) ∧
        ⁅K, conjSub c K⁆ ≤ oddCoreOf K ⊓ oddCoreOf (conjSub c K) := by
  have h' := h.conj_of_commute hc
  obtain ⟨a, b, c'⟩ := h.twin_facts h' hne
  exact ⟨h', a, b, c'⟩

theorem commutator_mem_of_twin {K₁ K₂ : Subgroup F} (h₁ : Mem3 K₁ z) (h₂ : Mem3 K₂ z)
    (hne : K₁ ≠ K₂) {x : F} (hx : x ∈ K₂) : ∀ u ∈ K₁, ⁅x, u⁆ ∈ oddCoreOf K₁ := by
  intro u hu
  obtain ⟨-, -, hc⟩ := h₁.twin_facts h₂ hne
  rw [← commutatorElement_inv]
  exact (oddCoreOf K₁).inv_mem (hc (Subgroup.commutator_mem_commutator hu hx)).1

theorem eq_of_mem_of_mem_same {K₁ K₂ : Subgroup F} (h₁ : Mem3 K₁ z) (h₂ : Mem3 K₂ z) {a : F}
    (ha₁ : a ∈ K₁) (ha₂ : a ∈ K₂) (ha2 : IsPGroup 2 (Subgroup.zpowers a)) (ha4 : 4 ≤ orderOf a) :
    K₁ = K₂ := by
  by_contra hne
  obtain ⟨-, -, hc⟩ := h₁.twin_facts h₂ hne
  have hle : padicValNat 2 (Nat.card ↥(K₁ ⊓ K₂)) ≤ 1 :=
    padicValNat_card_inf_le_one_of_commutator (hc.trans inf_le_left)
      h₁.member.natCard_center_eq_two
  obtain ⟨n, hn⟩ := ha2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 4 ∣ Nat.card ↥(K₁ ⊓ K₂) := by
    have h4 : 4 ∣ orderOf a := by
      rw [hn]
      exact (pow_dvd_pow 2 hn2 : 2 ^ 2 ∣ 2 ^ n)
    exact h4.trans (Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨ha₁, ha₂⟩))
  have hpos : Nat.card ↥(K₁ ⊓ K₂) ≠ 0 := Nat.card_pos.ne'
  have := (padicValNat_dvd_iff_le (p := 2) (n := 2) hpos).mp (by simpa using hdvd)
  omega

theorem eq_of_mem_of_mem {K₁ K₂ : Subgroup F} {z₁ z₂ : F} (h₁ : Mem3 K₁ z₁) (h₂ : Mem3 K₂ z₂)
    {a : F} (ha₁ : a ∈ K₁) (ha₂ : a ∈ K₂) (ha2 : IsPGroup 2 (Subgroup.zpowers a))
    (ha4 : 4 ≤ orderOf a) : K₁ = K₂ := by
  have hsame : z₁ = z₂ := by
    obtain ⟨n, hn⟩ := ha2.exists_card_eq
    rw [Nat.card_zpowers] at hn
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    set b : F := a ^ (2 ^ (n - 1)) with hb
    have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hb2 : b * b = 1 := by
      have : b * b = a ^ (2 ^ n) := by
        rw [hb, ← pow_add]
        congr 1
        omega
      rw [this, ← hn]
      exact pow_orderOf_eq_one a
    have hb1 : b ≠ 1 := by
      intro h1
      have hdvd : orderOf a ∣ 2 ^ (n - 1) := orderOf_dvd_of_pow_eq_one h1
      have hle := Nat.le_of_dvd (by positivity) hdvd
      have h3 : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hb₁ : b ∈ K₁ := K₁.pow_mem ha₁ _
    have hb₂ : b ∈ K₂ := K₂.pow_mem ha₂ _
    have e1 : b = z₁ := (h₁.isUniqueInvolution.unique b hb₁ hb2).resolve_left hb1
    have e2 : b = z₂ := (h₂.isUniqueInvolution.unique b hb₂ hb2).resolve_left hb1
    exact e1.symm.trans e2
  subst hsame
  exact eq_of_mem_of_mem_same h₁ h₂ ha₁ ha₂ ha2 ha4

theorem centralizer_le_normalizer (h : Mem3 K z) {x : F} (hx : x ∈ K)
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hx4 : 4 ≤ orderOf x) :
    Subgroup.centralizer ({x} : Set F) ≤ Subgroup.normalizer (K : Set F) := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  apply AscHypOmega.mem_normalizer_of_conjSub_eq
  have hKc := h.conj c
  have hxc : x ∈ conjSub c K := by
    have := conj_mem_conjSub (n := c) hx
    have hck : c * x * c⁻¹ = x := by rw [mul_inv_eq_iff_eq_mul]; exact hc
    rwa [hck] at this
  exact (eq_of_mem_of_mem h hKc hx hxc hx2 hx4).symm

theorem mem_normalizer_of_commute_of_mem_noncentral (h : Mem3 J t) {v : F} (hvJ : v ∈ J)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hv3 : 3 ≤ Nat.card (Subgroup.zpowers v)) {y : F}
    (hyv : y * v = v * y) : y ∈ Subgroup.normalizer (J : Set F) := by
  rw [Nat.card_zpowers] at hv3
  have hv4 : 4 ≤ orderOf v := by
    obtain ⟨n, hn⟩ := hv2.exists_card_eq
    rw [Nat.card_zpowers] at hn
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  exact h.centralizer_le_normalizer hvJ hv2 hv4 ((Subgroup.mem_centralizer_singleton_iff).mpr hyv)

end Mem3

section OddQuotient

omit [Finite F] in
theorem forall_comm_of_mk_mem_center {K : Subgroup F} {a : F} (haK : a ∈ K)
    (h : (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : OddQuot K) ∈ Subgroup.center (OddQuot K)) :
    ∀ u ∈ K, ⁅a, u⁆ ∈ oddCoreOf K := by
  intro u hu
  have h1 := (Subgroup.mem_center_iff.mp h) (QuotientGroup.mk (⟨u, hu⟩ : ↥K))
  have hmem : ⁅a, u⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem haK hu) (K.inv_mem haK)) (K.inv_mem hu)
  refine mem_oddCoreOf_iff.mpr ⟨hmem, ?_⟩
  have h2 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) ⁅(⟨a, haK⟩ : ↥K), ⟨u, hu⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h1.symm
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  convert h2 using 1

omit [Finite F] in
theorem mk_mem_center_of_forall {K : Subgroup F} {a : F} (haK : a ∈ K)
    (h : ∀ u ∈ K, ⁅a, u⁆ ∈ oddCoreOf K) :
    (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : OddQuot K) ∈ Subgroup.center (OddQuot K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨hm, hmo⟩ := mem_oddCoreOf_iff.mp (h x x.2)
  have h2 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) ⁅(⟨a, haK⟩ : ↥K), x⁆ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    convert hmo using 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2.symm

theorem eq_of_mk_eq {K R : Subgroup F} (hR2 : IsPGroup 2 R) {x y : F} (hxR : x ∈ R)
    (hyR : y ∈ R) (hxK : x ∈ K) (hyK : y ∈ K)
    (h : (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : OddQuot K) = QuotientGroup.mk (⟨y, hyK⟩ : ↥K)) :
    x = y := by
  rw [QuotientGroup.eq] at h
  have hmem : x⁻¹ * y ∈ oddCoreOf K :=
    mem_oddCoreOf_iff.mpr ⟨K.mul_mem (K.inv_mem hxK) hyK, h⟩
  have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hmem
    (hR2.to_le (Subgroup.zpowers_le.mpr (R.mul_mem (R.inv_mem hxR) hyR)))
  exact (inv_mul_eq_one.mp h1)

end OddQuotient

end CFSG.ClassicalInvolution.Uniform.U4
