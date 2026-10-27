module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.GH74.Generic.BProg.B1.PilotS3Facts

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup
  CFSG.GH74.Generic.BProg.B1.PilotS3
open scoped commutatorElement MatrixGroups

namespace S3T2L291

theorem sl23_comm_of_pow_eight :
    ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → ∃ a b : SL(2, ZMod 3), g = a * b * a⁻¹ * b⁻¹ := by
  decide

theorem sl23_pow_twelve : ∀ g : SL(2, ZMod 3), g ^ 12 = 1 := by
  decide

theorem sl23_pow_eight_of_two {g : SL(2, ZMod 3)} (h : ∃ k : ℕ, g ^ (2 ^ k) = 1) : g ^ 8 = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf g ∣ 12 := orderOf_dvd_of_pow_eq_one (sl23_pow_twelve g)
  obtain ⟨j, hj, hoj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hj2 : j ≤ 2 := by
    by_contra hj3
    have h8 : 2 ^ 3 ∣ orderOf g := by
      rw [hoj]
      exact Nat.pow_dvd_pow 2 (by omega)
    have := Nat.dvd_trans h8 h2
    omega
  refine orderOf_dvd_iff_pow_eq_one.1 ?_
  rw [hoj, show (8 : ℕ) = 2 ^ 3 by norm_num]
  exact Nat.pow_dvd_pow 2 (by omega)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_of_two_of_mul_odd {N O : Subgroup X} (hON : O ≤ normalizer (N : Set X))
    (hO : Odd (Nat.card ↥O)) {n o t : X} (hn : n ∈ N) (ho : o ∈ O) (ht : t = n * o)
    (h2 : ∃ k : ℕ, t ^ (2 ^ k) = 1) : t ∈ N := by
  set M : Subgroup X := N ⊔ O with hM
  have hNM : N ≤ M := le_sup_left
  have hOM : O ≤ M := le_sup_right
  have hMN : M ≤ normalizer (N : Set X) := sup_le Subgroup.le_normalizer hON
  set N' : Subgroup ↥M := N.subgroupOf M with hN'
  have hN'n : N'.Normal := ⟨fun a ha g => by
    rw [hN', Subgroup.mem_subgroupOf] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hMN g.2) a).1 ha⟩
  set q : ↥M →* ↥M ⧸ N' := QuotientGroup.mk' N' with hq
  have htM : t ∈ M := by rw [ht]; exact mul_mem (hNM hn) (hOM ho)
  have hqt : q ⟨t, htM⟩ = q ⟨o, hOM ho⟩ := by
    have e : (⟨t, htM⟩ : ↥M) = ⟨n, hNM hn⟩ * ⟨o, hOM ho⟩ := Subtype.ext ht
    rw [e, map_mul]
    have hn1 : q ⟨n, hNM hn⟩ = 1 := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
      exact hn
    rw [hn1, one_mul]
  have hodd : Odd (orderOf (q ⟨o, hOM ho⟩)) := by
    have h1 : orderOf (q ⟨o, hOM ho⟩) ∣ orderOf (⟨o, hOM ho⟩ : ↥M) := orderOf_map_dvd q _
    have h2 : orderOf (⟨o, hOM ho⟩ : ↥M) = orderOf (⟨o, ho⟩ : ↥O) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    have h3 : orderOf (⟨o, ho⟩ : ↥O) ∣ Nat.card ↥O := orderOf_dvd_natCard _
    exact Odd.of_dvd_nat hO (h1.trans (h2 ▸ h3))
  obtain ⟨k, hk⟩ := h2
  have h4 : orderOf (q ⟨t, htM⟩) ∣ 2 ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    have : (⟨t, htM⟩ : ↥M) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  rw [hqt] at h4
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
  have hj0 : j = 0 := by
    by_contra hj1
    rw [hj] at hodd
    exact Nat.not_even_iff_odd.2 hodd (Nat.even_pow.2 ⟨even_two, hj1⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff, ← hqt, hq, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf] at hj
  exact hj

theorem mem_of_isSolv2CompIn {F : Type} [Field F] [Finite F] {u : X} {J H X₀ I : Subgroup X}
    (hS : IsSplit3 F u J H) (hX₀ : X₀ ≤ H) (hI : IsSolv2CompIn X₀ I) {t : X} (ht : t ∈ I)
    (h2 : ∃ k : ℕ, t ^ (2 ^ k) = 1) : t ∈ J := by
  obtain ⟨Lb, -, ⟨eL⟩, rfl⟩ := hI
  obtain ⟨t', ht', rfl⟩ := ht
  set mk := QuotientGroup.mk' (pPrimeCore 2 ↥X₀) with hmk
  have ht'L : mk t' ∈ Lb := ht'
  have h2' : ∃ k : ℕ, (eL ⟨mk t', ht'L⟩) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨mk t', ht'L⟩ : ↥Lb) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← map_pow]
      have : t' ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
      rfl
    rw [this, map_one]
  obtain ⟨a, b, hab⟩ := sl23_comm_of_pow_eight _ (sl23_pow_eight_of_two h2')
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥X₀) ((eL.symm a : ↥Lb) : _)
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥X₀) ((eL.symm b : ↥Lb) : _)
  have hcomm : mk t' = mk (a' * b' * a'⁻¹ * b'⁻¹) := by
    have h1 : (⟨mk t', ht'L⟩ : ↥Lb) = eL.symm a * eL.symm b * (eL.symm a)⁻¹ * (eL.symm b)⁻¹ := by
      apply eL.injective
      rw [hab]
      simp
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [show mk a' = _ from ha', show mk b' = _ from hb']
  have ho : (a' * b' * a'⁻¹ * b'⁻¹)⁻¹ * t' ∈ pPrimeCore 2 ↥X₀ :=
    (QuotientGroup.eq (s := pPrimeCore 2 ↥X₀)).1 hcomm.symm
  set c : ↥X₀ := a' * b' * a'⁻¹ * b'⁻¹ with hc
  set o : ↥X₀ := c⁻¹ * t' with ho'
  have hcJ : (c : X) ∈ J := by
    have e : (c : X) = ⁅(a' : X), (b' : X)⁆ := by
      rw [hc, commutatorElement_def]
      simp
    rw [e]
    exact hS.comm _ (hX₀ a'.2) _ (hX₀ b'.2)
  have hoO : (o : X) ∈ pPrimeCoreOf 2 X₀ := ⟨o, ho, rfl⟩
  have hON : pPrimeCoreOf 2 X₀ ≤ normalizer (J : Set X) := by
    intro g hg
    have hgH : g ∈ H := hX₀ (TwoThin.pPrimeCoreOf_le X₀ hg)
    have hn := hS.normal
    rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · intro hj
      have := hn.conj_mem ⟨j, hS.le_H hj⟩ (Subgroup.mem_subgroupOf.2 hj) ⟨g, hgH⟩
      exact Subgroup.mem_subgroupOf.1 this
    · intro hj
      have := hn.conj_mem ⟨g * j * g⁻¹, hS.le_H hj⟩ (Subgroup.mem_subgroupOf.2 hj)
        ⟨g, hgH⟩⁻¹
      have e : ((⟨g, hgH⟩⁻¹ * ⟨g * j * g⁻¹, hS.le_H hj⟩ * (⟨g, hgH⟩⁻¹)⁻¹ : ↥H) : X) = j := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      rw [← e]
      exact Subgroup.mem_subgroupOf.1 this
  refine mem_of_two_of_mul_odd hON (TwoThin.card_pPrimeCoreOf_odd X₀) hcJ hoO ?_ h2
  rw [ho']
  simp

end S3T2L291

end CFSG.GH74.Generic.BProg.B3
