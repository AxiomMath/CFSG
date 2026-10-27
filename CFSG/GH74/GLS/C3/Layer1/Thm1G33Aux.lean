module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.GH74.GLS.C3.Layer1.Thm1P310Two
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem klein_cases {x f w : G} (hx : x * x = 1) (hf : f * f = 1) (hxf : x * f = f * x)
    (hw : w ∈ zpowers x ⊔ zpowers f) : w = 1 ∨ w = x ∨ w = f ∨ w = x * f := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Thm1P310.exists_mul_of_mem_sup (P := zpowers x) (D := zpowers f)
    (fun u hu w hw => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
      exact (Commute.zpow_zpow (show Commute x f from hxf) i j).eq) hw
  rcases Thm1P310.eq_one_or_eq_of_mem_zpowers hx hu with h1 | h1 <;>
    rcases Thm1P310.eq_one_or_eq_of_mem_zpowers hf hv with h2 | h2 <;> rw [h1, h2]
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inr (Or.inl (by simp)))
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem exists_pow_not_mem_sq_mem {V : Subgroup G} {b : G} (hb2 : ∃ k : ℕ, b ^ (2 ^ k) = 1)
    (hb : b ∉ V) : ∃ c ∈ zpowers b, c ∉ V ∧ c ^ 2 ∈ V := by
  classical
  have hex : ∃ j : ℕ, b ^ (2 ^ (j + 1)) ∈ V := by
    obtain ⟨k, hk⟩ := hb2
    refine ⟨k, ?_⟩
    rw [pow_succ, pow_mul, hk, one_pow]
    exact V.one_mem
  let j := Nat.find hex
  have hj : b ^ (2 ^ (j + 1)) ∈ V := Nat.find_spec hex
  have hjnot : b ^ (2 ^ j) ∉ V := by
    by_cases h0 : j = 0
    · rw [h0]; simpa using hb
    · obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero h0
      have := Nat.find_min hex (show i < j by omega)
      rw [hi]
      simpa [Nat.succ_eq_add_one] using this
  refine ⟨b ^ (2 ^ j), ?_, hjnot, ?_⟩
  · exact (mem_zpowers_iff).2 ⟨((2 ^ j : ℕ) : ℤ), by rw [zpow_natCast]⟩
  · rw [← pow_mul, ← pow_succ]; exact hj

theorem exists_mem_normalizer_not_mem [Finite G] {V W : Subgroup G} (hVW : V ≤ W) (hne : V ≠ W)
    (hW2 : IsPGroup 2 ↥W) :
    ∃ b ∈ W, b ∈ normalizer (V : Set G) ∧ b ∉ V := by
  have hnil : Group.IsNilpotent ↥W := hW2.isNilpotent
  have hnc : NormalizerCondition ↥W := Group.normalizerCondition_of_isNilpotent
  set U : Subgroup ↥W := V.subgroupOf W with hU
  have hUtop : U < ⊤ := by
    refine lt_top_iff_ne_top.2 (fun h => hne ?_)
    apply le_antisymm hVW
    intro w hw
    have : (⟨w, hw⟩ : ↥W) ∈ U := by rw [h]; exact Subgroup.mem_top _
    exact this
  have hlt := hnc U hUtop
  obtain ⟨b, hbN, hbU⟩ := IsConcreteLE.exists_of_lt hlt
  have hbV : (b : G) ∉ V := hbU
  refine ⟨b, b.2, ?_, hbV⟩
  rw [Subgroup.mem_normalizer_iff] at hbN ⊢
  intro h
  constructor
  · intro hh
    have hhW : h ∈ W := hVW hh
    have := (hbN ⟨h, hhW⟩).1 hh
    exact this
  · intro hh
    have hhW : h ∈ W := by
      have h1 : (b : G)⁻¹ * ((b : G) * h * (b : G)⁻¹) * (b : G) ∈ W :=
        W.mul_mem (W.mul_mem (W.inv_mem b.2) (hVW hh)) b.2
      simpa [mul_assoc] using h1
    exact (hbN ⟨h, hhW⟩).2 hh

theorem mem_of_isSylowOf_of_normalizes [Finite G] {V H : Subgroup G} (hSyl : IsSylowOf 2 V H)
    {b : G} (hbH : b ∈ H) (hbN : b ∈ normalizer (V : Set G))
    (hb2 : ∃ k : ℕ, b ^ (2 ^ k) = 1) : b ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 ↥(zpowers b) := by
    obtain ⟨k, hk⟩ := hb2
    intro g
    obtain ⟨g, j, rfl⟩ := g
    refine ⟨k, Subtype.ext ?_⟩
    show (b ^ j) ^ (2 ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hN : zpowers b ≤ normalizer (V : Set G) := (zpowers_le).2 hbN
  have hP2 : IsPGroup 2 ↥(V ⊔ zpowers b) := hSyl.isPGroup.to_sup_of_normal_left' hzp hN
  have hle : V ⊔ zpowers b ≤ H := sup_le hSyl.le ((zpowers_le).2 hbH)
  have heq := hSyl.eq_of_le le_sup_left hle hP2
  rw [← heq]
  exact Subgroup.mem_sup_right (mem_zpowers b)

theorem hom_central_involution_eq_one {H : Type} [Group H] {C : Type} [Group C]
    (hCc : ∀ u v : C, u * v = v * u) {a x f : H} (hf : f ∈ zpowers a) (hf2 : f * f = 1)
    (hf1 : f ≠ 1) (hN : ∃ k : ℕ, orderOf a = 2 ^ k) (hxa : x * a * x⁻¹ ∈ zpowers a)
    (hne : x * a * x⁻¹ ≠ a) (ψ : H →* C) : ψ f = 1 := by
  obtain ⟨k, hk⟩ := hN
  obtain ⟨t, ht⟩ := mem_zpowers_iff.1 hxa
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hf
  set c : C := ψ a with hc
  have hc1 : c ^ (t - 1) = 1 := by
    have h1 : ψ (x * a * x⁻¹) = c := by
      rw [map_mul, map_mul, map_inv, hCc (ψ x) c, mul_assoc, mul_inv_cancel, mul_one]
    rw [← ht, map_zpow] at h1
    rw [zpow_sub_one, h1, mul_inv_cancel]
  have hc2 : c ^ (2 ^ k) = 1 := by
    rw [hc, ← map_pow, ← hk, pow_orderOf_eq_one, map_one]
  have hnot : ¬ (((2 ^ k : ℕ) : ℤ) ∣ t - 1) := by
    intro hd
    apply hne
    rw [← ht]
    have : a ^ (t - 1) = 1 := by
      rw [← hk] at hd
      exact orderOf_dvd_iff_zpow_eq_one.1 hd
    rw [zpow_sub_one] at this
    exact (mul_inv_eq_one.1 this)
  have hcm2 : ((2 ^ k : ℕ) : ℤ) ∣ 2 * m := by
    rw [← hk]
    refine orderOf_dvd_iff_zpow_eq_one.2 ?_
    have : a ^ (2 * m) = (a ^ m) ^ (2 : ℤ) := by rw [mul_comm, zpow_mul]
    rw [this, hm, zpow_two]
    exact hf2
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hf1
    have : a = 1 := orderOf_eq_one_iff.1 (by simpa using hk)
    rw [← hm, this, one_zpow]
  have hkm : (((2 ^ (k - 1) : ℕ) : ℤ) ∣ m) := by
    have h2k : (2 ^ k : ℕ) = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2k] at hcm2
    push_cast at hcm2
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).1 hcm2
  have hord : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc2
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hjk' : j < k := by
    rcases hjk.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hnot
      have : (orderOf c : ℤ) ∣ t - 1 := orderOf_dvd_iff_zpow_eq_one.2 hc1
      rw [hj, h] at this
      exact this
  have hdvd : (orderOf c : ℤ) ∣ m := by
    refine dvd_trans ?_ hkm
    rw [hj]
    exact_mod_cast pow_dvd_pow 2 (by omega : j ≤ k - 1)
  rw [← hm, map_zpow]
  exact orderOf_dvd_iff_zpow_eq_one.1 hdvd

end CFSG.GH74.GLS.C3.Layer1.Thm1G33
