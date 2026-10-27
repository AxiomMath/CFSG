module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RThmI

public section

namespace CFSG.ClassicalInvolution.Hat2A7R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement

section Statements

@[expose] def Prop366i : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ (J K : Subgroup F) (t z : F), IsClassical2A7 ⊤ J t → IsClassical2A7 ⊤ K z →
      ∀ y ∈ J, IsPGroup 2 (Subgroup.zpowers y) → 4 ≤ orderOf y → y * z = z * y →
        y ∈ Subgroup.normalizer (K : Set F)

@[expose] def Prop369iii : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ (J K : Subgroup F) (t z : F), IsClassical2A7 ⊤ J t → IsClassical2A7 ⊤ K z →
      z ∈ Subgroup.normalizer (J : Set F) → t ∉ Subgroup.normalizer (K : Set F) →
        ∀ a ∈ J, orderOf a = 4 → ¬ a * z = z * a

@[expose] def Prop37x : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ (J K : Subgroup F) (t z : F), IsClassical2A7 ⊤ J t → IsClassical2A7 ⊤ K z →
      z ∈ Subgroup.normalizer (J : Set F) → t ∈ Subgroup.normalizer (K : Set F) →
        ∀ y ∈ J, IsPGroup 2 (Subgroup.zpowers y) → 4 ≤ orderOf y → y * z = z * y →
          y ∈ Subgroup.normalizer (K : Set F)

end Statements

section Reduction

variable {F : Type*} [Group F] [Finite F]

omit [Finite F] in
theorem exists_pow_orderOf_eq_four {y : F} (hy2 : IsPGroup 2 (Subgroup.zpowers y))
    (hy4 : 4 ≤ orderOf y) : ∃ k : ℕ, orderOf (y ^ k) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hy2.exists_orderOf_eq_pow (⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y)
  rw [Subgroup.orderOf_mk] at hm
  have hm2 : 2 ≤ m := by
    by_contra h
    have : m ≤ 1 := by omega
    have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  refine ⟨2 ^ (m - 2), ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) ?_, hm]
  · have : 2 ^ m = 2 ^ (m - 2) * 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    rw [this]
    exact Nat.mul_div_cancel_left 4 (by positivity)
  · rw [hm]
    exact pow_dvd_pow 2 (by omega)

theorem step_one {J : Subgroup F} {t z y : F} (hJ : IsClassical2A7 ⊤ J t) (hyJ : y ∈ J)
    (hy2 : IsPGroup 2 (Subgroup.zpowers y)) (hy4 : 4 ≤ orderOf y) (hyz : y * z = z * y) :
    z ∈ Subgroup.normalizer (J : Set F) ∧ ∃ a ∈ J, orderOf a = 4 ∧ a * z = z * a := by
  obtain ⟨k₀, hk₀⟩ := exists_pow_orderOf_eq_four hy2 hy4
  set a : F := y ^ k₀ with ha
  have haJ : a ∈ J := J.pow_mem hyJ k₀
  have haz : a * z = z * a := (Commute.pow_left (show Commute y z from hyz) k₀).eq
  have hat : a ^ 2 = t := by
    have h2 : orderOf (a ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hk₀]; norm_num), hk₀]
    exact hJ.eq_of_orderOf_eq_two (J.pow_mem haJ 2) h2
  have hzt : z * t = t * z := by
    rw [← hat]
    exact (Commute.pow_right (show Commute z a from haz.symm) 2).eq
  have hy3 : 3 ≤ Nat.card (Subgroup.zpowers y) := by
    rw [Nat.card_zpowers]
    omega
  exact ⟨mem_normalizer_of_commute_of_mem_noncentral hJ hzt hyJ hy2 hy3 hyz.symm,
    a, haJ, hk₀, haz⟩

theorem prop366i_of_steps (h369 : Prop369iii) (h37 : Prop37x) : Prop366i := by
  intro F _ _ _ hnab J K t z hJ hK y hyJ hy2 hy4 hyz
  obtain ⟨hzJ, a, haJ, ha4, haz⟩ := step_one hJ hyJ hy2 hy4 hyz
  by_cases ht : t ∈ Subgroup.normalizer (K : Set F)
  · exact h37 F hnab J K t z hJ hK hzJ ht y hyJ hy2 hy4 hyz
  · exact absurd haz (h369 F hnab J K t z hJ hK hzJ ht a haJ ha4)


section Transport

variable {F : Type*} [Group F] [Finite F]

theorem conj_two_element {K : Subgroup F} {z k : F} (hK : IsClassical2A7 ⊤ K z) (hkK : k ∈ K)
    (hk2 : IsPGroup 2 (Subgroup.zpowers k)) (hkz : k ∉ Subgroup.zpowers z) (g : F) :
    IsClassical2A7 ⊤ (K.map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) ∧
      g * k * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom ∧
      IsPGroup 2 (Subgroup.zpowers (g * k * g⁻¹)) ∧ 4 ≤ orderOf (g * k * g⁻¹) := by
  have hJc : IsClassical2A7 ⊤ (K.map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) := by
    have h1 := hK.conj g
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1
  have hyJ : g * k * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨k, hkK, rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hk2.exists_orderOf_eq_pow (⟨k, Subgroup.mem_zpowers k⟩ : Subgroup.zpowers k)
  rw [Subgroup.orderOf_mk] at hm
  have hy2 : IsPGroup 2 (Subgroup.zpowers (g * k * g⁻¹)) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k ^ (2 ^ n) = 1 := ⟨m, by rw [← hm]; exact pow_orderOf_eq_one k⟩
    intro x
    obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨n, ?_⟩
    apply Subtype.ext
    show (x : F) ^ (2 ^ n) = 1
    rw [← hr, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have : (g * k * g⁻¹) ^ (2 ^ n) = 1 := by
      rw [conj_pow, hn]
      group
    rw [this, one_zpow]
  have hy4 : 4 ≤ orderOf (g * k * g⁻¹) := by
    rw [orderOf_conj_eq, hm]
    by_contra hlt
    have hm1 : m ≤ 1 := by
      by_contra hm2
      have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases m
    · rw [pow_zero, orderOf_eq_one_iff] at hm
      exact hkz (hm ▸ Subgroup.one_mem _)
    · rw [pow_one] at hm
      exact hkz (hK.eq_of_orderOf_eq_two hkK hm ▸ Subgroup.mem_zpowers z)
  exact ⟨hJc, hyJ, hy2, hy4⟩

theorem a7Omega5_of_prop366i (h : Prop366i) : A7Omega5 := by
  intro F _ _ _ hnab K z hK k hkK hk2 hkz g hg
  obtain ⟨hJc, hyJ, hy2, hy4⟩ := conj_two_element hK hkK hk2 hkz g
  have hyz : g * k * g⁻¹ * z = z * (g * k * g⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hg z rfl).symm
  exact h F hnab _ K _ z hJc hK _ hyJ hy2 hy4 hyz

end Transport

end Reduction

end CFSG.ClassicalInvolution.Hat2A7R
