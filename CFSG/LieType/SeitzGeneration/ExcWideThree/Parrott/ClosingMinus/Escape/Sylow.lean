module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape

variable {G : Type*} [Group G]

theorem commute_of_conj_eq_inv {g x : G} {m : ℕ} (hg : g ^ (3 ^ m) = 1)
    (hgx : g * x * g⁻¹ = x⁻¹) : g * x = x * g := by
  have h2 : Commute (g ^ 2) x := by
    have e : g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by rw [sq]; group
    have e2 : g ^ 2 * x * (g ^ 2)⁻¹ = x := by
      rw [e, hgx]
      have e3 : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e3, hgx, inv_inv]
    exact (mul_inv_eq_iff_eq_mul.1 e2)
  have hk : (g ^ 2) ^ ((3 ^ m + 1) / 2) = g := by
    have hodd : (3 ^ m + 1) % 2 = 0 := by
      have : 3 ^ m % 2 = 1 := Nat.pow_mod 3 m 2 ▸ by norm_num
      omega
    rw [← pow_mul, show 2 * ((3 ^ m + 1) / 2) = 3 ^ m + 1 by omega, pow_succ, hg, one_mul]
  have := (h2.pow_left ((3 ^ m + 1) / 2)).eq
  rwa [hk] at this

theorem exists_pow_prime_pow_eq_one {p : ℕ} {P : Subgroup G} (hP : IsPGroup p P) {g : G}
    (hg : g ∈ P) : ∃ m : ℕ, g ^ (p ^ m) = 1 := by
  obtain ⟨m, hm⟩ := hP ⟨g, hg⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem isPGroup_zpowers_of_pow_three {x : G} (hx3 : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  rintro ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]

theorem zpowers_cases_of_pow_three {x y : G} (hx3 : x ^ 3 = 1) (hy : y ∈ Subgroup.zpowers x) :
    y = 1 ∨ y = x ∨ y = x⁻¹ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hx3' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  have hmod : x ^ n = x ^ (n % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
    rw [zpow_add, zpow_mul, hx3', one_zpow, mul_one]
  rw [hmod]
  have h0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have h1 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero x)
  · exact Or.inr (Or.inl (zpow_one x))
  · right; right
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, hx3']

theorem exists_conj_comm_or_fusion [Finite G] {x s : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hs3 : s ^ 3 = 1) :
    (∃ g : G, (g * s * g⁻¹) * x = x * (g * s * g⁻¹)) ∨
      ∃ g : G, (g * x * g⁻¹) * x = x * (g * x * g⁻¹) ∧ g * x * g⁻¹ ∉ Subgroup.zpowers x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hxP⟩ := (isPGroup_zpowers_of_pow_three hx3).exists_le_sylow
  have hxP' : x ∈ (P : Subgroup G) := hxP (Subgroup.mem_zpowers x)
  by_cases hc : ∀ p ∈ (P : Subgroup G), p * x = x * p
  · left
    obtain ⟨Q, hsQ⟩ := (isPGroup_zpowers_of_pow_three hs3).exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
    have hsQ' : s ∈ (Q : Subgroup G) := hsQ (Subgroup.mem_zpowers s)
    have hmem : g * s * g⁻¹ ∈ (P : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact ⟨s, hsQ', by simp [MulAut.conj_apply]⟩
    exact ⟨g, hc _ hmem⟩
  · right
    push Not at hc
    obtain ⟨p₀, hp₀P, hp₀x⟩ := hc
    set C : Subgroup G := (P : Subgroup G) ⊓ Subgroup.centralizer {x} with hCdef
    set C' : Subgroup (P : Subgroup G) := C.subgroupOf (P : Subgroup G) with hC'def
    have hxC : x ∈ C := ⟨hxP', Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    have hlt : C' < ⊤ := by
      refine lt_top_iff_ne_top.2 fun h => hp₀x ?_
      have hmem : (⟨p₀, hp₀P⟩ : (P : Subgroup G)) ∈ C' := h ▸ Subgroup.mem_top _
      have h2 : p₀ ∈ C := hmem
      exact (Subgroup.mem_centralizer_singleton_iff.1 h2.2)
    have : Finite (P : Subgroup G) := inferInstance
    have hnil : Group.IsNilpotent (P : Subgroup G) := P.isPGroup'.isNilpotent
    obtain ⟨g', hg'N, hg'C⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent C' hlt)
    set g : G := (g' : G) with hgdef
    have hgP : g ∈ (P : Subgroup G) := g'.2
    have hxC' : (⟨x, hxP'⟩ : (P : Subgroup G)) ∈ C' := hxC
    have hgx : g * x * g⁻¹ ∈ C := by
      have := (Subgroup.mem_normalizer_iff.1 hg'N _).1 hxC'
      exact this
    have hcomm : (g * x * g⁻¹) * x = x * (g * x * g⁻¹) :=
      (Subgroup.mem_centralizer_singleton_iff.1 hgx.2)
    have hgnot : g * x ≠ x * g := by
      intro h
      apply hg'C
      show g ∈ C
      exact ⟨hgP, Subgroup.mem_centralizer_singleton_iff.2 h⟩
    refine ⟨g, hcomm, fun hz => ?_⟩
    rcases zpowers_cases_of_pow_three hx3 hz with h | h | h
    · apply hx1
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, h]; group
    · apply hgnot
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h]
    · obtain ⟨m, hm⟩ := exists_pow_prime_pow_eq_one P.isPGroup' hgP
      exact hgnot (commute_of_conj_eq_inv hm h)

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape
